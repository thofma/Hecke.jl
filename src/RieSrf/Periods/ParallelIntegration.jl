################################################################################
#
#  RieSrf/Periods/ParallelIntegration.jl : chunked, parallel integration
#
#  The nodes of every subpath (the points -1, the abscissae, 1) are split into
#  chunks of `chunk_len` nodes. Each chunk starts from a freshly computed
#  fiber at its first point and continues it (adaptively or by bisection, see
#  AnalyticContinuation.jl) up to the first point of the next chunk, adding
#  up weight * differentials at the abscissae it owns. The chunks are
#  independent jobs, handed out to one worker per thread.
#
#  Afterwards every path is put together serially (_stitch_path!): at every
#  chunk boundary both neighbouring chunks have computed the fiber at the SAME
#  point, so the sheets are matched by ball overlap (which must be a
#  bijection). This gives the integral matrix and the permutation of the
#  sheets of the path.
#
#  Entry point: _integrate_paths_chunked!.
#
################################################################################

struct _ChunkResult
  fiber_start::Vector{AcbFieldElem}   # fresh fiber at the first point of the chunk (any order)
  fiber_end::Vector{AcbFieldElem}     # continued fiber at its last point, in the same order
  integrals::Matrix{AcbFieldElem}     # m x g, row i = sheet fiber_start[i]; weights applied,
                                      # the constant derivative of a line NOT yet applied
end

# permutation[i] = the index j with a[i] and b[j] overlapping; must be unique
# and a bijection.
function _match_fibers(a::Vector{AcbFieldElem}, b::Vector{AcbFieldElem})
  m = length(a)
  @req length(b) == m "Fibers have different sizes."
  permutation = Vector{Int}(undef, m)
  for i in 1:m
    hits = findall(y -> overlaps(a[i], y), b)
    if length(hits) != 1
      distance = minimum(Float64(abs(a[i] - y)) for y in b)
      radius_a = Float64(radius(real(a[i])))
      radius_b = maximum(Float64(radius(real(y))) for y in b)
      error("Could not match sheets at a chunk boundary: root $i overlaps $(length(hits)) roots " *
            "(distance to the nearest root $distance, radii $radius_a and at most $radius_b, " *
            "separation of the roots $(_min_separation_f64(b))). Try a larger chunk_len or higher precision.")
    end
    permutation[i] = hits[1]
  end
  allunique(permutation) || error("Sheet matching at a chunk boundary is not a bijection.")
  return permutation
end

_min_separation_f64(b) = length(b) < 2 ? Inf :
  minimum(Float64(abs(b[i] - b[j])) for i in eachindex(b) for j in i+1:length(b))

# The chunks of the N + 2 nodes u = [-1; abscissae; 1]: chunk (j_start, j_end)
# continues from u[j_start] to u[j_end] and owns the abscissae with node
# index j in [j_start, j_end) ∩ [2, N + 1].
function _chunk_bounds(N::Int, chunk_len::Int)
  starts = collect(1:chunk_len:N + 1)
  push!(starts, N + 2)
  return [(starts[c], starts[c + 1]) for c in 1:length(starts) - 1]
end

# One chunk (j_start, j_end) of a subpath, with the given scheme. values is
# a preallocated m x g buffer; low_workspace (or nothing) as in
# _continue_adaptive!.
function _integrate_chunk(subpath::CPath, scheme, j_start::Int, j_end::Int, CC::AcbField,
                          work_prec::Int, workspace::ContinuationWorkspace,
                          cache::DifferentialFactorCache, values::Matrix{AcbFieldElem},
                          low_workspace::Union{Nothing, ContinuationWorkspace} = nothing,
                          adaptive::Bool = true)
  abscissae = scheme.abscissae
  weights = scheme.weights
  N = length(abscissae)
  RR = parent(abscissae[1])
  node(j) = j == 1 ? -one(RR) : (j == N + 2 ? one(RR) : abscissae[j - 1])
  m, g = size(values)
  subpath_is_line = is_line(subpath)

  x = evaluate(subpath, node(j_start))
  fiber = _fresh_fiber!(workspace, x, work_prec)
  @req length(fiber) == m "Wrong number of roots at the start of a chunk."
  fiber_start = _copy_fiber(CC, fiber)          # fiber is updated in place
  integrals = [CC() for _ in 1:m, _ in 1:g]
  if low_workspace === nothing
    CC_low = CC
    low_fiber = fiber
  else
    CC_low = base_ring(low_workspace.Ky)
    low_fiber = [CC_low() for _ in 1:m]
    for i in 1:m
      Nemo._acb_set(low_fiber[i], fiber[i], precision(CC_low))
    end
  end
  if adaptive
    state = AdaptiveContinuationState(CC_low, m)
    _adaptive_reset!(state, x)
  end

  for j in j_start:j_end
    if j > j_start
      x_next = evaluate(subpath, node(j))
      if adaptive
        _continue_adaptive!(state, workspace, low_workspace, x_next, fiber, low_fiber)
      else
        # every top-level target (abscissa or chunk end) gets full precision
        _continue_by_bisection!(workspace, low_workspace, x, x_next, fiber, low_fiber)
      end
      x = x_next
    end
    if 2 <= j <= N + 1 && j < j_end            # an abscissa owned by this chunk
      i = j - 1
      weight = subpath_is_line ? CC(weights[i]) : weights[i] * evaluate_derivative(subpath, abscissae[i])
      _evaluate_differentials!(values, cache, x, fiber, weight)
      for t in eachindex(integrals)
        add!(integrals[t], integrals[t], values[t])
      end
    end
  end
  return _ChunkResult(fiber_start, fiber, integrals)
end

# Serial: put the chunks of one path together; sets the integral matrices
# (of the path and of its line subpaths) and the permutation of the path.
# quadrature_error: added to the radii of the integrals along the subpaths
# (the heuristic quadrature error), or nothing.
function _stitch_path!(path::CPath, pieces::Vector{Vector{_ChunkResult}}, CC::AcbField,
                       work_prec::Int, workspace::ContinuationWorkspace, s_m, scheme_of;
                       quadrature_error::Union{Nothing, ArbFieldElem} = nothing)
  m = workspace.m
  g = size(pieces[1][1].integrals, 2)
  x0 = start_point(path.subpaths[1])
  fiber = sort!(_fresh_fiber!(workspace, x0, work_prec), lt = sheet_ordering)
  integral_matrix = zero_matrix(CC, m, g)

  for (k, subpath) in enumerate(path.subpaths)
    sums = [CC() for _ in 1:m, _ in 1:g]
    for piece in pieces[k]
      permutation = _match_fibers(fiber, piece.fiber_start)
      for i in 1:m, t in 1:g
        add!(sums[i, t], sums[i, t], piece.integrals[permutation[i], t])
      end
      fiber = piece.fiber_end[permutation]
    end
    D = matrix(CC, sums)
    if is_line(subpath)
      D *= evaluate_derivative(subpath, scheme_of(subpath).abscissae[1])
    end
    if quadrature_error !== nothing
      for i in 1:m, t in 1:g
        z = D[i, t]
        _add_error!(z, quadrature_error)
        D[i, t] = z
      end
    end
    is_line(subpath) && set_integral_matrix!(subpath, D)
    integral_matrix += D
  end
  # permutation first: the integral matrix setter needs it for the reverse path
  set_permutation!(path, inv(s_m(sortperm(fiber, lt = sheet_ordering))))
  set_integral_matrix!(path, integral_matrix)
  return nothing
end

# Integrate the differentials along all paths (paths in `order` are handed
# out first, the expensive ones), see the header.
#   scheme_of(subpath): its integration scheme;
#   f_split, Ky: the defining polynomial at the working precision (_split_in_y);
#   differential_factors, factor_matrix, min_powers, power_ranges: see
#     DifferentialFactorCache;
#   low_data: nothing or (f_split, Ky) at the low precision of the
#     intermediate continuation steps.
function _integrate_paths_chunked!(paths::Vector{CPath}, order, scheme_of, CC::AcbField,
                                   work_prec::Int, f_split, Ky, differential_factors,
                                   factor_matrix, min_powers, power_ranges, s_m, m::Int, g::Int;
                                   chunk_len::Int = 16, low_data = nothing, adaptive::Bool = true,
                                   quadrature_error::Union{Nothing, ArbFieldElem} = nothing)
  bounds = [[_chunk_bounds(length(scheme_of(subpath).abscissae), chunk_len) for subpath in path.subpaths]
            for path in paths]
  pieces = [[Vector{_ChunkResult}(undef, length(b)) for b in bounds[i]] for i in eachindex(paths)]

  jobs = Tuple{Int, Int, Int}[]            # (path, subpath, chunk), expensive paths first
  for i in order, k in eachindex(paths[i].subpaths), c in eachindex(bounds[i][k])
    push!(jobs, (i, k, c))
  end

  # One long-lived worker per thread; the workers pull the next job from a
  # shared counter (dynamic load balancing, no Task object per chunk).
  # Everything a worker writes must be `local`: a closure that assigns a name
  # that is also a local of the enclosing function shares that variable with
  # the other workers.
  next_job = Threads.Atomic{Int}(1)
  workers = map(1:Threads.nthreads()) do _
    Threads.@spawn begin
      local workspace = ContinuationWorkspace(f_split, Ky)
      local cache = DifferentialFactorCache(differential_factors, factor_matrix, min_powers, power_ranges)
      local values = [CC() for _ in 1:m, _ in 1:g]
      local low_workspace = low_data === nothing ? nothing : ContinuationWorkspace(low_data[1], low_data[2])
      while true
        local n = Threads.atomic_add!(next_job, 1)   # returns the old value
        n > length(jobs) && break
        local i, k, c = jobs[n]
        local subpath = paths[i].subpaths[k]
        local j_start, j_end = bounds[i][k][c]
        pieces[i][k][c] = _integrate_chunk(subpath, scheme_of(subpath), j_start, j_end, CC, work_prec,
                                           workspace, cache, values, low_workspace, adaptive)
      end
    end
  end
  foreach(wait, workers)

  stitch_workspace = ContinuationWorkspace(f_split, Ky)
  for i in eachindex(paths)
    _stitch_path!(paths[i], pieces[i], CC, work_prec, stitch_workspace, s_m, scheme_of;
                  quadrature_error = quadrature_error)
  end
  return nothing
end
