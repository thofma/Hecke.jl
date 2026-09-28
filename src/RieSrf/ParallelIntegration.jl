################################################################################
#
#  Chunked, parallel integration along the paths.
#
#  Every subpath's abscissae are split into chunks of `chunk_len` abscissae.
#  Each chunk starts from freshly computed roots at its first point and is
#  continued (continue_adaptive!, or recursive bisection if adaptive = false)
#  up to the first point of the next chunk. The chunks are independent jobs,
#  handed out to one worker per thread.
#
#  Afterwards, each path is stitched together serially: at every chunk
#  boundary both neighbouring chunks have computed the fiber at the SAME point,
#  so the sheets are matched by ball overlap (which must be a bijection).
#
################################################################################

struct _ChunkResult
  ys_start::Vector{AcbFieldElem}   # fresh roots at the chunk's first point (any order)
  ys_end::Vector{AcbFieldElem}     # continued roots at the chunk's last point, same order
  M::Matrix{AcbFieldElem}          # m x g, row i = sheet ys_start[i]; weights applied,
                                   # the constant dx-factor of lines NOT yet applied
end

# perm[i] = index j with a[i] and b[j] overlapping; must be unique and a bijection.
function _match_fibers(a::Vector{AcbFieldElem}, b::Vector{AcbFieldElem})
  m = length(a)
  @req length(b) == m "Fibers have different sizes."
  perm = Vector{Int}(undef, m)
  for i in 1:m
    hits = findall(t -> overlaps(a[i], t), b)
    if length(hits) != 1
      d = minimum(Float64(abs(a[i] - t)) for t in b)
      ra = Float64(radius(real(a[i])))
      rb = maximum(Float64(radius(real(t))) for t in b)
      error("Could not match sheets at a chunk boundary: root $i overlaps $(length(hits)) roots " *
            "(distance to the nearest root $d, radii $ra and at most $rb, " *
            "separation of the roots $(_min_sep_f64(b))). Try a larger chunk_len or higher precision.")
    end
    perm[i] = hits[1]
  end
  allunique(perm) || error("Sheet matching at a chunk boundary is not a bijection.")
  return perm
end

_min_sep_f64(b) = length(b) < 2 ? Inf :
  minimum(Float64(abs(b[i] - b[j])) for i in eachindex(b) for j in i+1:length(b))

# Point indices into u = [-1; abscissae; 1] (length N + 2).
# Chunk (jlo, jhi) continues from u[jlo] to u[jhi] and owns the abscissae
# with point index j in [jlo, jhi) ∩ [2, N + 1].
function _chunk_bounds(N::Int, L::Int)
  b = collect(1:L:N + 1)
  push!(b, N + 2)
  return [(b[c], b[c + 1]) for c in 1:length(b) - 1]
end

function _integrate_chunk(subpath::CPath, scheme, jlo::Int, jhi::Int, CC::AcbField,
                          max_prec::Int, ws::ContinuationWorkspace,
                          cache::DifferentialFactorCache, vals::Matrix{AcbFieldElem},
                          lo::Union{Nothing, ContinuationWorkspace} = nothing,
                          adaptive::Bool = true)  
  abscissae = scheme.abscissae
  weights = scheme.weights
  N = length(abscissae)
  RR = parent(abscissae[1])
  u(j) = j == 1 ? -one(RR) : (j == N + 2 ? one(RR) : abscissae[j - 1])
  m, g = size(vals)
  is_line = path_type(subpath) == 0

  x = evaluate(subpath, u(jlo))
  z = _fresh_fiber!(ws, x, max_prec)
  @req length(z) == m "Wrong number of roots at the start of a chunk."
  ys_start = [CC() for _ in 1:m]              # own copies: z is updated in place
  for i in 1:m
    Hecke.set!(ys_start[i], z[i])
  end
  acc = [CC() for _ in 1:m, _ in 1:g]
    if lo !== nothing
    CL = base_ring(lo.Ky)
    zl = [CL() for _ in 1:m]
    for i in 1:m
      Nemo._acb_set(zl[i], z[i], precision(parent(zl[i])))
    end
  else                                                                            #new
    CL = CC                                                                       #new
    zl = z                                                                        #new
  end
  if adaptive                                                                     #new
    st = AdaptiveContinuationState(CL, m)                                         #new
    _adaptive_reset!(st, x, zl)                                                   #new
  end                                                                             #new

  for j in jlo:jhi
    if j > jlo
      xn = evaluate(subpath, u(j))
      if adaptive                                                                 #new
        continue_adaptive!(st, ws, lo, xn, z, zl)                                 #new
      elseif lo === nothing
        recursive_continuation_inplace!(ws, x, xn, z)
      else
        # every top-level target (abscissa or chunk end) gets full precision
        recursive_continuation_mixed!(lo, ws, x, xn, z, zl, true)
      end
      x = xn
    end
    if 2 <= j <= N + 1 && j < jhi            # abscissa owned by this chunk
      i = j - 1
      wi = is_line ? CC(weights[i]) : weights[i] * evaluate_d(subpath, abscissae[i])
      evaluate_differential_factors_matrix!(vals, cache, x, z, wi)
      for t in eachindex(acc)
        add!(acc[t], acc[t], vals[t])
      end
    end
  end
  return _ChunkResult(ys_start, z, acc)
end

# Serial: glue the chunks of one path together.
# qerr: the quadrature error (heuristic bound) added to the integrals along
# the subpaths, or nothing.
function _stitch_path!(path::CPath, pieces::Vector{Vector{_ChunkResult}}, CC::AcbField,
                       max_prec::Int, ws::ContinuationWorkspace, s_m, schemeof;
                       qerr::Union{Nothing, ArbFieldElem} = nothing)
  m = ws.m
  g = size(pieces[1][1].M, 2)
  x0 = start_point(path.sub_paths[1])
  ys = sort!(_fresh_fiber!(ws, x0, max_prec), lt = sheet_ordering)
  integral_matrix = zero_matrix(CC, m, g)

  for (k, subpath) in enumerate(path.sub_paths)
    acc = [CC() for _ in 1:m, _ in 1:g]
    for piece in pieces[k]
      perm = _match_fibers(ys, piece.ys_start)
      for i in 1:m, t in 1:g
        add!(acc[i, t], acc[i, t], piece.M[perm[i], t])
      end
      ys = piece.ys_end[perm]
    end
    D = matrix(CC, acc)
    if path_type(subpath) == 0
      D *= evaluate_d(subpath, schemeof(subpath).abscissae[1])
    end
    if qerr !== nothing
      for i in 1:m, t in 1:g
        z = D[i, t]
        ccall((:acb_add_error_arb, libflint), Nothing, (Ref{AcbFieldElem}, Ref{ArbFieldElem}), z, qerr)
        D[i, t] = z
      end
    end
    path_type(subpath) == 0 && assign_integral_matrix(subpath, D)
    integral_matrix += D
  end
  # permutation first: the integral-matrix setter may need it for the reverse path
  assign_permutation(path, inv(s_m(sortperm(ys, lt = sheet_ordering))))
  assign_integral_matrix(path, integral_matrix)
  return nothing
end

function _integrate_paths_chunked!(paths::Vector{CPath}, order, schemeof, Cp::AcbField,
                                   max_prec::Int, f_split, Ky, embedded_differentials,
                                   fm, mp, rp, s_m, m::Int, g::Int; chunk_len::Int = 16,
                                   lo_data = nothing, adaptive::Bool = true,   # nothing or (F_lo, Ky_lo)
                                   qerr::Union{Nothing, ArbFieldElem} = nothing)
  bounds = [[_chunk_bounds(length(schemeof(sp).abscissae), chunk_len) for sp in p.sub_paths]
            for p in paths]
  pieces = [[Vector{_ChunkResult}(undef, length(bs)) for bs in bounds[ip]] for ip in eachindex(paths)]

  jobs = Tuple{Int, Int, Int}[]            # (path, subpath, chunk); expensive paths first
  for ip in order, ik in eachindex(paths[ip].sub_paths), ic in eachindex(bounds[ip][ik])
    push!(jobs, (ip, ik, ic))
  end

  # One long-lived worker per thread; workers pull the next job from a shared
  # counter (dynamic load balancing, no per-chunk Task objects).
  next_job = Threads.Atomic{Int}(1)
  workers = map(1:Threads.nthreads()) do _
    Threads.@spawn begin
      wsb    = ContinuationWorkspace(f_split, Ky)
      cacheb = DifferentialFactorCache(embedded_differentials, fm, mp, rp)
      valsb  = [Cp() for _ in 1:m, _ in 1:g]
      lob    = lo_data === nothing ? nothing : ContinuationWorkspace(lo_data[1], lo_data[2])
      while true
        n = Threads.atomic_add!(next_job, 1)   # returns the old value
        n > length(jobs) && break
        ip, ik, ic = jobs[n]
        spb = paths[ip].sub_paths[ik]
        jlo, jhi = bounds[ip][ik][ic]
        pieces[ip][ik][ic] = _integrate_chunk(spb, schemeof(spb), jlo, jhi, Cp, max_prec,
                                              wsb, cacheb, valsb, lob, adaptive)
      end
    end
  end
  foreach(wait, workers)

  ws0 = ContinuationWorkspace(f_split, Ky)
  for ip in eachindex(paths)
    _stitch_path!(paths[ip], pieces[ip], Cp, max_prec, ws0, s_m, schemeof; qerr = qerr)
  end
  return nothing
end
