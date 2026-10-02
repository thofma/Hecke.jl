################################################################################
#
#  RieSrf/Periods/PeriodMatrix.jl : the period matrices (general algorithm)
#
#  The big period matrix of a plane model: the integrals of the basis of
#  differentials over a symplectic basis of the homology (Neurohr, Chapter 4;
#  the steps are listed at _compute_big_period_matrix), with the precision
#  management (target and working precision, precision retry) and the
#  optional check with a direct loop around infinity. The small period matrix
#  is computed from it.
#
#  Entry points: big_period_matrix, small_period_matrix.
#
################################################################################

@doc raw"""
    big_period_matrix(RS::RiemannSurfaceModel) -> AcbMatrix

The g x 2g big period matrix of the plane model: the integrals of the basis
of differentials over a symplectic basis of the homology.
"""
function big_period_matrix(RS::RiemannSurfaceModel)
  isdefined(RS, :big_period_matrix) && return RS.big_period_matrix
  # A failed computation leaves the paths etc. half-modified, and the
  # parameters cannot be changed anymore: do not retry on the same object.
  if isdefined(RS, :computation_failure)
    error("The period matrix computation for this Riemann surface failed earlier " *
          "($(sprint(showerror, RS.computation_failure))). Use " *
          "with_integration_parameters(RS; ...) to try again on a new surface.")
  end
  try
    return _big_period_matrix(RS)
  catch e
    RS.computation_failure = e
    rethrow()
  end
end

# T = prec + guard + ceil(log2 K) (at least the minimum set by a retry),
# W = T + guard, but not below the initial W (see _quadrature_guard_bits).
function _set_target_precision!(RS::RiemannSurfaceModel, K::Int; extra::Int = 0)
  prec = precision(RS)
  T = prec + _quadrature_guard_bits() + _genus_guard_bits(genus(RS)) + ceil(Int, log2(max(K, 1)))
  T = max(T, RS.min_target_precision)
  RS.target_precision = T
  RS.computational_precision = max(T, _initial_target_precision(prec)) + _rounding_guard_bits() + extra
  RS.computational_error = ArbField(RS.computational_precision)(2)^(-T)
  return RS
end

# -log2 of the largest radius of the real and imaginary parts of the entries
# of M (Inf if all entries are exact).
function _claimed_bits(M::AcbMatrix)
  RR = ArbField(64)
  r = zero(RR)
  for i in 1:nrows(M), j in 1:ncols(M)
    r = max(r, RR(radius(real(M[i, j]))), RR(radius(imag(M[i, j]))))
  end
  iszero(r) && return Inf
  return -_arb_mid_f64(log(r) / log(RR(2)))
end

# Bits missing to the requested precision, for the matrices selected by
# the parameter accuracy (:small = tau, :big = the big period matrix P).
# (Also used for the superelliptic model.)
function _precision_deficit(acc::Symbol, prec::Int, g::Int, P::AcbMatrix)
  d = -Inf
  if acc === :big || acc === :both
    d = max(d, prec - _claimed_bits(P))
  end
  if acc === :small || acc === :both
    d = max(d, prec - _claimed_bits(_solve_precond(P[1:g, 1:g], P[1:g, g+1:2*g])))
  end
  return d
end

function _big_period_matrix(RS::RiemannSurfaceModel)
  isdefined(RS, :big_period_matrix) && return RS.big_period_matrix
  P = _compute_big_period_matrix(RS)
  if RS.resolved_parameters.precision_retry
    deficit = _precision_deficit(RS.resolved_parameters.accuracy, precision(RS), genus(RS), P)
    if deficit > 0
      old_target = RS.target_precision
      RS.precision_retries += 1
      RS.min_target_precision = old_target + ceil(Int, deficit) + _retry_extra_bits()
      @debug "Precision retry ($(RS.resolved_parameters.accuracy)): short of $(round(deficit, digits = 1)) bits, target $(old_target) -> $(RS.min_target_precision)"
      # Redo the integration from the splitting of the paths on; the
      # fundamental group, the chains and the homology basis are kept.
      # (subpaths far from all discriminant points have no closest point and
      #  keep the fixed bound 1 set with their parameters)
      RS.bounds = ArbFieldElem[]
      all_paths = vcat(fundamental_group_of_punctured_P1(RS)[1],
                       isdefined(RS, :direct_inf_paths) ? RS.direct_inf_paths : CPath[])
      for path in all_paths, subpath in unique(vcat([path], subpaths(path)))
        isdefined(subpath, :closest_disc_point_parameter) && empty!(subpath.bounds)
      end
      P = _compute_big_period_matrix(RS; resplit = false)
    end
  end
  RS.big_period_matrix = P
  return P
end

# A direct loop around infinity: a line from the base point x0 to a point p on
# a big circle, and the circle. The circle has center c (center of the
# bounding box of the discriminant points) and radius R >= twice their largest
# distance from c, so it stays at distance >= R/2 from all of them; x0 lies
# well inside. The base point need not lie to the left of the discriminant
# points (e.g. the midpoint of an edge), so the direction of the line is
# chosen among 64 directions to keep it as far as possible (relative to its
# length) from all discriminant points.
function _direct_inf_paths(RS::RiemannSurfaceModel)
  isdefined(RS, :direct_inf_paths) && return RS.direct_inf_paths
  disc_points = internal_discriminant_points(RS)
  CC = parent(disc_points[1])
  x0 = CC(RS.base_point.coordx)
  # the geometry in Float64 suffices
  z = [ComplexF64(Float64(real(q)), Float64(imag(q))) for q in disc_points]
  w0 = ComplexF64(Float64(real(x0)), Float64(imag(x0)))
  c64 = complex((minimum(real, z) + maximum(real, z))/2, (minimum(imag, z) + maximum(imag, z))/2)
  R64 = max(2*maximum(abs(w - c64) for w in z), 2*abs(w0 - c64), 1.0)
  best, pbest = -Inf, c64 - R64
  for k in 0:63
    u = cis(2*pi*k/64)
    # exit point of the ray x0 + s u (s > 0) from the circle |x - c| = R
    b = real(conj(u)*(w0 - c64))
    s = -b + sqrt(b^2 - abs2(w0 - c64) + R64^2)
    q = w0 + s*u
    # clearance: min distance of the discriminant points to the segment, relative to its length
    cl = minimum(abs(w - (w0 + clamp(real(conj(u)*(w - w0)), 0.0, s)*u)) for w in z) / s
    if cl > best
      best, pbest = cl, q
    end
  end
  c = CC(real(c64), imag(c64))
  p = CC(real(pbest), imag(pbest))
  RS.direct_inf_paths = [line_path(x0, p, CC), circle_path(p, c, CC)]
  return RS.direct_inf_paths
end

_max_radius_64(M::AcbMatrix) = maximum(max(ArbField(64)(radius(real(M[i, j]))), ArbField(64)(radius(imag(M[i, j]))))
                                       for i in 1:nrows(M), j in 1:ncols(M))

# Compare the loop around infinity composed of the other loops with the direct
# one (either orientation, same permutation). If they overlap, keep the one
# with the smaller radius; otherwise warn.
function _check_direct_inf_chain!(RS::RiemannSurfaceModel)
  line, circle = RS.direct_inf_paths
  inf_chain = RS.inf_chain
  M = inf_chain.integral_matrix
  for c in (circle, reverse(circle))
    direct_chain = CChain([line, c, reverse(line)])
    direct_chain.permutation == inf_chain.permutation || continue
    N = direct_chain.integral_matrix
    all(overlaps(N[i, j], M[i, j]) for i in 1:nrows(M), j in 1:ncols(M)) || continue
    RS.infinity_check = 1
    _max_radius_64(N) < _max_radius_64(M) && (inf_chain.integral_matrix = N)
    return RS
  end
  RS.infinity_check = -1
  @warn "The integrals along a loop around infinity computed directly and as a composition of the other loops do not agree. The period matrix is probably wrong." maxlog = 1
  return RS
end

# The big period matrix of the general algorithm (Neurohr, Chapter 4):
#  1. the quadrature type and parameter of every subpath,
#  2. the target and working precision (from the number of subpaths),
#  3. integrand bounds and integration schemes,
#  4. the integrals along all paths (with the monodromy as a by-product),
#  5. the chains around the discriminant points and around infinity,
#  6. the integrals over the cycles of homology_basis, transformed to a
#     symplectic basis.
# resplit = false (precision retry): keep the subpaths and their quadrature
# type from the first pass, only the bounds, schemes and integrals are redone.
function _compute_big_period_matrix(RS::RiemannSurfaceModel; resplit::Bool = true)
  _ensure_differentials!(RS)
  params = _resolve_integration_parameters!(RS)   # fixed from here on
  g = genus(RS)
  paths, pi1_gens = fundamental_group_of_punctured_P1(RS)
  # the paths of the direct loop around infinity are integrated with the
  # others (appended: the indices in pi1_gens stay valid)
  params.direct_infinity && (paths = vcat(paths, _direct_inf_paths(RS)))
  disc_points = internal_discriminant_points(RS)
  differentials = differential_form_data(RS)[1]
  v = embedding(RS)

  # 1. Quadrature type and parameter of every subpath.
  gl_parameters, de_parameters = _quadrature_parameters!(RS, paths, disc_points, params.int_style, resplit)

  # 2. Target and working precision from the number of subpaths.
  number_of_subpaths = sum(length(subpaths(path)) for path in paths)
  _set_target_precision!(RS, number_of_subpaths)
  work_prec = RS.computational_precision
  embedded_differentials = [_embed_mpoly(omega, v, work_prec) for omega in differentials]

  # 3. Group the parameters (one scheme per group), bound the integrands.
  gl_group_rs = isempty(gl_parameters) ? ArbFieldElem[] :
                _gl_group_rs(sort!(gl_parameters), RS.computational_error; c = params.group_cost)
  de_group_rs = isempty(de_parameters) ? ArbFieldElem[] : _de_group_rs(sort!(de_parameters))
  differential_basis = params.integration_method === :rigorous ?
                       [omega.f for omega in basis_of_differentials(RS)] : nothing
  all_subpaths = [subpath for path in paths for subpath in subpaths(path)]
  f = _embed_mpoly(defining_polynomial(RS), v, work_prec)    # shared by the bounds
  Threads.@threads :dynamic for subpath in all_subpaths
    if subpath.integration_scheme === :gl
      if is_line(subpath) && params.integration_method === :rigorous
        _ellipse_bound_rigorous!(subpath, differential_basis, gl_group_rs, RS)
      else
        _ellipse_bound_heuristic!(subpath, embedded_differentials, gl_group_rs, RS; f = f)
      end
    else
      _burger_bound_heuristic!(subpath, embedded_differentials, de_group_rs, RS; f = f)
    end
  end
  gl_bounds = ArbFieldElem[]
  de_bounds = ArbFieldElem[]
  for subpath in all_subpaths
    append!(subpath.integration_scheme === :gl ? gl_bounds : de_bounds, subpath.bounds)
  end

  # accuracy = :big/:both: the big period matrix is wanted to an absolute
  # 2^-prec, but its entries are about as large as the integrands (up to
  # 2^70 for curves with coefficients of very different sizes), and the
  # rounding errors are relative. Raise the working precision by log2 of the
  # (heuristic) integrand bound, to avoid a precision retry.
  if params.accuracy !== :small
    all_bounds = vcat(gl_bounds, de_bounds, RS.bounds)
    extra = isempty(all_bounds) ? 0 : _magnitude_guard_bits(maximum(all_bounds))
    if extra > 0
      _set_target_precision!(RS, number_of_subpaths; extra = extra)
      work_prec = RS.computational_precision
      embedded_differentials = [_embed_mpoly(omega, v, work_prec) for omega in differentials]
      f = _embed_mpoly(defining_polynomial(RS), v, work_prec)
    end
  end

  # The number of nodes N depends on r and the bound M: r has a strong
  # influence, M only a logarithmic one. One bound for all schemes on
  # purpose: the heuristic bound of a single subpath can be too small, the
  # maximum over all subpaths has been safe. (The DE schemes use the maximum
  # of the GL and DE bounds.)
  if !isempty(gl_parameters)
    push!(RS.bounds, maximum(gl_bounds))
    bound = maximum(RS.bounds)
    RS.integration_schemes_GL = [IntegrationSchemeGL(r, work_prec, RS.computational_error, bound)
                                 for r in gl_group_rs]
  end
  if !isempty(de_parameters)
    push!(RS.bounds, maximum(de_bounds))
    bound = maximum(RS.bounds)
    RS.integration_schemes_DE = [IntegrationSchemeDE(r, work_prec, [bound, bound], RS.target_precision)
                                 for r in de_group_rs]
  end

  # 4. The integrals along the paths (and their permutations).
  CC = base_ring(f)
  m = degree(f, 2)
  Ky, _ = polynomial_ring(CC, "y")
  s_m = SymmetricGroup(m)
  _, factor_matrix, min_powers, power_ranges = differential_form_data(RS)
  scheme_of(subpath) = subpath.integration_scheme === :gl ?
                       RS.integration_schemes_GL[subpath.integration_scheme_index] :
                       RS.integration_schemes_DE[subpath.integration_scheme_index]
  cost(path) = sum(length(scheme_of(subpath).abscissae) for subpath in path.subpaths)
  order = sortperm(paths, by = cost, rev = true)
  _integrate_paths_chunked!(paths, order, scheme_of, CC, work_prec, _split_in_y(f), Ky,
                            embedded_differentials, factor_matrix, min_powers, power_ranges, s_m, m, g;
                            chunk_len = params.chunk_len,
                            low_data = _midpoint_data(RS, params, disc_points, work_prec),
                            adaptive = params.adaptive, quadrature_error = RS.computational_error)

  # 5. The chains. If the monodromy was computed before without periods
  # (_ensure_monodromy!), the chains are kept and only get their integrals.
  if isdefined(RS, :pi1_chains)
    _refresh_chains!(RS)
  else
    _build_chains!(RS, paths, pi1_gens, s_m)
  end
  params.direct_infinity && _check_direct_inf_chain!(RS)
  closed_chains = vcat(RS.closed_chains, [RS.inf_chain])

  # 6. The periods: the integrals over the 2g + m - 1 cycles, transformed with
  # the symplectic reduction S: the first 2g rows are the periods over a
  # symplectic basis, the other m - 1 rows must vanish (a sanity check).
  cycles, _, symplectic_transform = homology_basis(RS)
  cycle_integrals, RS.sheet_to_sheet_integrals = _cycle_integrals(cycles, closed_chains, CC, m, g)
  periods = symplectic_transform * matrix(cycle_integrals)
  dependent_rows = periods[2g+1:end, :]
  @req all([contains(z, zero(CC)) for z in dependent_rows]) "Sanity check failed. There may have been an error in the period matrix computation."
  return transpose(periods[1:2*g, :])
end

# Step 1 of _compute_big_period_matrix: the quadrature type (:gl or :de) and
# the parameter of every subpath. int_style :gl splits the lines
# (_gauss_legendre_path_parameters!); :mixed in addition switches the subpaths
# with r < 1.03 to double exponential; :de uses double exponential on the
# unsplit paths. With resplit = false (precision retry) the subpaths and their
# types are kept. Returns the parameters of the GL and of the DE subpaths.
function _quadrature_parameters!(RS::RiemannSurfaceModel, paths::Vector{CPath},
                                 disc_points::Vector{AcbFieldElem}, int_style::Symbol, resplit::Bool)
  if resplit
    if int_style === :de
      for path in paths
        _double_exponential_path_parameters!(disc_points, path)
        path.integration_scheme = :de
      end
    else
      Threads.@threads :dynamic for path in paths
        _gauss_legendre_path_parameters!(disc_points, path, RS.computational_error)
      end
      for path in paths, subpath in subpaths(path)
        if int_style === :mixed && subpath.quadrature_parameter < 1.03
          _double_exponential_path_parameters!(disc_points, subpath)
          @req subpath.quadrature_parameter < 1.03 "The double exponential parameter of a subpath is not below 1.03."
          subpath.integration_scheme = :de
        else
          subpath.integration_scheme = :gl
        end
      end
    end
  end
  gl_parameters = ArbFieldElem[]
  de_parameters = ArbFieldElem[]
  for path in paths, subpath in subpaths(path)
    push!(subpath.integration_scheme === :gl ? gl_parameters : de_parameters, subpath.quadrature_parameter)
  end
  return gl_parameters, de_parameters
end

# The data for the low-precision intermediate continuation steps
# (midpoint_precision), or nothing: off when midpoint_precision == 0 or when
# it would not be lower than the working precision. The low precision must
# resolve the geometry: if discriminant points lie closer together than
# ~2^(30 - low_prec) (relative), steps near them cannot even be represented
# at low_prec. Then the midpoint precision is switched off (recorded in the
# resolved parameters).
function _midpoint_data(RS::RiemannSurfaceModel, params::IntegrationParameters,
                        disc_points::Vector{AcbFieldElem}, work_prec::Int)
  params.midpoint_precision > 0 || return nothing
  low_prec = max(100, min(params.midpoint_precision, work_prec))
  low_prec < work_prec || return nothing
  if !_resolvable_at(disc_points, low_prec - 30)
    @info "Midpoint precision $(params.midpoint_precision) is too low for the distances between the discriminant points of this curve; it is switched off."
    params.midpoint_precision = 0
    return nothing
  end
  return _continuation_data(RS, low_prec)
end

# Step 6: the integrals over the cycles (rows), and for every sheet j >= 2
# the integral along the first part of a cycle that reaches sheet j from
# sheet 1 (sheet_to_sheet_integrals, used by the Abel-Jacobi map). A cycle
# [s_1, c_1, s_2, c_2, ..., s_k] (see homology_basis) follows the closed
# chain c_i from sheet s_i, as many times as needed to reach sheet s_{i+1}.
function _cycle_integrals(cycles::Vector{Vector{Int}}, closed_chains::Vector{CChain},
                          CC::AcbField, m::Int, g::Int)
  sheet_to_sheet_integrals = zero_matrix(CC, m, g)
  sheets_left = Set(2:m)
  sheets_to_record = Set{Int}()
  cycle_integrals = Vector{AcbFieldElem}[]
  for cycle in cycles
    if !isempty(sheets_left)
      # the intermediate sheets of this cycle not seen before
      sheets_to_record = intersect(sheets_left, Set(cycle[3:2:end-2]))
      setdiff!(sheets_left, sheets_to_record)
    end
    cycle_integral = [zero(CC) for _ in 1:g]
    l = 1
    while l < length(cycle)
      sheet = cycle[l]
      chain = closed_chains[cycle[l+1]]
      while sheet != cycle[l+2]
        cycle_integral += chain.integral_matrix[sheet, :]
        sheet = permutation(chain)[sheet]
        if sheet in sheets_to_record
          sheet_to_sheet_integrals[sheet, :] = cycle_integral
          delete!(sheets_to_record, sheet)
        end
      end
      l += 2
    end
    push!(cycle_integrals, cycle_integral)
  end
  return cycle_integrals, sheet_to_sheet_integrals
end

@doc raw"""
    small_period_matrix(RS::AbstractRiemannSurfaceModel) -> AcbMatrix

The small period matrix tau = P1^-1 P2 for the big period matrix (P1 | P2).
"""
function small_period_matrix(RS::AbstractRiemannSurfaceModel)
  if isdefined(RS, :small_period_matrix)
    return RS.small_period_matrix
  end
  g = genus(RS)
  P = big_period_matrix(RS)
  P1 = P[1:g, 1:g]
  P2 = P[1:g, g+1:2*g]
  P1_inv = _inv_precond(P1)
  small_period_matrix = _solve_precond(P1, P2)   # better than P1_inv * P2
  RS.small_period_matrix = small_period_matrix
  RS.complex_reduction_matrices = [P1_inv]
  return small_period_matrix
end

# The matrices for the reduction of Abel-Jacobi values modulo the period
# lattice (see AbelJacobiMap.jl), cached in RS:
#   :real     the inverse of the 2g x 2g real matrix of the periods,
#   :complex  P1^-1 (set by small_period_matrix) and Im(tau)^-1.
function _compute_reduction_matrix!(RS::AbstractRiemannSurfaceModel, reduction::Symbol)
  g = genus(RS)
  if reduction === :real
    isdefined(RS, :real_reduction_matrix) && return RS
    P = big_period_matrix(RS)
    M = zero_matrix(ArbField(precision(base_ring(P))), 2*g, 2*g)
    for j in 1:g, k in 1:g
      M[j, k] = real(P[j, k])
      M[j+g, k] = imag(P[j, k])
      M[j, k+g] = real(P[j, k+g])
      M[j+g, k+g] = imag(P[j, k+g])
    end
    RS.real_reduction_matrix = _inv_precond(M)
  elseif reduction === :complex
    tau = small_period_matrix(RS)
    if length(RS.complex_reduction_matrices) == 1
      push!(RS.complex_reduction_matrices, change_base_ring(base_ring(tau), _inv_precond(imag(tau))))
    end
  else
    error("Unknown reduction $reduction.")
  end
  return RS
end

# true iff all pairwise distances of the points are at least 2^(-bits) relative
# to their size, i.e. |a - b| >= 2^(-bits) * max(1, |a|, |b|).
function _resolvable_at(points::Vector{AcbFieldElem}, bits::Int)
  n = length(points)
  for i in 1:n, j in i+1:n
    a, b = points[i], points[j]
    scale = max(1.0, _arb_mid_f64(abs(a)), _arb_mid_f64(abs(b)))
    d = abs(a - b)
    # compare with an upper bound for |a - b|
    _arb_mid_f64(d) + _arb_mid_f64(radius(d)) < ldexp(scale, -bits) && return false
  end
  return true
end
