################################################################################
#
#          RieSrf/PeriodMatrix.jl : Computing the period matrix
#
# (C) 2025 Jeroen Hanselman
# This is a port of the Riemann surfaces package written by
# Christian Neurohr. It is based on his Phd thesis
# https://www.researchgate.net/publication/329100697_Efficient_integration_on_Riemann_surfaces_applications
# Neurohr's package can be found on https://github.com/christianneurohr/RiemannSurfaces
#
################################################################################

export big_period_matrix, small_period_matrix

#Computes a big period matrix for the Riemann surface.
@doc raw"""
 big_period_matrix(RS::RiemannSurfaceModel)

Compute the big period matrix for the Riemann surface.
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
      allp = vcat(fundamental_group_of_punctured_P1(RS)[1],
                  isdefined(RS, :direct_inf_paths) ? RS.direct_inf_paths : CPath[])
      for path in allp, sp in unique(vcat([path], get_subpaths(path)))
        isdefined(sp, :t_of_closest_d_point) && empty!(sp.bounds)
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
  D = internal_discriminant_points(RS)
  CC = parent(D[1])
  x0 = CC(RS.base_point.coordx)
  z = [ComplexF64(Float64(real(q)), Float64(imag(q))) for q in D]
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
  L = c_line(x0, p, CC)
  circ = c_circle(p, c, CC)
  RS.direct_inf_paths = [L, circ]
  return RS.direct_inf_paths
end

_max_radius_64(M::AcbMatrix) = maximum(max(ArbField(64)(radius(real(M[i, j]))), ArbField(64)(radius(imag(M[i, j]))))
                                       for i in 1:nrows(M), j in 1:ncols(M))

# Compare the loop around infinity composed of the other loops with the direct
# one (either orientation, same permutation). If they overlap, keep the one
# with the smaller radius; otherwise warn.
function _check_direct_inf_chain!(RS::RiemannSurfaceModel)
  L, circ = RS.direct_inf_paths
  S = RS.inf_chain
  M = S.integral_matrix
  for c in (circ, reverse(circ))
    D = CChain([L, c, reverse(L)])
    D.permutation == S.permutation || continue
    N = D.integral_matrix
    all(overlaps(N[i, j], M[i, j]) for i in 1:nrows(M), j in 1:ncols(M)) || continue
    RS.infinity_check = 1
    _max_radius_64(N) < _max_radius_64(M) && (S.integral_matrix = N)
    return RS
  end
  RS.infinity_check = -1
  @warn "The integrals along a loop around infinity computed directly and as a composition of the other loops do not agree. The period matrix is probably wrong." maxlog = 1
  return RS
end

# resplit = false (precision retry): keep the subpaths and their quadrature
# type from the first pass, only the bounds, schemes and integrals are redone.
function _compute_big_period_matrix(RS::RiemannSurfaceModel; resplit::Bool = true)
  _ensure_differentials!(RS)
  params = _resolve_integration_parameters!(RS)   # fixed from here on

  g = genus(RS)
  # the exact basis is only needed for the rigorous bounds (and in the
  # certified Baker case it is not computed at all)
  # (the cached value is a 2-tuple, so take the disc. points from the field;
  #  with lazy construction the fundamental group may already be cached here)
  paths, pi1_gens = fundamental_group_of_punctured_P1(RS)
  ordered_disc_points = RS.pi1_ordered_disc_points
  num_paths = length(paths)
  # the paths of the direct loop around infinity are integrated with the
  # others (appended: the indices of pi1_gens stay valid)
  params.direct_infinity && (paths = vcat(paths, _direct_inf_paths(RS)))
  prec = precision(RS)
  disc_points = internal_discriminant_points(RS)

  differentials = differential_form_data(RS)[1]

  v = embedding(RS)

  RR = ArbField(RS.computational_precision)
  dif_basis = params.integration_method == "rigorous" ? [omega.f for omega in basis_of_differentials(RS)] : nothing

  k = RR(103/100)

  double_exponential_int_pars = ArbFieldElem[]
  gauss_legendre_int_pars = ArbFieldElem[]

  #path`N seems to be less than what it is in Neurohr's implementation.
  #Neurohr takes disc_points of low precision here, but I don't see any 
  #real reason for us to do so as well. I expect higher precision to improve
  #stability.

  int_style = params.int_style

  if !resplit
    for path in paths, subpath in get_subpaths(path)
      push!(subpath.integration_scheme == "GL" ? gauss_legendre_int_pars : double_exponential_int_pars,
            subpath.int_param_r)
    end
  end

  if resplit && (int_style == "Mixed" || int_style == "GL")

    Threads.@threads :dynamic for path in paths
      gauss_legendre_path_parameters(disc_points, path, RS.computational_error)
    end
  end

  if resplit && int_style == "Mixed"
    for path in paths
      for subpath in path.sub_paths
        if subpath.int_param_r < k 
          double_exponential_path_parameters(disc_points, subpath)
          subpath.integration_scheme = "DE"
          @req subpath.int_param_r < k "Error in double exponential parameters"
          push!(double_exponential_int_pars, subpath.int_param_r)
        else
          subpath.integration_scheme = "GL"
          push!(gauss_legendre_int_pars, subpath.int_param_r)
        end
      end
    end
  end

  if resplit && int_style == "GL"
    for path in paths
      for subpath in path.sub_paths
        subpath.integration_scheme = "GL"
        push!(gauss_legendre_int_pars, subpath.int_param_r)
      end
    end
  end 

  if resplit && int_style == "DE"
    for path in paths
      double_exponential_path_parameters(disc_points, path)
      path.integration_scheme = "DE"
      push!(double_exponential_int_pars, path.int_param_r)
    end
  end 

  # target and working precision from the number of subpaths
  nr_of_subpaths = int_style == "DE" ? length(paths) : sum(length(get_subpaths(p)) for p in paths)
  _set_target_precision!(RS, nr_of_subpaths)
  max_prec = RS.computational_precision
  RR = ArbField(max_prec)
  embedded_differentials = [embed_mpoly(g, v, max_prec) for g in differentials]

 #Set up GL integration schemes (optimal grouping, see _gl_group_rs)
  nr_of_GL_int_pars = length(gauss_legendre_int_pars)
  if nr_of_GL_int_pars > 0
    sort!(gauss_legendre_int_pars)
    RR = parent(gauss_legendre_int_pars[1])
    gauss_legendre_int_group_rs = _gl_group_rs(gauss_legendre_int_pars, RS.computational_error; c = params.group_cost)
  end

  #Set up DE integration schemes
  double_exponential_int_group_rs = []
  nr_of_DE_int_pars = length(double_exponential_int_pars)
  if nr_of_DE_int_pars > 0
    sort!(double_exponential_int_pars)
    r_minimum = double_exponential_int_pars[1]
    r_maximum = double_exponential_int_pars[end]

    min_max_diff = RR(0)
    try 
      min_max_diff = floor(Int, 20*(r_maximum-r_minimum))
    catch
      min_max_diff = floor(Int, 20*(r_maximum-r_minimum) + 0.5)
    end

    number_of_schemes = max(min(floor(Int, nr_of_DE_int_pars/2), ), 1)

    if number_of_schemes == 1 && abs(r_minimum-r_maximum) < RR(1/20)
      push!(double_exponential_int_group_rs, RR(19/20) * r_minimum)
    else
      double_exponential_int_group_rs = [ RR(19/20) * ((RR(1)-RR(t)/RR(number_of_schemes))*r_minimum + RR(t)/RR(number_of_schemes)*r_maximum) for t in (0:number_of_schemes) ]
    end
  end

    # Computed the bound M for every path. The bound M is the maximum value of
    # the integrands along the boundary of the ellipse with radius r.

  GL_bound_temp = Vector{ArbFieldElem}()
  DE_bound_temp = Vector{ArbFieldElem}()
  subpaths = [subpath for path in paths for subpath in get_subpaths(path)]
  Threads.@threads :dynamic for subpath in subpaths
    if subpath.integration_scheme == "GL"
      if path_type(subpath) == 0 && params.integration_method == "rigorous"
        compute_ellipse_bound_rigorous(subpath, dif_basis, gauss_legendre_int_group_rs, RS)
      else
        compute_ellipse_bound_heuristic(subpath, embedded_differentials, gauss_legendre_int_group_rs, RS)
      end
    elseif subpath.integration_scheme == "DE"
      compute_burger_bound_heuristic(subpath, embedded_differentials, double_exponential_int_group_rs, RS)
    else
      error("Integration scheme does not exist.")
    end
  end
  for subpath in subpaths
    append!(subpath.integration_scheme == "GL" ? GL_bound_temp : DE_bound_temp, subpath.bounds)
  end

  # accuracy = :big/:both: the big period matrix is wanted to an absolute
  # 2^-prec, but its entries are about as large as the integrands (up to
  # 2^70 for curves with coefficients of very different sizes), and the
  # rounding errors are relative. Raise the working precision by log2 of the
  # (heuristic) integrand bound, to avoid a precision retry.
  if params.accuracy !== :small
    allb = vcat(GL_bound_temp, DE_bound_temp, RS.bounds)
    extra = isempty(allb) ? 0 : _magnitude_guard_bits(maximum(allb))
    if extra > 0
      _set_target_precision!(RS, nr_of_subpaths; extra = extra)
      max_prec = RS.computational_precision
      RR = ArbField(max_prec)
      embedded_differentials = [embed_mpoly(g, v, max_prec) for g in differentials]
    end
  end

  if nr_of_GL_int_pars>0
    GL_bound_temp_max = maximum(GL_bound_temp)

    push!(RS.bounds, GL_bound_temp_max)
    bound = maximum(RS.bounds)

    #Maybe change error value.
    #Change max_prec

    # Compute integration schemes. The number of abscissae N depends on r and M.
    # The goal is to minimize the size of N. r has strong influence on the size of N while the
    # contribution of M is logarithmic.
    # (One bound for all schemes on purpose: the heuristic bound of a single
    # subpath can be too small, the maximum over all subpaths has been safe.)
    RS.integration_schemes_GL = [IntegrationSchemeGL(r, max_prec, RS.computational_error, bound) for r in gauss_legendre_int_group_rs ]
  end

  if nr_of_DE_int_pars>0
    DE_bound_temp_max = maximum(DE_bound_temp)
    push!(RS.bounds, DE_bound_temp_max)
    bound = maximum(RS.bounds)
    RS.integration_schemes_DE = [IntegrationSchemeDE(r, max_prec, [bound, bound], RS.target_precision) for r in double_exponential_int_group_rs ]
  end

  f = embed_mpoly(defining_polynomial(RS), v, max_prec)
  CC = base_ring(f)
  I = onei(CC)
  f = change_base_ring(CC, f, parent = parent(f))

  Kxy = parent(f)
  Ky, y = polynomial_ring(base_ring(Kxy), "y")
  m = degree(f, 2)

  # The monodromy representation is computed here as a by-product of the
  # analytic continuation along the paths. (If only the monodromy were needed,
  # far fewer points than the abscissae of the integration schemes would do.)
  s_m = SymmetricGroup(m) # ::AbstractAlgebra.Generic.SymmetricGroup{Int}

  _, fm, mp, rp = differential_form_data(RS)
  Cp = AcbField(max_prec)          # created once, before any threads
  f_split = _split_in_y(f)         # f already embedded at max_prec

  scheme(sp) = sp.integration_scheme == "GL" ? RS.integration_schemes_GL[sp.integration_scheme_index] :
                                             RS.integration_schemes_DE[sp.integration_scheme_index]
  cost(p) = sum(length(scheme(sp).abscissae) for sp in p.sub_paths)
  order = sortperm(paths, by = cost, rev = true)
  # Optional low precision for the intermediate continuation points (off when
  # params.midpoint_precision == 0, or when it would not be lower than max_prec).
  lo_data = nothing
  if params.midpoint_precision > 0
    lo_prec = max(100, min(params.midpoint_precision, max_prec))
    # The low precision must resolve the geometry: if discriminant points lie
    # closer together than ~2^(30 - lo_prec) (relative), steps near them cannot
    # even be represented at lo_prec. Then switch the midpoint precision off
    # (recorded in the resolved parameters).
    if lo_prec < max_prec && !_resolvable_at(disc_points, lo_prec - 30)
      @info "Midpoint precision $(params.midpoint_precision) is too low for the distances between the discriminant points of this curve; it is switched off."
      params.midpoint_precision = 0
    elseif lo_prec < max_prec
      f_lo = embed_mpoly(defining_polynomial(RS), v, lo_prec)
      Ky_lo, _ = polynomial_ring(base_ring(f_lo), "y")
      lo_data = (_split_in_y(f_lo), Ky_lo)
    end
  end

  _integrate_paths_chunked!(paths, order, scheme, Cp, max_prec, f_split, Ky,
                            embedded_differentials, fm, mp, rp, s_m, m, g;
                            chunk_len = params.chunk_len, lo_data = lo_data, adaptive = params.adaptive,
                            qerr = RS.computational_error)

  # The monodromy (the chains around the discriminant points and around
  # infinity) is a by-product of the continuation along the paths. If it was
  # computed before without periods (_ensure_monodromy!), the chains are kept
  # and only get their integral matrices.
  if isdefined(RS, :pi1_chains)
    _refresh_chains!(RS)
  else
    _build_chains!(RS, paths, pi1_gens, s_m)
  end
  params.direct_infinity && _check_direct_inf_chain!(RS)
  closed_chains = vcat(RS.closed_chains, [RS.inf_chain])

  cycles, K, sym_transform = homology_basis(RS)

  # The pre-period matrix is the matrix computed using the 2g + m - 1 cycles
  # computed by homology_basis. We will later normalize this using the matrix S
  # computed in homology_basis so that the first 2g cycles actually form
  # a homology basis and we get a proper perios matrix.
  pre_period_matrix = Vector{AcbFieldElem}[]

  #For all 2g + m - 1 cycles we compute the integrals of the g differential
  #forms.

  sheet_to_sheet_integrals = zero_matrix(CC, m, g)
  sheets_left = Set((2:m))
  sheets_meet = Set()

  for cycle in cycles
    if length(sheets_left) != 0 
      sheets_in_cycle = Set([ cycle[2*l+1] for l in (1:round(Int,(length(cycle)-1)/2-1)) ])
      sheets_meet = intersect(sheets_left, sheets_in_cycle)
      sheets_left = setdiff(sheets_left, sheets_meet)
    end
		cycle_integral = [zero(CC) for x in 1:g]
		l = 1
		while l < length(cycle)
      #Identify sheet we end up in after moving along the chain.
			sheet = cycle[l]
			while sheet != cycle[l+2]
        # Add the correct contribution based on the sheet we are in.
				cycle_integral += closed_chains[cycle[l+1]].integral_matrix[sheet,:]
				sheet = permutation(closed_chains[cycle[l+1]])[sheet]
        if sheet in sheets_meet
          sheet_to_sheet_integrals[sheet,:] = cycle_integral
          setdiff!(sheets_meet, Set([sheet]))
        end
			end
			l += 2
		end
		push!(pre_period_matrix, cycle_integral)
	end

  RS.sheet_to_sheet_integrals = sheet_to_sheet_integrals

  #Use symmetric transform S to normalize the polarization
	PMAPMB = sym_transform * matrix(pre_period_matrix)

  # Cut of the first 2g columns to get the actual period matrix.
	big_period_matrix = transpose(PMAPMB[1:2*g,:])
  dependent_columns = PMAPMB[2g+1:end, :]
  @req all([contains(r, zero(CC)) for r in dependent_columns]) "Sanity check failed. There may have been an error in the period matrix computation."
  return big_period_matrix
end

#Compute the small period matrix.
@doc raw"""
 small_period_matrix(RS::RiemannSurfaceModel)

Compute the small period matrix for the Riemann surface.
"""
function small_period_matrix(RS::RiemannSurfaceModel)
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

function compute_reduction_matrix(RS::AbstractRiemannSurfaceModel, type::String)
  g = genus(RS)
  @req (type == "real" || type =="complex") "Type has to be either 'real' or 'complex'."
  if type == "real" && !isdefined(RS, :real_reduction_matrix)
    P = big_period_matrix(RS)
    prec = precision(base_ring(P))
    M = zero_matrix(ArbField(prec), 2*g, 2*g)
    for j in (1:g)
      for k in (1:g)
        M[j,k] = real(P[j,k])
        M[j+g,k] = imag(P[j,k])
        M[j,k+g] = real(P[j,k+g])
        M[j+g,k+g] = imag(P[j,k+g])
      end
    end
    RS.real_reduction_matrix = _inv_precond(M)
  else
    tau = small_period_matrix(RS)
    CC = base_ring(tau)
    if length(RS.complex_reduction_matrices) == 1
      i_tau = imag(tau)
      push!(RS.complex_reduction_matrices, change_base_ring(CC, _inv_precond(i_tau)))
    end
  end
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
