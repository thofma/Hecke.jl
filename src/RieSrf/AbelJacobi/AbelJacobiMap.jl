################################################################################
#
#  RieSrf/AbelJacobi/AbelJacobiMap.jl : the Abel-Jacobi map
#
#  AJ(D) = sum_j n_j int_{P0}^{P_j} (omega_1, ..., omega_g) for a divisor
#  D = sum_j n_j P_j (D - deg(D) P0 if the degree is not 0), optionally reduced
#  modulo the period lattice. For a generic point the integral runs from the
#  base point along a chain of the fundamental group to a nearby path start,
#  and from there along a line, with detours around the discriminant points,
#  to the point; sheet_to_sheet_integrals connects the sheets at the base
#  point. Points over discriminant points and points at infinity are reached
#  by double exponential integration into the point (heuristic,
#  _abel_jacobi_special_point!); critical points with method :swap on the model
#  with x and y swapped. Divisors on another model of the surface are moved
#  to the computational model first; for the superelliptic model see
#  Superelliptic.jl.
#
#  Entry point: abel_jacobi_map.
#
################################################################################

################################################################################
#
#  Reduction modulo the period lattice
#
################################################################################

# AJ value V as an element of R^2g / Z^2g: the coordinates with respect to
# the periods, reduced modulo 1.
function _period_lattice_reduction_real(V::AcbMatrix, RS::AbstractRiemannSurfaceModel)
  g = genus(RS)
  T = RS.real_reduction_matrix
  RR = base_ring(T)
  W = T * vcat(real(V), imag(V))
  return matrix(RR, 2*g, 1, [w - round(ZZRingElem, w) for w in W])
end

# AJ value V as an element of C^g / (Z^g + tau Z^g) (normalized with P1^-1),
# reduced to the fundamental domain.
function _period_lattice_reduction_complex(V::AcbMatrix, RS::AbstractRiemannSurfaceModel)
  g = genus(RS)
  CC = parent(V[1, 1])
  tau = small_period_matrix(RS)
  V = RS.complex_reduction_matrices[1] * V
  W = real(RS.complex_reduction_matrices[2]) * imag(V)
  V -= tau * matrix(CC, g, 1, [round(ZZRingElem, w) for w in W])
  return V - matrix(CC, g, 1, [round(ZZRingElem, real(v)) for v in V])
end

# The AJ value reduced as asked for (reduction :none, :real or :complex).
function _reduce_abel_jacobi(V::AcbMatrix, RS::AbstractRiemannSurfaceModel, reduction::Symbol)
  reduction === :none && return V
  _compute_reduction_matrix!(RS, reduction)
  return reduction === :real ? _period_lattice_reduction_real(V, RS) :
                               _period_lattice_reduction_complex(V, RS)
end

################################################################################
#
#  Integration along a line to a point
#
################################################################################

# The line `path` with detours along arcs of the circles of radius
# RS.safe_radii around the discriminant points it crosses (in the order in
# which it crosses them), as a vector of paths. The side of a detour is
# chosen by the position of the discriminant point relative to the line from
# the base point to the end of the path (-1 if undecided).
function _path_avoiding_disc_points(path::CPath, RS::RiemannSurfaceModel)
  @req is_line(path) "Path needs to be a line."
  disc_points = discriminant_points_high_prec(RS)
  crossings = Tuple{Int, AcbFieldElem, AcbFieldElem}[]
  for (j, disc_point) in enumerate(disc_points)
    circle = circle_path(disc_point - RS.safe_radii[j], disc_point)
    intersects, points = intersection_points(path, circle)
    intersects && push!(crossings, (j, points[1], points[2]))
  end
  x_start = start_point(path)
  sort!(crossings, by = c -> _arb_mid_f64(abs(c[2] - x_start)))

  pieces = [path]
  x0 = RS.base_point.coordx
  I = onei(parent(x0))
  for (j, entry, exit) in crossings
    disc_point = disc_points[j]
    side = angle((disc_point - x0) * exp(-angle(end_point(path) - x0)*I))
    orientation = -1
    try
      orientation = sign(Int, side)
    catch
    end
    arc = arc_path(entry, exit, disc_point, orientation = orientation)
    rest = line_path(end_point(arc), end_point(path))
    last_piece = pop!(pieces)
    if contains(start_point(last_piece), entry)
      append!(pieces, [arc, rest])
    else
      append!(pieces, [line_path(start_point(last_piece), entry), arc, rest])
    end
  end
  return pieces
end

# The GL scheme for a subpath of the Abel-Jacobi paths: the scheme with the
# largest parameter below the parameter of the subpath. If there is none, a
# new scheme is made (parameter as for a group, see _gl_group_r, bound from
# the subpath). New schemes are appended, so that the indices of the schemes
# of the period computation stay valid.
function _abel_jacobi_scheme!(RS::RiemannSurfaceModel, subpath::CPath, embedded_differentials)
  schemes = RS.integration_schemes_GL
  r = subpath.quadrature_parameter
  best = 0
  for (i, scheme) in enumerate(schemes)
    if r > scheme.quadrature_parameter &&
       (best == 0 || scheme.quadrature_parameter > schemes[best].quadrature_parameter)
      best = i
    end
  end
  if best == 0
    r_group = _gl_group_r(r)
    _ellipse_bound_heuristic!(subpath, embedded_differentials, [r_group], RS)
    push!(schemes, IntegrationSchemeGL(r_group, RS.computational_precision + 10,
                                       RS.computational_error, maximum(subpath.bounds)))
    best = length(schemes)
  end
  subpath.integration_scheme_index = best
  return schemes[best]
end

# Integrate the differentials along the paths (from _path_avoiding_disc_points)
# on the sheet that ends in y_end over the end point: the paths are
# continued backwards from the end point. Afterwards every path has its
# 1 x g integral matrix, and paths[1].sheets holds the y-value at the start.
function _integrate_on_sheet!(paths::Vector{CPath}, y_end::AcbFieldElem, RS::RiemannSurfaceModel)
  work_prec = RS.computational_precision
  CC = AcbField(work_prec)
  _, y = polynomial_ring(CC)
  v = RS.embedding
  f = _embed_mpoly(defining_polynomial(RS), v, work_prec)
  differentials, factor_matrix, min_powers, power_ranges = differential_form_data(RS)
  embedded_differentials = [_embed_mpoly(omega, v, work_prec) for omega in differentials]
  g = genus(RS)
  cache = DifferentialFactorCache(embedded_differentials, factor_matrix, min_powers, power_ranges)
  values = [CC() for _ in 1:1, _ in 1:g]          # one sheet

  reverse_paths = reverse([reverse(path) for path in paths])
  fiber = sort!(_accurate_roots(f(start_point(reverse_paths[1]), y), work_prec), lt = sheet_ordering)
  _, sheet = closest_point(y_end, fiber)

  for path in reverse_paths
    _gauss_legendre_path_parameters!(RS.discriminant_points, path, RS.computational_error)
    integral_matrix = zero_matrix(CC, 1, g)
    for subpath in path.subpaths
      scheme = _abel_jacobi_scheme!(RS, subpath, embedded_differentials)
      abscissae = scheme.abscissae
      weights = scheme.weights
      x_values, fibers = analytic_continuation(RS, subpath, abscissae, fiber, work_prec)
      subpath_integral = zero_matrix(CC, 1, g)
      for i in eachindex(abscissae)
        # lines: the constant derivative is applied afterwards
        weight = is_line(subpath) ? CC(weights[i]) :
                                    CC(weights[i] * evaluate_derivative(subpath, abscissae[i]))
        _evaluate_differentials!(values, cache, x_values[i+1], [fibers[i+1][sheet]], weight)
        subpath_integral += matrix(CC, values)
      end
      if is_line(subpath)
        subpath_integral *= evaluate_derivative(subpath, abscissae[1])
        set_integral_matrix!(subpath, subpath_integral)
      end
      integral_matrix += subpath_integral
      fiber = fibers[end]
      paths[1].sheets = [fibers[end][sheet]]
    end
    set_integral_matrix!(path, integral_matrix)
  end

  for k in 1:length(paths)
    set_integral_matrix!(paths[k], -reverse_paths[end-k+1].integral_matrix)
  end
end

################################################################################
#
#  The Abel-Jacobi map
#
################################################################################

@doc raw"""
    abel_jacobi_map(P::RiemannSurfacePoint, method = :swap, reduction = :complex) -> AcbMatrix

The Abel-Jacobi map of the divisor P - P0, P0 the base point of the Riemann
surface. See `abel_jacobi_map(D::RiemannSurfaceDivisor, ...)`.
"""
function abel_jacobi_map(P::RiemannSurfacePoint, method = :swap, reduction = :complex)
  return abel_jacobi_map(divisor([P], [1]), method, reduction)
end

@doc raw"""
    abel_jacobi_map(P::RiemannSurfacePoint, Q::RiemannSurfacePoint, method = :swap,
                    reduction = :complex) -> AcbMatrix

The Abel-Jacobi map of the divisor P - Q.
"""
function abel_jacobi_map(P::RiemannSurfacePoint, Q::RiemannSurfacePoint, method = :swap,
                         reduction = :complex)
  return abel_jacobi_map(divisor([P, Q], [1, -1]), method, reduction)
end

@doc raw"""
    abel_jacobi_map(D::RiemannSurfaceDivisor, P0::RiemannSurfacePoint, method = :swap,
                    reduction = :complex) -> AcbMatrix

The Abel-Jacobi map of the divisor D - deg(D) P0.
"""
function abel_jacobi_map(D::RiemannSurfaceDivisor, P0::RiemannSurfacePoint, method = :swap,
                         reduction = :complex)
  return abel_jacobi_map(D - degree(D)*P0, method, reduction)
end

@doc raw"""
    abel_jacobi_map(D::RiemannSurfaceDivisor, method = :swap, reduction = :complex) -> AcbMatrix

The Abel-Jacobi map of the divisor D with respect to the base point P0 of the
Riemann surface: for ``D = \sum_j n_j D_j`` the g x 1 matrix with entries
``\sum_j n_j \int_{P0}^{D_j} \omega_i``, where the ``\omega_i`` are the basis
of differentials of the computational model.

`method`:
- `:swap`: the Abel-Jacobi map of critical points is computed on the curve
  f(y, x) = 0 if possible.
- `:direct`: critical points are reached by integrating into them directly
  (heuristic: there are no error bounds at critical points).

`reduction`:
- `:complex`: the result is reduced to C^g / (Z^g + tau Z^g), tau the small
  period matrix (after normalizing with P1^-1).
- `:real`: the result is given in R^2g / Z^2g (coordinates with respect to
  the periods).
- `:none`: the result as computed.
(Strings such as `"swap"` or `"complex"` are accepted as well.)
"""
function abel_jacobi_map(D::RiemannSurfaceDivisor, method = :swap, reduction = :complex)
  V = _abel_jacobi_map(D, _option_symbol(method), _option_symbol(reduction))
  # the output type chosen for the RiemannSurface (AcbField or ComplexField)
  RS = riemann_surface(D)
  return isdefined(RS, :surface) ? _out(RS.surface, V) : V
end

function _abel_jacobi_map(D::RiemannSurfaceDivisor, method::Symbol, reduction::Symbol)
  @req reduction in (:none, :real, :complex) "reduction must be :none, :real or :complex."
  @req method in (:swap, :direct) "method must be :swap or :direct."
  RS = riemann_surface(D)
  # A divisor on another model of the same Riemann surface (e.g. points of the
  # curve as given, while the periods are computed on another model): move it
  # to the computational model, whose bases the result refers to.
  if isdefined(RS, :surface)
    C = computational_model(RS.surface)
    if C isa SuperellipticModel
      isdefined(D, :abel_jacobi_value) || (D.abel_jacobi_value = _se_abel_jacobi(C, D))
      return _reduce_abel_jacobi(D.abel_jacobi_value, C, reduction)
    end
    if C !== RS
      if !isdefined(D, :abel_jacobi_value)
        big_period_matrix(C)     # before the points are created on C (monodromy as a by-product)
        D2 = _transfer_divisor(D, C)
        _abel_jacobi_map(D2, method, :none)
        D.abel_jacobi_value = D2.abel_jacobi_value
      end
      return _reduce_abel_jacobi(D.abel_jacobi_value, C, reduction)
    end
  end
  big_period_matrix(RS)
  isdefined(D, :abel_jacobi_value) || (D.abel_jacobi_value = _abel_jacobi_value(RS, D, method))
  return _reduce_abel_jacobi(D.abel_jacobi_value, RS, reduction)
end

_heuristic_warning(extra::String = "") =
  @warn "Heuristic methods have been used in this computation as the divisor included critical points for which we have no nice error bounds. The output is most likely still correct, but it is not provably correct.$extra" maxlog = 1

# The unreduced AJ value (g x 1) of a divisor on the model RS, whose periods
# have been computed.
function _abel_jacobi_value(RS::RiemannSurfaceModel, D::RiemannSurfaceDivisor, method::Symbol)
  g = genus(RS)
  CC = AcbField(RS.computational_precision)
  RR = ArbField(RS.computational_precision)
  infty = CC(1/0)
  total = zero_matrix(CC, 1, g)
  sheet_to_sheet = RS.sheet_to_sheet_integrals
  points, mults = support(D)
  for (P, mult) in zip(points, mults)
    if P.coordx == infty
      # a point at infinity: integral to infinity on its sheet
      sheet = P.sheets[1]
      @req sheet in 1:RS.degree[1] "Error in Abel-Jacobi map."
      if !isdefined(RS, :ajm_infinite_points)
        _abel_jacobi_special_point!(line_to_infinity(RS.base_point.coordx), 0, RS, RS.inf_chain)
      end
      sheet0 = inv(RS.ajm_infinite_points.permutation)[sheet]
      total += matrix(CC, 1, g, mult * (RS.ajm_infinite_points.integral_matrix[sheet0, :] +
                                        sheet_to_sheet[sheet0, :]))
      _heuristic_warning()
      continue
    end
    # Points over discriminant points lie on the chains around them
    # (SpecialPoints.jl); ajm_discriminant_points and
    # _abel_jacobi_special_point! index these chains (RS.pi1_chains).
    dist, ind = _disc_chain_index(RS, P.coordx)
    if P.is_singular || P.coordy == infty || (P in RS.critical_points && method === :direct)
      @req contains(dist, RR(0)) "Error in Abel-Jacobi map."
      # (the sheets of such a point are known; the fiber over it has a
      # multiple root and cannot be recomputed with isolated roots)
      @req isdefined(P, :sheets) "Error in Abel-Jacobi map."
      isassigned(RS.ajm_discriminant_points, ind) || _abel_jacobi_disc_point!(RS, ind)
      chain = RS.ajm_discriminant_points[ind]
      sheet = P.sheets[1]
      total += matrix(CC, 1, g, mult * (chain.integral_matrix[sheet, :] + sheet_to_sheet[sheet, :]))
      if P in RS.critical_points && !P.is_singular && P.coordy != infty
        _heuristic_warning(" It may be possible to use the method :swap for provably correct results.")
      else
        _heuristic_warning()
      end
    elseif P in RS.critical_points
      # method :swap: the point is not critical on the swapped model; there
      # the differentials are -omega_i (see swapped_surface), hence O - Q
      @req contains(dist, RR(0)) "Error in Abel-Jacobi map."
      swapped_surface(RS)
      Q = RS.swapped_surface([P.coordy, P.coordx])
      O = RS.swapped_surface([RS.base_point.coordy, RS.base_point.coordx])
      O_minus_Q = O - Q
      _abel_jacobi_map(O_minus_Q, method, :none)
      # (the swapped surface has its own working precision, e.g. from the
      #  magnitude guard bits of accuracy = :big/:both)
      total += mult * change_base_ring(CC, transpose(O_minus_Q.abel_jacobi_value))
    else
      # a generic finite point (not critical, not singular, not y-infinite)
      total += matrix(CC, 1, g, mult * _ajm_generic_point(RS, P, CC, RR, g))
    end
  end
  return transpose(total)
end

# Index (in RS.pi1_chains) of the chain around the discriminant point closest
# to x, and the distance.
function _disc_chain_index(RS::RiemannSurfaceModel, x::AcbFieldElem)
  return closest_point(x, [center(C) for C in RS.pi1_chains])
end

# Paths from the base point to the starting point of the path whose start is
# closest to x. May be empty (then the end point is the base point).
function _chain_to_closest_start(RS::RiemannSurfaceModel, x::AcbFieldElem)
  _, ind = closest_point(x, RS.ajm_starting_points)
  gens = RS.fundamental_group_of_P1[2]          # all generators, signed path indices
  chains = RS.pi1_chains                        # same order as gens
  for i in eachindex(gens)
    j = findfirst(t -> abs(t) == ind, gens[i])
    j === nothing && continue
    # forward occurrence: stop before the path (its start is the chain point);
    # reversed occurrence: include it (the reversed path ends at the start)
    k = gens[i][j] > 0 ? j - 1 : j
    return chains[i].paths[1:k]
  end
  error("Abel-Jacobi map: no generator of the fundamental group passes through the chosen starting point.")
end

# Contribution of a finite, non-critical point P to the Abel-Jacobi map.
function _ajm_generic_point(RS::RiemannSurfaceModel, P, CC::AcbField, RR::ArbField, g::Int)
  dist0, i0 = closest_point(P.coordx, RS.discriminant_points)
  if contains(dist0, zero(RR))
    return _ajm_regular_point_over_disc(RS, P, i0, CC, RR, g)
  end
  f = complex_defining_polynomial(RS)
  dist, sheet = closest_point(P.coordy, fiber(f, P.coordx))
  @req contains(dist, RR(0)) "Error in Abel-Jacobi map."
  base_point_x = RS.base_point.coordx
  s_to_s = RS.sheet_to_sheet_integrals

  if contains(abs(P.coordx - base_point_x), zero(RR))
    return [s_to_s[sheet, t] for t in 1:g]
  end

  prefix = _chain_to_closest_start(RS, P.coordx)
  x_start = isempty(prefix) ? base_point_x : end_point(prefix[end])

  # line from x_start to P (with detours around the safe circles)
  if contains(abs(P.coordx - x_start), zero(RR))
    sheet_start = sheet
    line_row = [zero(CC) for _ in 1:g]
  else
    path_to_x = _path_avoiding_disc_points(line_path(x_start, P.coordx), RS)
    _integrate_on_sheet!(path_to_x, P.coordy, RS)
    dist, sheet_start = closest_point(path_to_x[1].sheets[1], fiber(f, x_start))
    @req contains(dist, RR(0)) "Error in Abel-Jacobi map."
    line_row = sum(p.integral_matrix[1, :] for p in path_to_x)
  end

  # chain from the base point to x_start
  if isempty(prefix)
    sheet0 = sheet_start
    chain_row = [zero(CC) for _ in 1:g]
  else
    new_chain = CChain(prefix)
    sheet0 = inv(new_chain.permutation)[sheet_start]
    chain_row = new_chain.integral_matrix[sheet0, :]
  end

  return s_to_s[sheet0, :] + chain_row + line_row
end

# A regular point P (f_y(P) != 0) whose x-coordinate is a discriminant point:
# other sheets meet over x(P), e.g. a point of the swapped surface lying over
# the image of a node. The fiber over x(P) cannot be isolated, so
#     AJ(P) = AJ(P1) + int_{P1}^{P} omega
# for the point P1 over x1 = x(P) + delta on the sheet of P (delta a quarter of
# the distance to the next discriminant point, away from it). y is an analytic
# function of x on the disk around x(P) up to the next discriminant point (P is
# a simple root), so the short integral is done with Gauss-Legendre and y by
# Newton's method along the segment. Heuristic, like the other special points.
function _ajm_regular_point_over_disc(RS::RiemannSurfaceModel, P, i0::Int, CC::AcbField,
                                      RR::ArbField, g::Int)
  prec = precision(CC)
  f = complex_defining_polynomial(RS, prec)
  fy = derivative(f, 2)
  x0 = CC(P.coordx)
  y0 = CC(P.coordy)
  @req !contains(fy(x0, y0), zero(CC)) "Error in Abel-Jacobi map: the point is critical."
  newton(x, y) = (for _ in 1:(ceil(Int, log2(prec)) + 4); y = _acb_mid(y - f(x, y)/fy(x, y)); end; y)

  D = RS.discriminant_points
  others = [CC(d) for (j, d) in enumerate(D) if j != i0]
  if isempty(others)
    delta, dir = RR(1)/4, one(CC)
  else
    rho, j = closest_point(x0, others)
    delta, dir = rho/4, (x0 - others[j])/abs(x0 - others[j])
  end
  x1 = _acb_mid(x0 + delta*dir)

  # y at x1 on the sheet of P: Newton in a few steps along the segment, then
  # the exact root of the (isolated) fiber over x1
  y = y0
  for k in 1:8
    y = newton(x0 + (x1 - x0)*QQ(k, 8), y)
  end
  ys1 = fiber(f, x1)
  _, s1 = closest_point(y, ys1)
  y1 = ys1[s1]
  row1 = _ajm_generic_point(RS, RS([x1, y1]), CC, RR, g)

  # int_{x1}^{x0} omega on the sheet of P
  N = Int(_gauss_legendre_parameters(ArbField(prec)(4), RS.computational_error))
  abscissae, weights = _gauss_legendre_nodes(N, prec)
  factors = [_embed_mpoly(q, RS.embedding, prec) for q in differential_form_data(RS)[1]]
  half = (x0 - x1)/2
  mid = (x0 + x1)/2
  integral = [zero(CC) for _ in 1:g]
  y = y0
  for k in sortperm(abscissae, by = t -> -_arb_mid_f64(t))   # from x0 towards x1
    x = mid + half*abscissae[k]
    y = newton(x, y)
    vals = _evaluate_differentials(RS, factors, x, [y])
    for t in 1:g
      integral[t] += weights[k]*vals[1, t]*half
    end
  end
  return [row1[t] + integral[t] for t in 1:g]
end

################################################################################
#
#  Special points (heuristic)
#
################################################################################

# The integrals from the start of gamma into a special point at its end, on
# all sheets, by double exponential quadrature (without the isolation check
# of the analytic continuation, which does not work towards infinity or a
# multiple root). Used for points at infinity (k = 0, gamma a line to
# infinity), singular and y-infinite points, and with method :direct for
# critical points (k: the index of the chain around the discriminant point).
# Heuristic: the step size h is halved until the result agrees with
# test_chain (integrals around the point, if its monodromy is not trivial) or
# with the previous result, at most max_iterations times. The error estimate
# is added to the radii.
#
# Not adaptive on purpose: the continuation is not stable enough for that,
# recomputing everything per iteration works better. A possible speed-up:
# integrate the part of the path away from the special point rigorously and
# only the end as here.
function _abel_jacobi_special_point!(gamma::CPath, k::Int, RS::RiemannSurfaceModel, test_chain::CChain,
                                     max_iterations::Int = 5)
  prec = RS.computational_precision
  stalled = true
  refine = true

  iterations = 1

  CC = complex_field(RS)

  if k == 0   #Point at infinity
    c = maximum([ length(cycle) for cycle in  collect(cycles(permutation(RS.inf_chain))) ])+1
  else
    c = maximum([ length(cycle) for cycle in  collect(cycles(permutation(RS.pi1_chains[k]))) ])+1
  end
  
  comp_error = RS.computational_error
  m = RS.degree[1]
  g = genus(RS)
  h = QQ(16//125)
  s_m = SymmetricGroup(m)

  if permutation(test_chain) != one(s_m)
    target_error = maximum(map(x-> abs(x)-trim(abs(x)), test_chain.integral_matrix))
  else 
    target_error = maximum(map(x-> abs(x)-trim(abs(x)), small_period_matrix(RS)))
  end
  
  yj_new = CC(0)
  V = zero_matrix(CC, m, g)

  gammas = CPath[]
  while refine && iterations <= max_iterations
    refine = false
    # (heuristic choice of the precision)
    comp_prec = 2*c*prec
    CC = AcbField(comp_prec)
    RR = ArbField(comp_prec)
    Cz, z = polynomial_ring(CC)
    Cxy, (x,y) = polynomial_ring(CC,2)
    v = RS.embedding
    fC = _embed_mpoly(defining_polynomial(RS), v, comp_prec)
    differentials, fm, mp, rp = differential_form_data(RS)
    embedded_differentials = [_embed_mpoly(g, v, comp_prec) for g in differentials]
    # Built once per refinement round instead of once per abscissa
    ws = ContinuationWorkspace(_split_in_y(fC), Cz)
    dcache = DifferentialFactorCache(embedded_differentials, fm, mp, rp)
    vals = [CC() for _ in 1:m, _ in 1:g]

    if k == 0 #Point at infinity
      N_gamma = gamma
      err2 = (RR(1/2)*comp_error^(c+1))^2
    else
      N_gamma = line_path(CC(start_point(gamma)),CC(end_point((gamma))))
      err2 = comp_error^2/4
    end

    N = round(Int, 1//h * 72 //10)
    N2P1 = 2*N+1
    abscissae, weights = _tanh_sinh_nodes(N, RR(h))
    push!(abscissae,RR(1))
    xj = start_point(N_gamma)
		yj =  sort!(_accurate_roots(fC(xj, z), comp_prec), lt = sheet_ordering)
    yj_new = yj

    path_difference_matrix = zero_matrix(CC, m, g)
    for i in (1:N2P1)
      xj_new = evaluate(N_gamma, abscissae[i+1])
      # (without the isolation check, see above; the result is checked
      # heuristically below)
      try
        yj_new, stalled = _continue_unchecked!(ws, xj, xj_new, yj, err2, target_error)
        if stalled
          refine = true
          c +=1
          h = h/2
          iterations +=1
          break
        end
      catch
        break
      end

      # weight (times dx) is folded into the evaluation
      wi = CC(weights[i] * evaluate_derivative(N_gamma, abscissae[i]))
      _evaluate_differentials!(vals, dcache, xj, yj, wi)
      integral_matrix_contribution = matrix(CC, vals)
      
      max_abs = maximum([abs(c) for c in integral_matrix_contribution])
      if (i > N && max_abs < comp_error)
        break
      end

      xj = xj_new
      yj = yj_new
      
			path_difference_matrix += integral_matrix_contribution
		end

    set_integral_matrix!(N_gamma, path_difference_matrix)
    push!(gammas, N_gamma)

    if refine == false 
      if permutation(test_chain) != one(s_m)
        sigma = permutation(test_chain)
        V = N_gamma.integral_matrix - inv(sigma) * N_gamma.integral_matrix -  change_base_ring(CC,test_chain.integral_matrix)
        err_V = maximum([ abs(c) for c in V ])
        if contains(target_error*100, err_V)
          refine = false 
          continue
        else 
          h = h/2
          refine = true
          stalled = false
          iterations += 1
        end
      else
        # no monodromy to compare with: compare with the previous result (h/2)
        s = length(gammas)
        if s == 1
          refine = true
          h = h/2
          stalled = false
          continue
        else
          V = gammas[s].integral_matrix-gammas[s-1].integral_matrix
          err_V = maximum([ abs(c) for c in V ])
           if contains(target_error*100, err_V)
              refine = false 
              continue
          else 
            h = h/2
            refine = true
            stalled = false
            iterations += 1
          end
        end
      end
    end
  end

  final_gamma = gammas[end]
  # error, permutation and sheets
  path_perm = sortperm(yj_new, lt = sheet_ordering)
  set_permutation!(final_gamma, inv(s_m(path_perm)))

  V = map(abs, V)
  # add the heuristic error
  for i in (1:m)
    for j in (1:g)
      t = final_gamma.integral_matrix[i,j]
      err_t = V[i,j]
      _add_error!(t, err_t)
      final_gamma.integral_matrix[i,j] = t
    end
  end
  if k == 0 #Point at infinity
    RS.ajm_infinite_points = final_gamma
  else
    set_integral_matrix!(gamma, final_gamma.integral_matrix)
    gamma.sheets = yj_new
    set_permutation!(gamma, permutation(final_gamma))
  end
end

# The chain from the base point into the discriminant point of the chain k
# (RS.pi1_chains[k]): the chain up to the end of its loop around the point,
# and a line from there to the point, integrated by
# _abel_jacobi_special_point! (the loop is the test chain). Stored in
# RS.ajm_discriminant_points[k], with the y-values at the point per sheet.
function _abel_jacobi_disc_point!(RS::RiemannSurfaceModel, k::Int)
  chain = RS.pi1_chains[k]
  loop, l = _loop_around_center(chain)
  path_to_center = vcat(chain.paths[1:l-1], line_path(chain.paths[l-1].end_point_high, chain.center))
  _abel_jacobi_special_point!(path_to_center[l], k, RS, CChain(loop))
  chain_to_center = CChain(path_to_center)
  sigma = prod([permutation(path_to_center[j]) for j in 1:l-1])
  chain_to_center.sheets = [path_to_center[l].sheets[sigma[s]] for s in 1:RS.degree[1]]
  RS.ajm_discriminant_points[k] = chain_to_center
end

# The paths of the loop of a chain around its discriminant point (the arcs
# and circles around the center of the chain), and the index of the first
# path after the loop.
function _loop_around_center(chain::CChain)
  paths = chain.paths
  CC = paths[1].field
  l = 1
  while (!is_arc(paths[l]) && !is_circle(paths[l])) || !contains(center(paths[l]) - center(chain), CC(0))
    l += 1
  end
  loop = CPath[]
  while !is_line(paths[l])
    push!(loop, paths[l])
    l += 1
  end
  return loop, l
end
