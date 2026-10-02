################################################################################
#
#  RieSrf/Periods/Quadrature/Bounds.jl : bounds for the integrand
#
#  The number of nodes of a quadrature depends (logarithmically) on a bound M
#  for the integrand on the region around the path where it is holomorphic:
#  the image of the ellipse E_r (Gauss-Legendre) or of the burger
#  (double exponential). The bounds here are heuristic: 10 times the largest
#  value of the integrand at a few sample points on the boundary of that
#  region, near the closest discriminant point.
#
#  Entry points: _ellipse_bound_heuristic!, _burger_bound_heuristic!.
#
################################################################################

# Heuristic bound 10 * max |integrand| at the point subpath(t). f: the
# defining polynomial embedded at precision prec (embedded here if nothing).
# If the balls are not finite at this precision (cancellation, e.g. for
# discriminant points of very different sizes), the fiber and the
# differentials are evaluated again at a higher precision (only a few correct
# bits are needed).
function _integrand_bound(RS::RiemannSurfaceModel, subpath::CPath, differentials,
                          t, prec::Int; f = nothing)
  RR = ArbField(prec)
  x_ball = evaluate(subpath, t)
  dx = evaluate_derivative(subpath, t)
  p = prec
  while true
    f_p = (p == prec && f !== nothing) ? f : _embed_mpoly(defining_polynomial(RS), embedding(RS), p)
    Ky, y = polynomial_ring(base_ring(f_p), "y")
    differentials_p = p == prec ? differentials :
                      [_embed_mpoly(g, embedding(RS), p) for g in differential_form_data(RS)[1]]
    x = AcbField(p)(x_ball)
    fiber_values = roots(f_p(x, y), initial_prec = p, max_prec = 8*p)
    M = _evaluate_differentials(RS, differentials_p, x, fiber_values) * dx
    values = [M[i, j] for i in 1:nrows(M), j in 1:ncols(M)]
    if all(isfinite, values)
      return 10 * maximum([RR(abs(v)) for v in values]; init = RR(0))
    end
    p >= 8*prec && error("Could not bound the integrand along a path (not finite at $p bits).")
    p *= 2
  end
end

# Gauss-Legendre: choose the scheme of the subpath (see _scheme_index) and
# bound the integrand on the boundary of the image of its ellipse E_r, at the
# point of the ellipse closest to the nearest discriminant point (in the
# parameter domain). A subpath that already has a bound (no discriminant
# point nearby, see _gauss_legendre_line_parameter!) gets the scheme with the
# largest r.
function _ellipse_bound_heuristic!(subpath::CPath, differentials::Vector{AbstractAlgebra.Generic.MPoly{AcbFieldElem}},
                                   group_rs::Vector{ArbFieldElem}, RS::RiemannSurfaceModel; f = nothing)
  if !isempty(subpath.bounds)
    subpath.integration_scheme_index = length(group_rs)
    return
  end
  index = _scheme_index(subpath.quadrature_parameter, group_rs)
  subpath.integration_scheme_index = index
  r = group_rs[index]
  # The working precision, not the (lower) requested one: for large degrees
  # (e.g. a degree 92 polynomial with tiny coefficients) f(x, y) at the
  # requested precision can have balls too wide to isolate its roots at all.
  prec = RS.computational_precision
  RR = ArbField(prec)
  I = onei(AcbField(prec))
  b = sqrt(r^2 - 1)                     # E_r has semi-axes r and b
  x = subpath.closest_disc_point_parameter

  if abs(imag(x)) < RR(10^-10)
    x_on_ellipse = sign(Int, real(x))*r
  elseif abs(real(x)) < RR(10^-10)
    x_on_ellipse = sign(Int, imag(x))*b*I
  else
    # the closest point r cos(s) + i b sin(s) to x in the first quadrant
    # (after reflecting x there): Newton's method for the zero of the
    # derivative of the distance
    im_sign = sign(Int, imag(x))
    re_sign = sign(Int, real(x))
    x_reflected = abs(real(x)) + I*abs(imag(x))
    distance_derivative = s -> cos(s)*sin(s) - r*real(x_reflected)*sin(s) + b*imag(x_reflected)*cos(s)
    second_derivative = s -> (cos(s)^2 - sin(s)^2) - r*real(x_reflected)*cos(s) - b*imag(x_reflected)*sin(s)
    s_previous = real(acos(x_reflected))
    s = s_previous - distance_derivative(s_previous)/second_derivative(s_previous)
    while abs(s - s_previous) > 10^-3
      s_previous = s
      s -= distance_derivative(s)/second_derivative(s)
    end
    x_on_ellipse = re_sign*r*cos(s) + im_sign*I*b*sin(s)
  end
  push!(subpath.bounds, _integrand_bound(RS, subpath, differentials, x_on_ellipse, prec; f = f))
  return
end

# Double exponential: choose the scheme and bound the integrand at the end
# points and at the point of the boundary of the burger
# {tanh(lambda sinh(z)) : |Im z| < r} closest to the nearest discriminant
# point (among number_of_samples points on the boundary).
function _burger_bound_heuristic!(subpath::CPath, differentials, group_rs::Vector{ArbFieldElem},
                                  RS::RiemannSurfaceModel; f = nothing,
                                  lambda::ArbFieldElem = const_pi(parent(group_rs[1]))/2,
                                  number_of_samples::Int = 20)
  if !isempty(subpath.bounds)
    subpath.integration_scheme_index = length(group_rs)
    return
  end
  index = _scheme_index(subpath.quadrature_parameter, group_rs)
  subpath.integration_scheme_index = index
  r = group_rs[index]
  prec = RS.computational_precision        # see _ellipse_bound_heuristic!
  RR = ArbField(prec)
  x = subpath.closest_disc_point_parameter
  CC = parent(x)
  I = onei(CC)
  phi(t::AcbFieldElem) = tanh(lambda*sinh(t + I*r))   # the upper boundary of the burger

  if abs(real(x)) < RR(10)^-10
    x_on_boundary = sign(Int, imag(x)) * phi(CC(0))
  else
    x_reflected = abs(real(x)) + I*abs(imag(x))
    t_max = acosh(const_pi(CC)/(2*lambda*sin(r)))
    x_on_boundary = phi(CC(0))
    min_distance = abs(x_reflected - x_on_boundary)
    for k in 1:number_of_samples
      z = phi(k/number_of_samples*t_max)
      distance = abs(x_reflected - z)
      if distance < min_distance
        min_distance = distance
        x_on_boundary = z
      end
    end
    if abs(imag(x)) < RR(10)^-10
      x_on_boundary = sign(Int, real(x)) * real(x_on_boundary) + I * imag(x_on_boundary)
    else
      x_on_boundary = sign(Int, real(x)) * real(x_on_boundary) + I * sign(Int, imag(x))*imag(x_on_boundary)
    end
  end

  for t in [CC(-1), CC(1), CC(x_on_boundary)]
    push!(subpath.bounds, _integrand_bound(RS, subpath, differentials, t, prec; f = f))
  end
  return
end

# (Rigorous bounds by covering the boundaries of the ellipses / DE regions with
# balls, as suggested by Neurohr, were tried: root isolation over a ball needs
# balls much smaller than the distances between the roots, so even when only
# an upper bound within a factor 16 of the maximum was asked for, a subpath
# needed thousands of balls (f26_g45: ~3000 per subpath, 4 s per scheme).
# Rigorous periods are left to the Voronoi approach.)

# NOT FUNCTIONAL (integration_method = :rigorous is refused, see
# _check_integration_parameters). An unfinished implementation of Strategy 1 of
# Bruin, Disney-Hogg, Gao, "Rigorous integration along straight lines"
# (https://arxiv.org/abs/2208.12377): a rigorous bound for the integrand on
# the ellipses around line subpaths. Known problems: gmin_int is undefined
# (gmin is meant), minpoly is applied to a multivariate polynomial, and arcs
# and circles are not covered.
function _ellipse_bound_rigorous!(subpath, dif_basis, int_group_rs, RS)
  if length(subpath.bounds) == 0
    i = maximum(filter(x -> (subpath.quadrature_parameter > int_group_rs[x]), 1:length(int_group_rs));init = 1)
    subpath.integration_scheme_index = i
  else 
    i = length(int_group_rs)
    subpath.integration_scheme_index = i
    return false 
  end

  v_start = start_point(subpath)
  v_end = end_point(subpath)

  #these values are the 't values' of the discriminant points 
  rs = [(2 * alpha - (v_start + v_end))/(v_end - v_start) for alpha in internal_discriminant_points(RS)]

  for g in dif_basis
    interval = [-1]
    current_endpoint = 1
    gmin = minpoly(g)
    while (interval[end] != 1)
      mid = (1//2) * (interval[end] + current_endpoint)
      if minimum([abs(alpha - mid) for alpha in rs]) > (1//2) * abs(current_endpoint - interval[end])
        push!(interval, current_endpoint)
        current_endpoint = 1
      else 
        current_endpoint = (1//2) * (current_endpoint + interval[end])
      end
    end
    M_tilde_values = []

    for j in (2:length(interval))
      z_0 = (interval[j] + interval[j-1])/2
      delta = minimum([abs(alpha - z_0) for alpha in rs]) + (abs(interval[j] - interval[j-1]))/2 
      lis = [denominator(coeff(gmin, i)) for i in (0:degree(gmin))]
      gmin = lcm(lis) * gmin
      CC = complex_field(RS)
      v = embedding(RS)
      _, CCx = polynomial_ring(CC, "x")
      coeffs = [numerator(coeff(gmin_int,i)) for i in (0:degree(gmin_int))]
      #precompose with the path
      #the coefficients in the minimal polynomial of g are rational functions from the path P to CC.
      #The paper [BDG24] requires this equation to hold on [-1,1]. The straight path P is encoded as a fucntion [-1,1] -> P 
      #so in order to get an equation on [-1,1] we precompose the coefficients with the formula for the straight path. 
      if base_ring(base_ring(parent(gmin_int))) == QQ
        coeffs = [sum(CC(coeff(a,i)) * ( (CCx+1)*v_end/2 + (1-CCx)*v_start/2 )^i for i in (0:length(coefficients(a)))) for a in coeffs]
      else 
        coeffs = [sum(CC(embeddings(v)[1](coeff(a,i))) * ( (CCx+1)*v_end/2 + (1-CCx)*v_start/2 )^i for i in (0:length(coefficients(a)))) for a in coeffs]
      end 

      A_0 = CC(abs((coeff(coeffs[end], degree(coeffs[end]))) ) * prod( [abs(z_0 - alpha) - delta for alpha in rs] , init = one(CC)))
      A_i = [ (sum([CC(abs(coeff(a, i)) * (abs(z_0) + delta)^i) for i in (0:length(coefficients(a)))], init = zero(CC))) for a in coeffs[1:end - 1] ]

      M_tilde = 2 * maximum([ real((A_i[i]/A_0)^(1/i)) for i in (1:length(A_i)) ])

      push!(M_tilde_values, M_tilde)
    end
    push!(subpath.bounds, maximum(M_tilde_values))
  end
end 

