################################################################################
#
#  RieSrf/Periods/Quadrature/DoubleExponential.jl : double exponential quadrature
#
#  Paths that pass close to a discriminant point (Gauss-Legendre parameter
#  r < 1.03) are integrated with the tanh-sinh (double exponential)
#  quadrature (Neurohr, Section 3.3). Its parameter r is the half width of the
#  strip |Im z| < r whose image under t = tanh(lambda sinh(z)) (the "burger")
#  contains no discriminant point.
#
#  Entry points: _double_exponential_path_parameters!,
#  _double_exponential_parameters, _tanh_sinh_nodes.
#
################################################################################

@doc raw"""
    _tanh_sinh_nodes(N::IntegerUnion, h::ArbFieldElem, lambda::ArbFieldElem = const_pi(parent(h))/2)
      -> Vector{ArbFieldElem}, Vector{ArbFieldElem}

The 2N + 1 abscissae and weights of the tanh-sinh quadrature with step size h.
"""
function _tanh_sinh_nodes(N::IntegerUnion, h::ArbFieldElem,
                          lambda::ArbFieldElem = const_pi(parent(h))/2)
  RR = parent(h)
  N = Int(N)
  # The step size is a free parameter: any h slightly off the computed value
  # works as well. h inherits the radius of the (low precision) integrand
  # bounds, which would otherwise spread into every node and weight (at
  # prec 231 the nodes had only ~124 bits). Use the exact midpoint.
  h = Nemo.midpoint(h)
  abscissae = zeros_array(RR, N)
  weights = zeros_array(RR, N)
  lambda_h = lambda * h
  for l in 1:N
    lh = l*h
    lambda_sinh = lambda*sinh(lh)
    abscissae[l] = tanh(lambda_sinh)
    weights[l] = lambda_h * cosh(lh)//(cosh(lambda_sinh))^2
  end
  abscissae = vcat(-reverse(abscissae), [zero(RR)], abscissae)
  weights = vcat(reverse(weights), [lambda_h], weights)
  return abscissae, weights
end

# The number of nodes N (2N + 1 in total) and the step size h of the
# tanh-sinh quadrature for an error 2^-prec, for the strip parameter r and the
# integrand bounds `bounds` (Neurohr, Section 3.3).
function _double_exponential_parameters(r::ArbFieldElem, prec::Int,
                                        bounds::Vector{ArbFieldElem} = [parent(r)(10)^5, parent(r)(10)^5],
                                        lambda::ArbFieldElem = const_pi(parent(r))/2)
  RR = parent(r)
  D = prec * log(RR(2))
  M_1 = RR(bounds[1])
  M_2 = RR(bounds[2])
  X_r = cos(r) * sqrt(const_pi(RR)/(2*lambda*sin(r)) - 1)
  B_r = (2/cos(r)) * ((X_r/2) * (1/((cos(lambda*sin(r)))^2) + 1/(X_r^2)) + 1/(2*sinh(X_r)^2))
  h = (2 * const_pi(RR) * r) / (D + log(2 * M_2 * B_r + exp(-D)))
  N = ceil(ZZRingElem, asinh((D + log(8*M_1))/(2*lambda)) / h)
  return N, h
end

# |Im z| for the point z of the strip with tanh(lambda sinh(z)) = t.
_burger_parameter(t, lambda) = abs(imag(asinh(atanh(t)/lambda)))

# The strip parameter r_0 of a path: the largest r <= 5 such that no point
# lies inside the image of the burger under the path. The parameter t of the
# closest point is stored in the path (the integrand bound is sampled near it).
function _double_exponential_line_parameter!(points::Vector{AcbFieldElem}, path::CPath,
                                             lambda = const_pi(ArbField(precision(parent(path.start_point))))/2)
  RR = ArbField(precision(parent(path.start_point)))
  r_0 = RR(5)
  a = start_point(path)
  b = end_point(path)
  for p in points
    t_p = trim_zero((2*p - a - b)//(b - a))   # path(t_p) = p
    r_p = _burger_parameter(t_p, lambda)
    if r_p < r_0
      r_0 = r_p
      set_closest_disc_point_parameter!(path, t_p)
    end
  end
  return r_0
end

# The same for arcs and circles. In addition r_0 is decreased in steps of 1/20
# until |(b - a) Im(phi(-i r_0))| < 2 pi (arcs from angle a to b) or
# |Im(phi(-i r_0))| < 1 (circles), phi(z) = tanh(lambda sinh(z)) (as in
# Neurohr's implementation).
function _double_exponential_arc_circle_parameter!(points::Vector{AcbFieldElem}, path::CPath,
                                                   lambda = const_pi(ArbField(precision(parent(path.start_point))))/2)
  CC = parent(points[1])
  RR = ArbField(precision(CC))
  I = onei(CC)
  r_0 = RR(5)
  c = center(path)
  parameter = _arc_parameter_function(path, CC)
  for p in points
    contains(c - p, zero(CC)) && continue
    t_p = parameter(p)
    r_p = _burger_parameter(t_p, lambda)
    if r_p < r_0
      r_0 = r_p
      set_closest_disc_point_parameter!(path, t_p)
    end
  end
  if is_circle(path)
    while abs(imag(tanh(lambda*sinh(-I*r_0)))) >= RR(1)
      r_0 -= RR(1/20)
    end
  else
    angle_range = end_angle(path) - start_angle(path)
    while abs(angle_range*imag(tanh(lambda*sinh(-I*r_0)))) >= 2*const_pi(RR)
      r_0 -= RR(1/20)
    end
  end
  return r_0
end

# The strip parameter of a path (no splitting).
function _double_exponential_path_parameters!(points::Vector{AcbFieldElem}, path::CPath)
  if is_line(path)
    set_quadrature_parameter!(path, _double_exponential_line_parameter!(points, path))
    set_subpaths!(path, [path])
  elseif is_arc(path) || is_circle(path)
    set_quadrature_parameter!(path, _double_exponential_arc_circle_parameter!(points, path))
    set_subpaths!(path, [path])
  end
end
