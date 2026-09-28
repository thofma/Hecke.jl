################################################################################
#
#          RieSrf/NumIntegrate.jl : Numerical integration
#
# (C) 2025 Jeroen Hanselman
# This is a port of the Riemann surfaces package written by
# Christian Neurohr. It is based on his Phd thesis
# https://www.researchgate.net/publication/329100697_Efficient_integration_on_Riemann_surfaces_applications
# Neurohr's package can be found on https://github.com/christianneurohr/RiemannSurfaces
#
################################################################################

export IntegrationSchemeGL

export gauss_legendre_integration_points, gauss_chebyshev_integration_points, tanh_sinh_quadrature_integration_points,
 gauss_legendre_path_parameters

################################################################################
#
#  Gauss-Legendre
#
################################################################################

#Use arb to compute the abscissae and the weights.(Cf. Neurohr's thesis 3.2.2)
@doc raw"""
gauss_legendre_integration_points(N::T, prec::Int = 100) where T <: IntegerUnion

Compute abscissae and weights according to the Gauss-Legendre integration
scheme.
"""
function gauss_legendre_integration_points(N::T, 
  prec::Int = 100) where T <: IntegerUnion

  Rc = ArbField(prec)

  N = Int(N)
  m = floor(Int, (N +1)//2)

  ab = zeros_array(Rc, m)
  w = zeros_array(Rc, m)

  Threads.@threads for l in 0:m-1
    ccall((:arb_hypgeom_legendre_p_ui_root, libflint), Nothing,
          (Ref{ArbFieldElem}, Ref{ArbFieldElem}, UInt, UInt, Int), ab[l+1], w[l+1], N, l, prec)
  end

  if isodd(N)
    abscissae = vcat(-ab, reverse(ab[1:m-1]))
    weights = vcat(w, reverse(w[1:m-1]))
  else
    abscissae = vcat(-ab, reverse(ab))
    weights = vcat(w, reverse(w))
  end
  return abscissae, weights
end

function gauss_legendre_parameters(r::ArbFieldElem, error::ArbFieldElem, bound::ArbFieldElem = parent(r)(10^5))
  @req isfinite(bound) "The bound for the integrand is not finite."
  @req r > 1 "The ellipse parameter r must be larger than 1 (got $r)."

  N = Hecke.upper_bound(ZZRingElem, (log(64*(bound/15))-log(error)-
    log(1-exp(acosh(r))^(-2)))/(2*acosh(r)));
  return N
end

# Compute the parameters for the integration scheme for every path
# based on the error bound we allow.
function gauss_legendre_path_parameters(points::Vector{AcbFieldElem}, path::CPath, err::ArbFieldElem)

  if path_type(path) == 0
    set_subpaths(path, split_line_segment(points, path, err))
  elseif path_type(path) == 1
    set_int_param_r(path, gauss_legendre_arc_parameters(points, path))
    set_subpaths(path, [path])
  elseif path_type(path) == 2
    set_int_param_r(path, gauss_legendre_circle_parameters(points, path))
    set_subpaths(path, [path])
    #point?
  end
end

# Check if it is more efficient to split a line into two segments.
# (Cf. Neurohr 4.7.5)
function split_line_segment(points::Vector{AcbFieldElem}, path::CPath, err::ArbFieldElem)
  if !isdefined(path, :int_param_r)
    set_int_param_r(path, gauss_legendre_line_parameters(points, path))
  end

  paths = [path]
  prec = precision(parent(points[1]))
  Rc = ArbField(prec)
  CC = AcbField(prec)

  if get_int_param_r(path) < 1.2
    t = get_t_of_closest_d_point(path)
    if abs(real(t)) < (3/4)
      x = evaluate(path, real(t))
    else
      x = evaluate(path,Rc(sign(Int, real(t))*3/4))
    end
  
    gam1 = c_line(start_point(path), x, CC)
    gam2 = c_line(x, end_point(path), CC)

    set_int_param_r(gam1, gauss_legendre_line_parameters(points, gam1))
    set_int_param_r(gam2, gauss_legendre_line_parameters(points, gam2))

    N = gauss_legendre_parameters(get_int_param_r(path), err)
    N1 = gauss_legendre_parameters(get_int_param_r(gam1), err)
    N2 = gauss_legendre_parameters(get_int_param_r(gam2), err)

    set_int_params_N(path, N)
    set_int_params_N(gam1, N1)
    set_int_params_N(gam2, N2)

    if N - N1 - N2 >= 10
      paths = vcat(split_line_segment(points, gam1, err), split_line_segment(points, gam2, err))
    end
  end
  return paths
end

# The following functions have the same purpose.
# Given a set of points P. we compute the parameter r0 for the given path gamma.
# The parameter r_0 is the biggest radius smaller than 5 such that
# none of the points in P are in the interior of gamma(E_r0).
# Here, E_r0 = {z in C : |z-1| + |z+1| = 2cosh(r0)}. The path we integrate over
# corresponds to the interval [-1, 1] in E_r0). Usually P will
# consist of the ramification points and the singular points.

function gauss_legendre_line_parameters(points::Vector{AcbFieldElem}, path::CPath)
  CC = parent(points[1])
  Rr = ArbField(precision(CC))
  r_0 = Rr(5.0)

  a = start_point(path)
  b = end_point(path)

  for p in points
    #We find t_p such that path(t_p) = p , i.e. (a + b)/2 + (b - a)/2 * t_p = p
    t_p = (2*p - a - b)//(b - a)

    #Consider ellipse E = {z in C : |z-1| + |z+1| = 2cosh(r)}
    #Now picking r_k to be the following, we ensure that t_p lies on the boundary
    #and not on the ellipse if radius < r_k
    r_p = (abs(t_p + 1) + abs(t_p - 1))//2
    @req r_p > 1 "Error in computation of r_p"
    if r_p < r_0
      r_0 = r_p
      #The t_p is stored with the path
      set_t_of_closest_d_point(path, t_p)
    end
  end

  if r_0 == Rr(5.0)
    push!(path.bounds, Rr(1))
  end

  return r_0

end

# Compute the parameter r0 for the given arc or circle.
#
# t_p with path(t_p) = p needs a log per point. The points are the
# discriminant points (their precision is high, e.g. 600 bits), but r0 and
# t_p are only used to choose the quadrature and to place the sample points
# of the heuristic bounds, so they are computed at _arc_parameter_precision()
# bits; only if r_p cannot be separated from 1 there (a point extremely close
# to the path) is that point done again at full precision.
# (For f19 at 200 bits this took 20% of the attributed time, mostly log/exp
# at the precision of the discriminant points.)
_arc_parameter_precision() = 128

function _arc_circle_parameters(points::Vector{AcbFieldElem}, path::CPath, is_circle::Bool)
  CC = parent(points[1])
  Rr = ArbField(precision(CC))
  r_0 = Rr(5.0)
  c = center(path)

  # t_p = scale * log(trim_zero(w)) with w = (p - c)/E (arc) or (c - p)/E (circle)
  function setup(prec::Int)
    CL = AcbField(prec)
    RL = ArbField(prec)
    I = onei(CL)
    a = RL(start_arc(path)); b = RL(end_arc(path))
    cL = CL(c); rL = RL(radius(path)); or = orientation(path)
    if is_circle
      return CL, cL, rL * exp(I * a), -or / const_pi(RL) * I
    else
      return CL, cL, rL * exp(I * (b + a) / 2), or / (b - a) * (-2 * I)
    end
  end
  function t_and_r(p, S)
    CL, cL, E, scale = S
    w = is_circle ? (cL - CL(p)) / E : (CL(p) - cL) / E
    t = scale * log(trim_zero(w))
    return t, (abs(t + 1) + abs(t - 1)) / 2
  end

  lo = min(precision(CC), _arc_parameter_precision())
  S_lo = setup(lo)
  S_hi = nothing
  for p in points
    contains(c - p, zero(CC)) && continue
    t_p, r_p = t_and_r(p, S_lo)
    if !(r_p > 1) && lo < precision(CC)
      S_hi === nothing && (S_hi = setup(precision(CC)))
      t_p, r_p = t_and_r(p, S_hi)
    end
    @req r_p > 1 "Error in computation of r_p"
    if r_p < r_0
      r_0 = Rr(r_p)
      set_t_of_closest_d_point(path, CC(t_p))
    end
  end

  #Not sure why yet
  if r_0 == Rr(5.0)
    push!(path.bounds, Rr(1))
  end

  return r_0
end

gauss_legendre_arc_parameters(points::Vector{AcbFieldElem}, path::CPath) =
  _arc_circle_parameters(points, path, false)

gauss_legendre_circle_parameters(points::Vector{AcbFieldElem}, path::CPath) =
  _arc_circle_parameters(points, path, true)


# Compute the abscissae and the weights for Gauss-Chebyshev integration.
# I don't think this is used anywhere right now.
function gauss_chebyshev_integration_points(N::T, prec::Int = 100) where T <: IntegerUnion
  Rc = ArbField(prec)
  pi_N12 = const_pi(Rc)//(2*N)

  m = floor(Int, N//2)

  ab = zeros_array(Rc, m)
  w = zeros_array(Rc, m)

  for l in (1:m)
    ab[l] = cos(pi_N12 * (2*l - 1))
  end

  isodd(N) ? abscissae = vcat(-ab, [zero(Rc)], reverse(ab)) : abscissae = vcat(-ab, reverse(ab))
  return abscissae, fill(const_pi(Rc)//(N), N)
end
