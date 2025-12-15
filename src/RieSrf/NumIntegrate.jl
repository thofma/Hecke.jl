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

export IntegrationScheme

export gauss_legendre_integration_points, gauss_chebyshev_integration_points, tanh_sinh_quadrature_integration_points, gauss_legendre_path_parameters

  # An integration scheme
  # consists of a list of abscissae, weights and a bunch of parameters. 
  # Every path we integrate over gets assigned one of these integrations 
  # schemes. Currently all integration schemes are Gauss-Legendre integration
  # schemes. If we alow for different types of integration later on, we can
  # extend this struct to also include those.
mutable struct IntegrationScheme

  abscissae::Vector{ArbFieldElem}
  weights::Vector{ArbFieldElem}
  
 # r has strong influence on the size of N while the contribution of M is 
 # merely logarithmic. So, in order to minimize N the priority is to
 # maximize r such that M is still decent. 

  int_param_r::ArbFieldElem
  int_param_N::Int
  bounds::Vector{ArbFieldElem}
  prec::Int

  
  #Compute a Gauss-Legendre integration scheme
  function IntegrationScheme(r, prec, error, bound)
  
    integration_scheme = new()
    N = gauss_legendre_parameters(r, error, bound)
    integration_scheme.int_param_N = N
    abscissae, weights = gauss_legendre_integration_points(N, prec)
    integration_scheme.abscissae = abscissae
    integration_scheme.weights = weights
    integration_scheme.int_param_r = r
    integration_scheme.bounds = [bound]
    integration_scheme.prec = prec
    return integration_scheme 
  end

end

################################################################################
#
#  Gauss-Legendre
#
################################################################################

#Use arb to compute the abscissae and the weights.(Cf. Neurohr's thesis 3.2.2)
function gauss_legendre_integration_points(N::T, prec::Int = 100) where T <: IntegerUnion
  
  Rc = ArbField(prec)

  N = Int(N)
  m = floor(Int, (N +1)//2)
  
  ab = zeros(Rc, m)
  w = zeros(Rc, m)
  
  for l in (0:m-1)
    ccall((:arb_hypgeom_legendre_p_ui_root, libflint), Nothing, (Ref{ArbFieldElem}, Ref{ArbFieldElem}, UInt, UInt, Int), ab[l+1], w[l+1], N, l, prec)
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

function gauss_legendre_parameters(r, error, bound = 10^5)

  N = ceil(Int, (log(64*(bound/15))-log(error)-log(1-exp(acosh(r))^(-2)))/(2*acosh(r)));
  return N
end

# Compute the parameters for the integration scheme for every path
# based on the error bound we allow.
function gauss_legendre_path_parameters(points, path::CPath, err)

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
function split_line_segment(points, path::CPath, err)
  if !isdefined(path, :int_param_r)
    set_int_param_r(path, gauss_legendre_line_parameters(points, path))
  end 
  
  paths = [path]
  prec = precision(parent(points[1]))
  Rc = ArbField(prec)

  if get_int_param_r(path) < 1.2
    t = get_t_of_closest_d_point(path)
    if abs(real(t)) < (3/4) 
      x = evaluate(path, t)
    else
      x = evaluate(path,Rc(sign(Int, real(t))*3/4))
    end
    gam1 = c_line(start_point(path), x)
    gam2 = c_line(x, end_point(path))
    
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
  Cc = parent(points[1])
  Rr = ArbField(precision(Cc))
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
  
  #Not sure why yet
  if r_0 == Rr(5.0)
    push!(path.bounds, Rr(1))
  end

  return r_0
  
end

# Compute the parameter r0 for the given arc. 
function gauss_legendre_arc_parameters(points::Vector{AcbFieldElem}, path::CPath)
  Cc = parent(points[1])
  Rr = ArbField(precision(Cc))
  r_0 = Rr(5.0)
  
  Rpi = Rr(pi)
  I = onei(Cc)
  
  a = start_arc(path)
  b = end_arc(path)
  c = center(path)
  r = radius(path)
  or = orientation(path)
  
  for p in points
    r_p = r_0
    if p != c
      prec = precision(Cc)
      zero_sens = floor(Int, prec*log(2)/log(10)) - 5
      #We find t_p such that path(t_p) = p 
      #trim_zero is used to avoid errors in taking log. (It's ambiguous if either
      #the real or the imaginary part is close to zero. The ambiguity disappears
      # when taking absolute values during the computation of r_p)
      #t_p = or/(b - a) * (-2 * I * log(trim_zero((p - c)/(r * exp(I*(b + a)/2)), zero_sens)))
      t_p = or/(b - a) * (-2 * I * (log((p - c)/r) - I*(b + a)/2))

      r_p = Rr((abs(t_p + 1) + abs(t_p - 1))/2)
    end
   
    
    @req r_p > 1 "Error in computation of r_p"
    if r_p < r_0
      r_0 = r_p
      set_t_of_closest_d_point(path, t_p)
    end
  end
  
  #Not sure why yet
  if r_0 == Rr(5.0)
    push!(path.bounds, Rr(1))
  end

  return r_0
  
end

# Compute the parameter r0 for the given circle.
function gauss_legendre_circle_parameters(points::Vector{AcbFieldElem}, path::CPath)
  Cc = parent(points[1])
  Rr = ArbField(precision(Cc))
  r_0 = Rr(5.0)
  
  Rpi = Rr(pi)
  I = onei(Cc)
  
  a = start_arc(path)
  b = end_arc(path)
  c = center(path)
  r = radius(path)
  or = orientation(path)
  for p in points
    r_p = r_0
    if p != c
      #We find t_p such that path(t_p) = p 
      #trim_zero is used to avoid errors in taking log. (It's ambiguous if either
      #the real or the imaginary part is close to zero. The ambiguity disappears
      # when taking absolute values during the computation of r_p)
      prec = precision(Cc)
      zero_sens = floor(Int, prec*log(2)/log(10)) - 5

      #t_p = -or/Rpi * I * log(trim_zero((c - p) /(r* exp(I * a)), zero_sens));
      t_p = -or/Rpi * I * (log((c - p) /r) - I * a)

      r_p = Rr((abs(t_p + 1) + abs(t_p - 1))/2)
    end
    
    @req r_p > 1 "Error in computation of r_p"
    if r_p < r_0
      r_0 = r_p
      set_t_of_closest_d_point(path, t_p)
    end
  end
  
  #Not sure why yet
  if r_0 == Rr(5.0)
    push!(path.bounds, Rr(1))
  end

  return r_0
  
end

# Compute the abscissae and the weights for Gauss-Chebyshev integration.
# I don't think this is used anywhere right now.
function gauss_chebyshev_integration_points(N::T, prec::Int = 100) where T <: IntegerUnion
  Rc = ArbField(prec)
  pi_N12 = const_pi(Rc)//(2*N)
  
  m = floor(Int, N//2)
  
  ab = zeros(Rc, m)
  w = zeros(Rc, m)
  
  for l in (1:m)
    ab[l] = cos(pi_N12 * (2*l - 1))
  end
  
  isodd(N) ? abscissae = vcat(-ab, [zero(Rc)], reverse(ab)) : abscissae = vcat(-ab, reverse(ab))
  return abscissae, fill(const_pi(Rc)//(N), N)  
end

# Compute the abscissae and the weights for the tanh_sinh quadrature
# I don't think this is used anywhere right now.
function tanh_sinh_quadrature_integration_points(N::T, h::ArbFieldElem, lambda::ArbFieldElem = const_pi(parent(h))//2) where T <: IntegerUnion
  Rc = parent(h)
  N = Int(N)

  abscissae = zeros(Rc, N)
  weights = zeros(Rc, N)
  
  lamh = lambda * h
  
  for l in (1:N)
    lh = l*h
    lamsin_lh = lambda*sinh(lh)
    
    abscissae[l] = tanh(lamsin_lh)
    weights[l] = lamh * cosh(lh)//(cosh(lamsin_lh))^2 
  end
  
  abscissae = vcat(-reverse(abscissae), [zero(Rc)], abscissae)
  weights = vcat(reverse(weights), [lamh], weights)
  
  return abscissae, weights
end

