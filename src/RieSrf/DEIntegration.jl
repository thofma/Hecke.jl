@doc raw"""
 tanh_sinh_quadrature_integration_points(N::T, h::ArbFieldElem, 
 lambda::ArbFieldElem = const_pi(parent(h))/2) where T <: IntegerUnion

Compute abscissae and weights according to the tanh-sinh_quadrature
integration scheme. 
"""
function tanh_sinh_quadrature_integration_points(N::T, h::ArbFieldElem, lambda::ArbFieldElem = const_pi(parent(h))/2) where T <: IntegerUnion
  Rc = parent(h)
  N = Int(N)

  abscissae = zeros_array(Rc, N)
  weights = zeros_array(Rc, N)

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



function double_exponential_integration_parameters( r::ArbFieldElem, prec::Int,  bounds::Vector{ArbFieldElem} = [parent(r)(10)^5, parent(r)(10)^5], lambda::ArbFieldElem = const_pi(parent(r))/2 )
#Computes integration parameters for double exponential integration
  RR = parent(r)
  D = prec * log(RR(2))

  M_1 = RR(bounds[1])
  M_2 = RR(bounds[2])


  X_r = cos(r) * sqrt( const_pi(RR)/(2*lambda*sin(r)) - 1 )

  B_r = (2/cos(r)) * ( (X_r/2) * (1/((cos(lambda*sin(r)))^2) + 1/(X_r^2)) + 1/(2*sinh(X_r)^2) )

  h = (2 * const_pi(RR) * r ) / ( D + log( 2 * M_2 * B_r + exp(-D) ))

  N = ceil(ZZRingElem, asinh((D+ log(8*M_1))/(2*lambda)) / h )
  return N, h
end

mutable struct IntegrationSchemeDE

  abscissae::Vector{ArbFieldElem}
  weights::Vector{ArbFieldElem}

  int_param_r::ArbFieldElem
  int_param_N::Int
  bounds::Vector{ArbFieldElem}
  prec::Int


  #Compute a Gauss-Legendre integration scheme
  function IntegrationSchemeDE(r::ArbFieldElem, prec::Int, bounds::Vector{ArbFieldElem})
    RR = parent(r)
    integration_scheme = new()
    integration_scheme.prec = prec
    @req r < const_pi(RR)/2 "Error in IntegrationSchemeDE"
    @req r > RR(0) "Error in IntegrationSchemeDE"

    N, h = double_exponential_integration_parameters(r, prec, bounds)
    abscissae, weights = tanh_sinh_quadrature_integration_points(N, h)
    integration_scheme.abscissae = abscissae
    integration_scheme.weights = weights
    integration_scheme.int_param_r = r
    integration_scheme.bounds = bounds
    integration_scheme.int_param_N = 2*N + 1
    return integration_scheme
  end
end


function double_exponential_line_parameters(points::Vector{AcbFieldElem}, path::CPath, lambda = const_pi(ArbField(precision(parent(path.start_point))))/2 )
  RR = ArbField(precision(parent(path.start_point)))
  r_0 = RR(5.0)

  a = start_point(path)
  b = end_point(path)

  for p in points
    t_p = (2*p - a - b)//(b - a)

    #Consider the burger shaped area: B = {tanh(lambda*sinh(z)) : |imag(z)| < r}
    #Now picking r_k to be the following, we ensure that t_p lies on the boundary
    #and not on the burger.
    r_p = abs(imag(asinh(atanh(t_p)/lambda)))
    if r_p < r_0
      r_0 = r_p
      set_t_of_closest_d_point(path, t_p)
    end
  end
  return r_0
end

function double_exponential_arc_parameters(points::Vector{AcbFieldElem}, path::CPath, lambda = const_pi(ArbField(precision(parent(path.start_point))))/2)
  CC = parent(points[1])
  RR = ArbField(precision(CC))
  r_0 = RR(5.0)

  Rpi = RR(pi)
  I = onei(CC)

  a = start_arc(path)
  b = end_arc(path)
  c = center(path)
  r = radius(path)
  or = orientation(path)

  for p in points
    if !contains(c - p, zero(CC))
      prec = precision(CC)
      #We find t_p such that path(t_p) = p
      #trim_zero is used to avoid errors in taking log. (It's ambiguous if either
      #the real or the imaginary part is close to zero. The ambiguity disappears
      # when taking absolute values during the computation of r_p)
      t_p = or/(b - a) * (-2 * I * log(trim_zero((p - c)/(r * exp(I*(b + a)/2)))))
      @req contains(evaluate(path, t_p),p) "Error"
      
      r_p = abs(imag(asinh(atanh(t_p)/lambda)))
      if r_p < r_0 
        r_0 = r_p
        set_t_of_closest_d_point(path, t_p)
      end
    end
  end

  while abs((b-a)*imag(tanh(lambda*sinh(-I*r_0)))) >= 2*Rpi
    r_0 -= RR(1/20)
  end
  return r_0
end

function double_exponential_circle_parameters(points::Vector{AcbFieldElem}, path::CPath, lambda = const_pi(ArbField(precision(parent(path.start_point))))/2)
  CC = parent(points[1])
  RR = ArbField(precision(CC))
  r_0 = RR(5.0)

  Rpi = RR(pi)
  I = onei(CC)

  a = start_arc(path)
  b = end_arc(path)
  c = center(path)
  r = radius(path)
  or = orientation(path)

  for p in points
    if !contains(c - p, zero(CC))
      #We find t_p such that path(t_p) = p
      #trim_zero is used to avoid errors in taking log. (It's ambiguous if either
      #the real or the imaginary part is close to zero. The ambiguity disappears
      # when taking absolute values during the computation of r_p)

      t_p = -or/Rpi * I * log(trim_zero((c - p) /(r* exp(I * a))))

      @req contains(evaluate(path, t_p) - p, CC(0)) "Error"
      r_p = abs(imag(asinh(atanh(t_p)/lambda)))
      if r_p < r_0 
        r_0 = r_p
        set_t_of_closest_d_point(path, t_p)
      end
    end
  end
  while abs(imag(tanh(lambda*sinh(-I*r_0)))) >= RR(1) 
    r_0 -= RR(1/20)
  end
  return r_0
end

# Compute the parameters for the integration scheme for every path
# based on the error bound we allow.
function double_exponential_path_parameters(points::Vector{AcbFieldElem}, path::CPath)
  if path_type(path) == 0
    set_int_param_r(path, double_exponential_line_parameters(points, path))
    set_subpaths(path, [path])
  elseif path_type(path) == 1
    set_int_param_r(path, double_exponential_arc_parameters(points, path))
    set_subpaths(path, [path])
  elseif path_type(path) == 2
    set_int_param_r(path, double_exponential_circle_parameters(points, path))
    set_subpaths(path, [path])
  end
end