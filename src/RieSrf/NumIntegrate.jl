################################################################################
#
#          RieSrf/NumIntegrate.jl : Numerical integration
#
# (C) 2022 Jeroen Hanselman
#
################################################################################

export gauss_legendre_integration_points, gauss_chebyshev_integration_points, tanh_sinh_quadrature_integration_points

################################################################################
#
#  Gauss-Legendre
#
################################################################################

function gauss_legendre_integration_points(N::T, prec::Int = 100) where T <: IntegerUnion
  
  Rc = ArbField(prec)

  N = Int(N)
  m = floor(Int, (N +1)//2)
  
  ab = zeros(Rc, m)
  w = zeros(Rc, m)
  
  for l in (0:m-1)
    ccall((:arb_hypgeom_legendre_p_ui_root, libarb), Nothing, (Ref{arb}, Ref{arb}, UInt, UInt, Int), ab[l+1], w[l+1], N, l, prec)
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

function gauss_legendre_parameters(r, err, Bound = 10^5)

  R = ArbField(10);
  N = ceil((log(64*R(Bound/15))-log(R(err))-log(1-exp(acosh(r))^(-2)))/acosh(r))-1;
  return N
end

function gauss_legendre_path_parameters(points, gamma::CPath, err)

  if path_type(gamma) == 0
    split_line_segment(points, gamma, err)
  elseif path_type(gamma) == 1
    gauss_legendre_arc_parameters(points, gamma)
  elseif path_type(gamma) == 2
    gauss_legendre_arc_parameters(points, gamma)
    #point?
  end
end

function split_line_segment(points, gamma::CPath, err)
  if !isdefined(gamma, :int_par_r)
    gauss_legendre_line_parameters(points, gamma)
  end 
  
  paths = [gamma]
  
  if get_int_param_r(gamma) < Rc(1.2)
    t = get_t_of_closest_d_point(gamma)
    if abs(real(t)) < (3/4) 
      x = evaluate(gamma, t)
    else
      x = evaluate(gamma(sign(real(t))*3/4))
    end
    gam1 = c_line(start_point(gamma), x)
    gam2 = c_line(x, end_point(gamma))
    
    set_int_param_r(gam1, gauss_legendre_line_parameters(points, gam1))
    set_int_param_r(gam2, gauss_legendre_line_parameters(points, gam2))
    
    N = gauss_legendre_parameters(get_int_param_r(gamma), err)
    N1 = gauss_legendre_parameters(get_int_param_r(gam1), err)
    N2 = gauss_legendre_parameters(get_int_param_r(gam2), err)
    
    
    set_int_params_N(gamma, N)
    set_int_params_N(gam1, N1)
    set_int_params_N(gam2, N2)
    
    if N - N1 - N2 >= 10
      paths = hcat(split_line_segment(points, gam1, err), split_line_segment(points, gam2, err))
    end
  end
  return paths
end

function gauss_legendre_line_parameters(points::Vector{acb}, gamma::CPath)
  Cc = parent(points[1])
  Rr = ArbField(precision(Cc))
  r_0 = Rr(5.0)
  
  a = start_point(gamma)
  b = end_point(gamma)
  
  for p in points
    #We find t_p such that gamma(t_p) = p , i.e. (a + b)/2 + (b - a)/2 * t_p = p
    t_p = (2*p - a - b)//(b - a)
    
    #Consider ellipse E = {z in C : |z-1| + |z+1| = 2cosh(r)}
    #Now picking r_k to be the following, we ensure that t_p lies on the boundary
    #and not on the ellipse if radius < r_k  
    r_p = (abs(t_p + 1) + abs(t_p - 1))//2
    
    @req r_p > 1 "Error in computation of r_k"
    if r_p < r_0
      r_0 = r_p
      set_t_of_closest_d_point(gamma, t_p)
    end
  end
  
  #Not sure why yet
  if r_0 == Rr(5.0)
    push!(bounds(gamma), 1)
  end

  return r_0
  
end

function gauss_legendre_arc_parameters(points::Vector{acb}, gamma::CPath)
  Cc = parent(points[1])
  Rr = ArbField(precision(Cc))
  r_0 = Rr(5.0)
  
  Rpi = pi(Rr)
  I = onei(Cc)
  
  a = start_arc(gamma)
  b = end_arc(gamma)
  c = center(gamma)
  r = radius(gamma)
  or = orientation(gamma)
  
  for p in points
    if p != c
      #We find t_p such that gamma(t_p) = p 
      t_p = or/(b - a) * (-2 * I * log((p - c)/(r * exp(I*(b + a)/2))));
      
      r_p = abs(im(2 * asinh(atanh(u_k)/(Rpi))))
    end
   
    
    @req r_p > 1 "Error in computation of r_k"
    if r_p < r_0
      r_0 = r_p
      set_t_of_closest_d_point(gamma, t_p)
    end
  end
  
  #Not sure why yet
  if r_0 == Rr(5.0)
    push!(bounds(gamma), 1)
  end

  return r_0
  
end

function gauss_legendre_circle_parameters(points::Vector{acb}, gamma::CPath)
  Cc = parent(points[1])
  Rr = ArbField(precision(Cc))
  r_0 = Rr(5.0)
  
  Rpi = pi(Rr)
  I = onei(Cc)
  
  a = start_arc(gamma)
  b = end_arc(gamma)
  c = center(gamma)
  r = radius(gamma)
  or = orientation(gamma)
  
  for p in points
    if p != c
      #We find t_p such that gamma(t_p) = p 
      t_p = or/Rpi * I * log((c - p) /(r* exp(I * a)));
      
      r_p = abs(im(2 * asinh(atanh(u_k)/(Rpi))))
    end
   
    
    @req r_p > 1 "Error in computation of r_k"
    if r_p < r_0
      r_0 = r_p
      set_t_of_closest_d_point(gamma, t_p)
    end
  end
  
  #Not sure why yet
  if r_0 == Rr(5.0)
    push!(bounds(gamma), 1)
  end

  return r_0
  
end


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

function tanh_sinh_quadrature_integration_points(N::T, h::arb, lambda::arb = const_pi(parent(h))//2) where T <: IntegerUnion
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

