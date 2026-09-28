################################################################################
#
#  RieSrf/Quadrature/Bounds.jl : bounds for the integrand on the ellipses
#
################################################################################

###  The following function compute_ellipse_bound_rigorous, together with the function construct_M,
###  are an implementation of the algorithm for rigorous integration along straight lines by Nils Bruin, Linden
###  Disney-Hogg, and Wuqian Effie Gao, as presented in https://arxiv.org/pdf/2208.12377. The implementation 
###  here is Strategy 1 from this paper.
function compute_ellipse_bound_rigorous(subpath, dif_basis, int_group_rs, RS)
  if length(subpath.bounds) == 0
    i = maximum(filter(x -> (subpath.int_param_r > int_group_rs[x]), 1:length(int_group_rs));init = 1)
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

# Heuristic bound 10 * max |integrand| at the point subpath(t). If the balls
# are not finite at the working precision (cancellation, e.g. for discriminant
# points of very different sizes), the fiber and the differentials are
# evaluated again at a higher precision (only a few correct bits are needed).
function _integrand_bound(RS::RiemannSurfaceModel, subpath::CPath, differentials,
                          t, prec::Int)
  RR = ArbField(prec)
  x_ball = evaluate(subpath, t)
  dx = evaluate_d(subpath, t)
  p = prec
  while true
    f = embed_mpoly(defining_polynomial(RS), embedding(RS), p)
    Ky, y = polynomial_ring(base_ring(f), "y")
    difs = p == prec ? differentials : [embed_mpoly(g, embedding(RS), p) for g in differential_form_data(RS)[1]]
    xp = AcbField(p)(x_ball)
    ys = roots(f(xp, y), initial_prec = p, max_prec = 8*p)
    M = evaluate_differential_factors_matrix(RS, difs, xp, ys) * dx
    vals = [M[i, j] for i in 1:nrows(M), j in 1:ncols(M)]
    if all(isfinite, vals)
      return 10 * maximum([RR(abs(v)) for v in vals]; init = RR(0))
    end
    p >= 8*prec && error("Could not bound the integrand along a path (not finite at $p bits).")
    p *= 2
  end
end

function compute_ellipse_bound_heuristic(subpath::CPath, differentials_test::Vector{ AbstractAlgebra.Generic.MPoly{AcbFieldElem}}, int_group_rs::Vector{ArbFieldElem}, RS::RiemannSurfaceModel)
  num_of_int_groups = length(int_group_rs)
  if length(subpath.bounds) == 0
    i = maximum(filter(x -> (subpath.int_param_r > int_group_rs[x]), 1:num_of_int_groups);init = 1)
    subpath.integration_scheme_index = i
    r = int_group_rs[i]

    v = embedding(RS)
    # The working precision, not the (lower) requested one: f is embedded at
    # this precision, and for large degrees (e.g. a degree 92 polynomial with
    # tiny coefficients) f(x, y) at the requested precision can have balls
    # too wide to isolate its roots at all.
    prec = RS.computational_precision
    RR = ArbField(prec)
    f = embed_mpoly(defining_polynomial(RS), v, prec)
    CC = base_ring(f)
    I = onei(CC)
    f = change_base_ring(CC, f, parent = parent(f))

    Kxy = parent(f)
    Ky, y = polynomial_ring(base_ring(Kxy), "y")

    piC = const_pi(CC)
    piR = const_pi(RR)
	  b = sqrt(r^2-1)
    x = subpath.t_of_closest_d_point

	if abs(imag(x)) < RR(10^-10)
		xr = sign(Int, real(x))*r
  elseif abs(real(x)) < RR(10^-10)
		xr = sign(Int, imag(x))*b*I
	else

	  im_sign = sign(Int, imag(x))
	  re_sign = sign(Int, real(x))

	  xa = abs(real(x)) + I*abs(imag(x))
	  s = function(t)
		  return cos(t)*sin(t)-r*real(xa)*sin(t)+b*imag(xa)*cos(t)
	  end

	  sp = function(t)
		  return (cos(t)^2 - sin(t)^2) - r*real(xa)*cos(t) - b*imag(xa)*sin(t)
	  end
    nt = real(acos(xa))
	  t = nt - s(nt)/sp(nt)
	  while abs(t-nt) > 10^-3
		  nt = t
		  t -= s(t)/sp(t)
    end
	  xr = re_sign * r*cos(t) + im_sign*I*b*sin(t)
  end

   push!(subpath.bounds, _integrand_bound(RS, subpath, differentials_test, xr, prec))

  else
    subpath.integration_scheme_index = num_of_int_groups
  end
end

function compute_burger_bound_heuristic(subpath::CPath, differentials_test, int_group_rs, RS::RiemannSurfaceModel, lambda::ArbFieldElem = const_pi(parent(int_group_rs[1]))/2, ss::Int = 20)
  
  num_of_int_groups = length(int_group_rs)
  if length(subpath.bounds) == 0
    i = maximum(filter(x -> (subpath.int_param_r > int_group_rs[x]), 1:num_of_int_groups);init = 1)
    subpath.integration_scheme_index = i
    r = int_group_rs[i]

    v = embedding(RS)
    prec = RS.computational_precision        # see compute_ellipse_bound_heuristic
    RR = ArbField(prec)
    f = embed_mpoly(defining_polynomial(RS), v, prec)
    CC = base_ring(f)
    I = onei(CC)
    f = change_base_ring(CC, f, parent = parent(f))

    Kxy = parent(f)
    Ky, y = polynomial_ring(base_ring(Kxy), "y")

    piC = const_pi(CC)
    piR = const_pi(RR)
	  b = sqrt(r^2-1)
    x = subpath.t_of_closest_d_point

    CC = parent(x)
    I = onei(CC)
    phi = function(t::AcbFieldElem)
      return tanh(lambda*sinh(t + I*r))
    end
    if abs(real(x)) < RR(10)^-10
        xr = sign(Int, imag(x)) * phi(CC(0))
    else 
      xt = abs(real(x)) + I * abs(imag(x))
      tmax = acosh(const_pi(CC)/(2*lambda*sin(r)))
      xr = phi(CC(0))
      min_dist = abs(xt-xr)
      for k in (1:ss)
        t = k/ss*tmax
        z = phi(t)
        dist = abs(xt-z)
        if dist < min_dist
          min_dist = dist
          xr = z
        end
      end
      if abs(imag(x)) < RR(10)^-10
        xr = sign(Int, real(x)) * real(xr) + I * imag(xr)
      else
        xr = sign(Int, real(x)) * real(xr) + I * sign(Int, imag(x))*imag(xr)
      end
    end

    for tj in [CC(-1), CC(1), CC(xr)]
      push!(subpath.bounds, _integrand_bound(RS, subpath, differentials_test, tj, prec))
    end
  else
    subpath.integration_scheme_index = num_of_int_groups
  end
end

# (Rigorous bounds by covering the boundaries of the ellipses / DE regions with
# balls, as suggested by Neurohr, were tried: root isolation over a ball needs
# balls much smaller than the distances between the roots, so even when only
# an upper bound within a factor 16 of the maximum was asked for, a subpath
# needed thousands of balls (f26_g45: ~3000 per subpath, 4 s per scheme).
# Rigorous periods are left to the Voronoi approach.)
