################################################################################
#
#          RieSrf/PeriodMatrix.jl : Computing the period matrix
#
# (C) 2023 Jeroen Hanselman
#
################################################################################

function big_period_matrix(RS::RiemannSurface)

  g = genus(RS)
  diff_base = basis_of_differentials(RS)
  paths, _ = fundamental_group_of_punctured_P1(RS::RiemannSurface)
  num_paths = length(paths)
  
  disc_points = discriminant_points(RS)
  small_C = AcbField(100)
  disc_points_low_precision = [small_C(P) for P in disc_points]
  
  #path`N seems to be less than what it is in Neurohr's implementation.
  for path in paths
    gauss_legendre_path_parameters(disc_points_low_precision, path, RS.extra_error)
  end
  
  int_parameters = []
  for path in paths 
    if path_type(path) == 0
      vcat!(int_parameters, [ get_int_param_r(sub_path) for sub_path in get_subpaths(path) ]
    else
      vcat!(int_parameters,get_int_param_r(path))
    end
  end
  sort(int_parameters);
  r_minimum = int_parameters[1]
  eps = 1/100

  #We group the paths together based on their r-value. As a consequence, we will
  #have to compute fewer integration schemes later making the algorithm faster.
  #According to Neurohr p101 of his thesis it suffices to have 5 for the Gauss-Legendre method.
  int_groups = [ [],[],[],[],[] ]
		for r in int_parameters
			if r < rm+0.1 then 
        append!(int_groups[1],r)
      elseif r < rm+0.4 then	
        append!(int_groups[2],r)
			elseif r < rm+0.9 then 
        append!(int_groups[3],r)
      elseif r < rm+2.0 then 
        append!(int_groups[4],r)
			else 
        append!(int_groups[5],r)
      end
		end

  #Make r_minimum slightly smaller than what it was. (But still larger than 1)
  if r_minimum <= 1 + 2 * eps then
    int_group_rs= [(1/2)*(r_minimum+1)]
  else
    int_group_rs = [r_minimum-eps]
  end

  #We only consider int_groups that contain more than 2 elements. If they only have two
  #or less elements, we simply group them together with the previous group
  filter(x -> length(x) > 2, int_group_rs)

  vcat!(int_group_rs, [ min(r) - eps for r in int_group_rs])


  bound_temp = []
  for path in paths
    for subpath in get_subpaths(path)
      compute_ellipse_bound(subpath, differentials_test, int_group_rs, RS)
      vcat!(bound_temp, subpath.bounds)
    end for;
  end for;
  bound_temp = max(bound_temp)
  append!(RS.bounds, bound_temp)
  bound = max(RS.bounds)
  bound = bound2
  RS.integration_schemes = [gauss_legendre_integration_scheme(r, RS.max_precision, err, bound) for r in int_group_rs ]
end


function compute_ellipse_bounds(subpath::CPath, differentials_test, int_group_rs, RS::RiemannSurface)
  
  num_of_int_groups = length(int_group_rs)
  if length(subpath.bounds) = 0
    i = maximum(filter [x -> subpath.int_param_r > int_group_rs[x]| 1:length(int_group_rs);init = 1]
    gamma.integration_scheme_index = i
    r = int_group_rs[i]

    v = embedding(RS)
    prec = precision(RS)
    Rc = ArbField(prec)
    f = embed_mpoly(defining_polynomial(RS), v, prec)
    Cc = base_ring(f)
    f = change_base_ring(Cc, f, parent = parent(f))

    Kxy = parent(f)
    Ky, y = polynomial_ring(base_ring(Kxy), "y")

    piC = const_pi(Cc)
    n = 20
    test_points = [k*2*pi/n for k in 1:n]
    a = cosh(r), b = sinh(r)
    M = 1
      for t in test_points
        e_t = a*cos(t) + b*cos(t)
        x_ball = evaluate(subpath, e_t)
        radius = real(piC/n)
        ccall((:acb_add_error_arb, libarb), Cvoid, (Ref{AcbFieldElem}, Ref{ArbFieldElem}), gamma_et, radius)
        
        ys = roots(gamma_et_ball, y), initial_prec = prec)
        bounds_matrix = evaluate_differential_factors_matrix(x_ball, ys, differentials_test)
        append!(subpath.bounds, maximum(bounds_matrix; init = Rc(1)))
      end

  else 
    gamma.integration_scheme_index = num_of_int_groups
  end
end 
