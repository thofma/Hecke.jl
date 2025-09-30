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


function big_period_matrix(RS::RiemannSurface)
  
  if isdefined(RS, :big_period_matrix)
    return RS.big_period_matrix
  end

  g = genus(RS)
  diff_base = basis_of_differentials(RS)
  paths, pi1_gens = fundamental_group_of_punctured_P1(RS::RiemannSurface)
  num_paths = length(paths)
  prec = precision(RS)
  disc_points = discriminant_points(RS)
  small_C = AcbField(100)
  disc_points_low_precision = [small_C(P) for P in disc_points]
  
  #path`N seems to be less than what it is in Neurohr's implementation.
  for path in paths
    gauss_legendre_path_parameters(disc_points_low_precision, path, RS.extra_error)
  end
  
  int_parameters = ArbFieldElem[]
  for path in paths 
    if path_type(path) == 0
      append!(int_parameters, [ get_int_param_r(sub_path) for sub_path in get_subpaths(path) ])
    else
      append!(int_parameters, [get_int_param_r(path)])
    end
  end
  sort!(int_parameters);
  r_minimum = int_parameters[1]
  RR = parent(r_minimum)
  eps = RR(1/100)

  #We group the paths together based on their r-value. As a consequence, we will
  #have to compute fewer integration schemes later making the algorithm faster.
  #According to Neurohr p101 of his thesis it suffices to have 5 for the Gauss-Legendre method.
  int_groups = [ [],[],[],[],[] ]
		for r in int_parameters
			if r < r_minimum + RR(0.1)
        push!(int_groups[1],r)
      elseif r < r_minimum + RR(0.4)
        push!(int_groups[2],r)
			elseif r < r_minimum + RR(0.9)
        push!(int_groups[3],r)
      elseif r < r_minimum + RR(2.0)
        push!(int_groups[4],r)
			else 
        push!(int_groups[5],r)
      end
		end

  #Make r_minimum slightly smaller than what it was. (But still larger than 1)
  if r_minimum <= RR(1) + 2 * eps
    int_group_rs= [(1/2)*(r_minimum+1)]
  else
    int_group_rs = [r_minimum-eps]
  end

  #We only consider int_groups that contain more than 2 elements. If they only have two
  #or less elements, we simply group them together with the previous group
  filter!(x -> length(x) > 2, int_groups)

  append!(int_group_rs, [ minimum(int_group) - eps for int_group in int_groups[2:end]])

  differentials = RS.differential_form_data[1]

  v = embedding(RS)
  max_prec = 187
  embedded_differentials = [embed_mpoly(g, v, max_prec) for g in differentials]

  bound_temp = []
  for path in paths
    for subpath in get_subpaths(path)
      compute_ellipse_bound(subpath, embedded_differentials, int_group_rs, RS)
      append!(bound_temp, subpath.bounds)
    end
  end
  bound_temp = maximum(bound_temp)
  push!(RS.bounds, bound_temp)
  bound = maximum(RS.bounds)

  #Maybe change error value.
  #Change max_prec

  RS.integration_schemes = [IntegrationScheme(r, max_prec, RS.extra_error, bound) for r in int_group_rs ]

  f = embed_mpoly(defining_polynomial(RS), v, max_prec)
  Cc = base_ring(f)
  I = onei(Cc)
  f = change_base_ring(Cc, f, parent = parent(f))

  Kxy = parent(f)
  Ky, y = polynomial_ring(base_ring(Kxy), "y")
  m = degree(f, 2)

  # Copied from monodromy representation to compute the monodromy representation
  # we just computed while computing periods. 
  # There is probably a more clever way to avoid doubling code.
  s_m = SymmetricGroup(m)

  for path in paths
    Cc = AcbField(max_prec)
		integral_matrix = zero_matrix(Cc, m, g)
    subpaths = path.sub_paths
    x0 = start_point(subpaths[1])
		ys =  sort!(roots(f(x0, y), initial_prec = prec), lt = sheet_ordering)

		for subpath in subpaths
			
			integration_scheme = RS.integration_schemes[subpath.integration_scheme_index]
		  
			path_difference_matrix = zero_matrix(Cc, m, g)
      abscissae = integration_scheme.abscissae
      N = length(abscissae)
			An = analytic_continuation(RS, subpath, abscissae, ys)[2:end]
			
			if path_type(subpath) == 0
				for i in (1:N)
					integral_matrix_contribution = RS.evaluate_differential_factors_matrix(embedded_differentials, An[i][1],An[i][2])
					integral_matrix_contribution = change_base_ring(Cc, integral_matrix_contribution)
          integral_matrix_contribution *= integration_scheme.weights[i]
					path_difference_matrix += integral_matrix_contribution
				end
        path_difference_matrix *= evaluate_d(subpath, abscissae[1])
				integral_matrix += path_difference_matrix
        subpath.integral_matrix = path_difference_matrix
			else
        for i in (1:N)
					integral_matrix_contribution = RS.evaluate_differential_factors_matrix(embedded_differentials,An[i][1],An[i][2])
          integral_matrix_contribution = change_base_ring(Cc, integral_matrix_contribution)
          integral_matrix_contribution *= integration_scheme.weights[i] * evaluate_d(path, abscissae[i])
					path_difference_matrix += integral_matrix_contribution
				end
				integral_matrix += path_difference_matrix
			end
      ys = An[end][2]

        # Copied from monodromy representation to compute the monodromy representation
        # we just computed while computing periods. 
       # There is probably a more clever way to avoid doubling code.
      path_perm = sortperm(An[end][2], lt = sheet_ordering)
      assign_permutation(path, inv(s_m(path_perm)))
		end
    path.integral_matrix = integral_matrix
	end

  # Copied from monodromy representation to compute the monodromy representation
  # we just computed while computing periods. 
  # There is probably a more clever way to avoid doubling code.

  mon_rep = Tuple{Vector{CPath}, Perm{Int64}}[]
  
  for gamma in pi1_gens
    chain = map(t -> ((t > 0) ? paths[t] : reverse(paths[-t])), gamma)
    gamma_perm = prod(map(permutation, chain))
    
    if gamma_perm != one(s_m)
      push!(mon_rep, (chain, gamma_perm))
     end
  end
  
  inf_chain = Vector{CPath}[]
  inf_perm = one(s_m)
  
  for g in mon_rep
    inf_chain = vcat(inf_chain, map(reverse, g[1]))
    inf_perm *= g[2]
  end
  
  push!(mon_rep, (reverse(inf_chain), inv(inf_perm)))
  RS.monodromy_representation = mon_rep

  cycles, K, sym_transform = homology_basis(RS)

 

  chain_integrals = []
  for mon in mon_rep
    chain = mon[1]
    chain_length = length(chain)
    chain_permutation = mon[2]
    chain_integral = zero_matrix(Cc, m, g)
    sigma = one(s_m)
    
    for k in (1:chain_length)
      path = chain[k]
      chain_integral += inv(sigma) * path.integral_matrix
      sigma *= permutation(path)
    end
    push!(chain_integrals, chain_integral)
  end

  pre_period_matrix = Vector{AcbFieldElem}[]
  for cycle in cycles
		
		cycle_integral = [zero(Cc) for x in 1:g]
		l = 1
		while l < length(cycle)
			sheet = cycle[l]
			while sheet != cycle[l+2]
				cycle_integral += chain_integrals[cycle[l+1]][sheet,:]
				sheet = mon_rep[cycle[l+1]][2][sheet]
			end
			l += 2
		end
		push!(pre_period_matrix, cycle_integral)
	end

	PMAPMB = sym_transform * matrix(pre_period_matrix)

	big_period_matrix = transpose(PMAPMB[1:2*g,:])
  RS.big_period_matrix = big_period_matrix
  return big_period_matrix
end

#We use the convention that  
#[0  1]
#[-1 0] defines a polarization.
function small_period_matrix(RS::RiemannSurface)
  if isdefined(RS, :small_period_matrix)
    return RS.small_period_matrix
  end
  g = genus(RS)
  P = big_period_matrix(RS)
  P1 = P[1:g, 1:g]
  P2 = P[1:g, g+1:2*g]
  small_period_matrix = P1^(-1)*P2
  RS.small_period_matrix = small_period_matrix
  return small_period_matrix
end

function compute_ellipse_bound(subpath::CPath, differentials_test, int_group_rs, RS::RiemannSurface)
  
  num_of_int_groups = length(int_group_rs)
  if length(subpath.bounds) == 0
    i = maximum(filter(x -> (subpath.int_param_r > int_group_rs[x]), 1:num_of_int_groups);init = 1)
    subpath.integration_scheme_index = i
    r = int_group_rs[i]

    v = embedding(RS)
    prec = precision(RS)
    Rc = ArbField(prec)
    f = embed_mpoly(defining_polynomial(RS), v, prec)
    Cc = base_ring(f)
    I = onei(Cc)
    f = change_base_ring(Cc, f, parent = parent(f))

    Kxy = parent(f)
    Ky, y = polynomial_ring(base_ring(Kxy), "y")

    piC = const_pi(Cc)

    #This should be done in a more clever way by sampling with less points with
    #bigger radius in the beginning and then zooming in
    n = 2000
    test_points = [k*2*pi/n for k in 0:n-1]

    b = sqrt(r^2-1)

    max_bound_t = []
      for t in test_points
        e_t = r*cos(t) + b*sin(t)*I
        radius = real(piC/n)
        #ccall((:acb_add_error_arb, libflint), Cvoid, (Ref{AcbFieldElem}, 
        #Ref{ArbFieldElem}), e_t, radius)
        x_ball = evaluate(subpath, e_t)
        ys = roots(f(x_ball, y), initial_prec = prec)
        g = RS.evaluate_differential_factors_matrix
        bounds_matrix = g(differentials_test, x_ball, ys)
        bounds_matrix *= evaluate_d(subpath, e_t)
        max_bound_t = push!(max_bound_t, 10 * maximum([Rc(abs(v)) for 
        v in bounds_matrix]; init = Rc(0)))
      end
      max_bound = maximum(max_bound_t)
      push!(subpath.bounds, max_bound)

  else 
    subpath.integration_scheme_index = num_of_int_groups
  end
end 
