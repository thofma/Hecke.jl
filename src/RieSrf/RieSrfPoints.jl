
@doc raw"""
    (RS::RiemannSurface)(coords::Vector{AcbFieldElem})

Return the point $P$ of $RS$ with coordinates specified by `coords`, which can
be either affine coordinates (`length(coords) == 2`) or projective coordinates
(`length(coords) == 3`).
"""
function (RS::RiemannSurface)(coords::Vector{AcbFieldElem})
  f = complex_defining_polynomial(RS)
  CC = base_ring(parent(f))
  RR = ArbField(precision(CC))
  @req 2<=length(coords)<=3 "Points need to be given in either affine coordinates (x, y) or projective coordinates (x : y : z)"
  if length(coords) == 2
    x_coord = CC(coords[1])
    y_coord = CC(coords[2])
    v = abs(f(x_coord, y_coord))
    if contains(v, RR(0))
      for s in RS.finite_singularities
        if contains(x_coord, s[1]) && contains(y_coord, s[2]) && contains(CC(1), s[3])
          error("Singular point of defining polynomial. Not a point on the Riemann surface.")
        end
      end
      point = RiemannSurfacePoint(RS)
      point.coordx = coords[1]
      point.coordy = coords[2]
      point.is_singular = false
      point.homog_coords = [point.coordx, point.coordy, CC(1)]
      point.is_finite = true
      for s in ramification_points(RS)
        if contains(x_coord, s.coordx) && contains(y_coord, s.coordy)
          return s
        end
      end
      point.ramification_index = 1
      return point
    else
      error("Not a point on the Riemann surface.")
    end
  elseif length(S) == 3
    homog_coords = [CC(S[1], CC(S[2]), CC(S[3]))]
    if homog_coords[3] != CC(0)
      return RS([homog_coords[1]/homog_coords[3], homog_coords[2]/homog_coords[3]])
    else
      point = RiemannSurfacePoint(RS)
      point.is_finite = false
      point.homog_coords = homog_coords
      for s in RS.singular_points
        if contains(homog_coords, s)
          error("Singular point of projective closure. Not a point on the Riemann surface.")
        end
      end
      for s in RS.infinite_points
        if contains(homog_coords, s.homog_coords)
          return s
        end
      end
      error("Not on a point the Riemann surface.")
    end
  end
end



@doc raw"""
    is_finite(P::RiemannSurfacePoint)

Return true if the point is a finite point of the Riemann surface.
"""
function is_finite(P::RiemannSurfacePoint)
  return P.is_finite
end

function show(io::IO, P::RiemannSurfacePoint)
  CC = parent(P.coordx)
  infty = CC(1/0)
  CC = AcbField(30)
  if is_finite(P)
    if !P.is_singular
      print(io, "Point  ($(CC(P.homog_coords[1])) : $(CC(P.homog_coords[2])) : $(CC(P.homog_coords[3])))  of $(P.parent)")
    else
      print(io, "Point lying in the desingularization of singular point $(CC(P.coordx)), $(CC(P.coordy)) in sheets $(P.sheets) of $(P.parent)")
    end
  else
    if P.coordx == CC(1/0) isdefined(P, :sheets)
      print(io, "Point at infinity on sheets $(P.sheets) of $(P.parent)")
    elseif P.is_singular
      print(io, "Point lying in the desingularization of singular point with x-coordinate $(CC(P.coordx)) in sheets $(P.sheets) of $(P.parent)")
    elseif P.coordy == CC(1/0)
      print(io,"Y-infinite point over x = $(CC(P.coordx)) on sheets $(P.sheets) of $(P.parent)")
    else
      error("Error in show function")
    end
  end
end


function ==(P::RiemannSurfacePoint, Q::RiemannSurfacePoint)
  RS = parent(P)
  prec = precision(RS)
  CC = AcbField(prec)
  RR = ArbField(prec)
  if RS != parent(Q)
    return
  end

  if is_finite(P) && is_finite(Q)
    if !contains(abs(P.coordx - Q.coordx), RR(0))
      return false
    else
      if !P.is_singular && !Q.is_singular
        return  contains(abs(P.coordy - Q.coordy), RR(0))
      elseif isdefined(P.sheets) && isdefined(Q.sheets)
        return Set(P.sheets) == Set(Q.sheets)
      else
        return false
      end
    end
  end

  if !is_finite(P) && !is_finite(Q)
    if isdefined(P.coordx) && isdefined(Q.coordx)
      if P.coordx == CC(1/0) && Q.coordx == CC(1/0)
        return Set(P.sheets) == Set(Q.sheets)
      else
        if contains(abs(P.coordx - Q.coordx), RR(0))
          return Set(P.sheets) == Set(Q.sheets)
        end
      end
    else
      if isdefined(P.homog_coords) && isdefined(Q.homog_coords)
        @req P.homog_coords[3] == CC(0) "This should not happen. There is a bug in the code."
        @req Q.homog_coords[3] == CC(0) "This should not happen. There is a bug in the code."
        if P.homog_coords[1] != 0
          if Q.homog_coords[1] != 0
            return contains(abs(P.homog_coords[2]/P.homog_coords[1]-Q.homog_coords[2]/Q.homog_coords[1]), zero(RR))
          else
            return false
          end
        else
          return Q.homog_coords[1] == 0
        end
      end
    end
  end
  return false
end

function parent(P::RiemannSurfacePoint)
  return P.parent
end


#Returns the roots using flint even if flint is unable to isolate the roots
#E.g. when the polynomial has multiple roots. In this case the roots that 
#were not isolated will be returned with low precision.
function find_roots_without_isolation(f::AcbPolyRingElem)
  m = degree(f)
  temp_vec_res = acb_vec(m)
  CC = base_ring(f)
  prec = precision(CC)
  dd = ccall((:acb_poly_find_roots, libflint), Cint, (Ptr{acb_struct}, Ref{AcbPolyRingElem}, Ptr{acb_struct}, Int, Int), temp_vec_res, f, C_NULL, 0, prec)
  z = array(CC, temp_vec_res, m)
  acb_vec_clear(temp_vec_res, m)
  return z
end 

#Returns roots with their ramification indices. If the maximal ramification index is
#known it can be passed to m. In this case roots are only checked up to the mth derivative.
function find_roots_with_mult(f::PolyRingElem, m::Int = degree(f))
  CC = base_ring(f)
  RR = ArbField(precision(CC))

  roots_found = AcbFieldElem[]
  mult = Int[]
  derivatives = [f]
  for i in (1:m-1)
    push!(derivatives, derivative(derivatives[end]))
  end
  for n in (m:-1:1)
    R = find_roots_without_isolation(derivatives[n])
    for r in R
      if all(map(x -> contains(x(r), zero(CC)), derivatives[1:n]))
        if length(roots_found)==0
          push!(roots_found, r)
          push!(mult, n)
        else 
          distance, index = closest_point(r, roots_found)
          if !contains(distance, RR(0))
            push!(roots_found, r)
            push!(mult, n)
          end
        end
      end
    end
  end
  @req sum(mult) == degree(f) "Sum of multiplicities does not match degree. Error in root computation."
  return roots_found, mult
end

#Analyzes all the special points on the Riemann surface.
#This includes:
# - infinite points: Points where the x-coordinate is infinity
# - y-infinite points: Points that correspond to [0:1:0] in projective coordinates
# - critical points: Points for which df/dy = 0
# - singular points: Points for which df/dy = df/dx = 0
function analyze_special_points(RS::RiemannSurface)
  if isdefined(RS, :infinite_points) && isdefined(RS, :y_infinite_points) && isdefined(RS, :singular_points)
    return nothing
  end

  infinite_points = RiemannSurfacePoint[]
  y_infinite_points = RiemannSurfacePoint[]
  critical_values = Set(AcbFieldElem[])
  critical_points = RiemannSurfacePoint[]
  finite_singularities = Set(Vector{AcbFieldElem}[])

  m = RS.degree[1]
  prec = precision(RS)
  f = embed_mpoly(RS.defining_polynomial, RS.embedding, prec)
  CC = base_ring(f)
  RR = ArbField(precision(CC))
  R, z = polynomial_ring(CC)

  dfx = derivative(f,1)
  dfy = derivative(f,2)


  for k in (1:length(RS.closed_chains))
    chain = RS.closed_chains[k]
    chain.points = RiemannSurfacePoint[]
    xk = center(chain)

    yk = fiber(f, xk)

    dfxk = dfx(xk,z)
    dfyk = dfy(xk, z)
    cyc_decomp = collect(cycles(permutation(chain)))
    if length(yk) == 0 
      for k in (1:length(cyc_decomp))
        point = RiemannSurfacePoint(RS)
        point.coordx = xk
        point.index = k
        point.sheets = cyc_decomp[k]
        point.is_finite = false
        point.coordy = CC(1/0)
        point.homog_coords = [CC(0),CC(1),CC(0)]
        push!(y_infinite_points, point)
        push!(chain.points, point)
      end
    elseif length(yk) < m
      #if !isassigned(RS.ajm_discriminant_points, k)
      #  ajm_discriminant_points(RS, k)
      #end
      yk_comp, cyc_decomp = ramification_point_sheets(RS, yk, k)
      for l in (1:length(cyc_decomp))
        point = RiemannSurfacePoint(RS) 
        point.sheets = cyc_decomp[l]
        point.ramification_index = length(point.sheets)
        point.coordx = xk
        point.index = l
        distance, index = closest_point(yk_comp[l], yk)
        if !contains(distance, RR(0))
          point.is_finite = false
          point.coordy = CC(1/0)
          point.homog_coords = [CC(0),CC(1),CC(0)]
          push!(y_infinite_points, point)
        else
          point.is_finite = true
          point.is_singular = false
          point.coordy = yk[index]
          point.homog_coords = [point.coordx, point.coordy, CC(1)]

          if contains(dfyk(point.coordy),CC(0))
            if contains(dfxk(point.coordy), CC(0))
              push!(finite_singularities, [point.coordx, point.coordy])
                point.is_singular = true
            end
            push!(RS.critical_values, point.coordx)
            push!(RS.critical_points, point)
          end
        end
        push!(chain.points, point)
      end
      @req length(chain.points) == length(cyc_decomp) "Error in analyzing special points."
    else
      yk, cyc_decomp = ramification_point_sheets(RS, yk, k)
      for l in (1:length(cyc_decomp))
        point = RiemannSurfacePoint(RS)
        point.is_finite = true
        point.is_singular = false
        point.index = l
        point.sheets = cyc_decomp[l]
        point.ramification_index = length(point.sheets)
        point.coordx = xk
        point.coordy = yk[point.sheets[1]]
        point.homog_coords = [point.coordx, point.coordy, CC(1)]
        if contains(dfyk(point.coordy),CC(0))
          if contains(dfxk(point.coordy), CC(0))
            push!(finite_singularities, [point.coordx, point.coordy])
              point.is_singular = true
          end
          push!(critical_values, point.coordx)
          push!(critical_points, point)
        end
        push!(chain.points, point)
      end
      @req (length(chain.points) == length(cyc_decomp)) "Error in analyzing special points."
      RS.critical_points = critical_points
      RS.critical_values = collect(critical_values)
    end
  end
  RS.finite_singularities = collect(finite_singularities)

  #Analyze points at infinity
  #We take the homogeneous defining polynomial of RS and set z=0.
  f_with_z_is_0 = sum(filter(x -> total_degree(x) == total_degree(f),[ term for term in terms(f)]))
  SFX1 = find_roots_with_mult(f_with_z_is_0(1,z))[1]
  SFY1 = find_roots_with_mult(f_with_z_is_0(z,1))[1]
  all_points = Set{Vector{AcbFieldElem}}()
  for y in SFX1
    if contains(abs(y), RR(0))
      point = [CC(1), CC(0) ,CC(0) ]
    else
      point = [CC(1/y), CC(1) ,CC(0) ]
    end
    push!(all_points, point)
  end

  for xk in SFY1 
    if contains(abs(xk), RR(0))
      point = [CC(0), CC(1), CC(0)]
      push!(all_points, point)
    else
      dist, ind = closest_point(xk,[ P[1] for P in all_points]) 
      if !contains(dist, RR(0))
        point = [xk, CC(1), CC(0)]
        push!(all_points, point)
      end
    end
  end

  RS.infinity_coords = collect(all_points)

  fC_homogeneous = embed_mpoly(RS.homogeneous_defining_polynomial, RS.embedding, prec)
  partial_derivs = [derivative(fC_homogeneous, k) for k in (1:3) ]
  RS.infinite_singularities = []
  Rxyz = parent(fC_homogeneous)
  for k in (1:length(RS.infinity_coords))
    point = RS.infinity_coords[k]
    df_evaluated = [ df(point...) for df in partial_derivs ]
    if all([contains(abs(v), RR(0)) for v in df_evaluated])
      push!(RS.infinite_singularities, point)
    end
  end
  RS.singular_points = vcat([ push!(P,CC(1)) for P in RS.finite_singularities], RS.infinite_singularities)
  inf_chain_points = RiemannSurfacePoint[]
  inf_perm = permutation(RS.inf_chain)
  cyc_decomp = collect(cycles(inf_perm))
  for k in (1:length(cyc_decomp))
    point = RiemannSurfacePoint(RS) 
    point.coordx = CC(1/0) 
    point.coordy = CC(1/0)
    point.is_finite = false
    point.index = k 
    point.sheets = cyc_decomp[k]
    point.ramification_index = length(point.sheets)
    push!(inf_chain_points, point)
  end
  RS.inf_chain.points = inf_chain_points
  RS.infinite_points = RS.inf_chain.points
   RS.y_infinite_points = y_infinite_points
  return nothing
end


#Compute the Abel-Jacobi map from the basepoint to a special point
#on all sheets using double-exponential integration. 

#Used for singular points, infinite points and y-infinite points.
#Can also be used for other critical points if the method `direct` is used.

#Note: This method is heuristic as we do not have proper error bounds.
#(Double exponential-integration is used because it is probably the 
#best method to compute problematic integrals).
function ajm_DE_special_point(gamma::CPath, k::Int, RS::RiemannSurface, test_chain::CChain, max_iterations = 5)
        
  prec = RS.extra_prec
  new_prec = true
  go_on = true

  iterations = 1

  CC = complex_field(RS)

  if k == 0   #Point at infinity
    c = maximum([ length(cycle) for cycle in  collect(cycles(permutation(RS.inf_chain))) ])+1
  else
    c = maximum([ length(cycle) for cycle in  collect(cycles(permutation(RS.closed_chains[k]))) ])+1
  end
  
  error = RS.extra_error
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
  while go_on && iterations <= max_iterations
    go_on = false
    #Needs to be determined heuristically in a better way:
    comp_prec = 2*c*prec
    CC = AcbField(comp_prec)
    RR = ArbField(comp_prec)
    Cz, z = polynomial_ring(CC)
    Cxy, (x,y) = polynomial_ring(CC,2)
    v = RS.embedding
    fC = embed_mpoly(defining_polynomial(RS), v, comp_prec)
    differentials = RS.differential_form_data[1]
    embedded_differentials = [embed_mpoly(g, v, comp_prec) for g in differentials]

    if k == 0 #Point at infinity
      N_gamma = gamma
      err2 = (RR(1/2)*RS.error^(c+1))^2
    else
      N_gamma = c_line(CC(start_point(gamma)),CC(end_point((gamma))))
      err2 = error^2/4
    end


    N = round(Int, 1//h * 72 //10)
    N2P1 = 2*N+1
    abscissae, weights = tanh_sinh_quadrature_integration_points(N, RR(h))
    push!(abscissae,RR(1))
    xj = start_point(N_gamma)
		yj =  sort!(roots(fC(xj, z), initial_prec = comp_prec), lt = sheet_ordering)
    yj_new = yj

    path_difference_matrix = zero_matrix(CC, m, g)
    for i in (1:N2P1)
      xj_new = evaluate(N_gamma, abscissae[i+1])
      #Integrating into infnity gives problems when trying to do it with the more 
      #rigorous recursive_continuation. Therefore we forego the precision check and
      #use a sanity check later on to check if our result is heuristically correct.
      try
        yj_new, new_prec = recursive_continuation_manual(fC, xj, xj_new, yj, err2, target_error)
        if new_prec
          go_on = true
          c +=1
          h = h/2
          iterations +=1
          break
        end
      catch
        break
      end

			integral_matrix_contribution = evaluate_differential_factors_matrix(RS, embedded_differentials, xj, yj)
			integral_matrix_contribution = change_base_ring(CC, integral_matrix_contribution)
      integral_matrix_contribution *= weights[i] * evaluate_d(N_gamma, abscissae[i])
      
      max_abs = maximum([abs(c) for c in integral_matrix_contribution])
      if (i > N && max_abs < error)
        break
      end

      xj = xj_new
      yj = yj_new
      
			path_difference_matrix += integral_matrix_contribution
		end


    N_gamma.integral_matrix = path_difference_matrix
    push!(gammas, N_gamma)

    if go_on == false 
      if permutation(test_chain) != one(s_m)
        sigma = permutation(test_chain)
        V = N_gamma.integral_matrix - inv(sigma) * N_gamma.integral_matrix -  change_base_ring(CC,test_chain.integral_matrix)
        err_V = maximum([ abs(c) for c in V ])
        N_gamma.integral_matrix - inv(sigma) * N_gamma.integral_matrix
       
        if contains(target_error*100, err_V)
          go_on = false 
          continue
        else 
          h = h/2
          go_on = true
          new_prec = false
          iterations += 1
        end
      else
        #If we can't determine correctness by comparing against the test_chain we need to recompute with h/2
        #and compare against the more precise computation done with the smaller step size
        s = length(gammas)
        if s == 1 then
          go_on = true
          h = h/2
          new_prec = false
          continue
        else
          V = gammas[s].integral_matrix-gammas[s-1].integral_matrix
          err_V = maximum([ abs(c) for c in V ])
           if contains(target_error*100, err_V)
              go_on = false 
              continue
          else 
            h = h/2
            go_on = true
            new_prec = false
            iterations += 1
          end
        end
      end
    end
  end

  final_gamma = gammas[end]
  #Error, permutation & sheets 
  path_perm = sortperm(yj_new, lt = sheet_ordering)
  assign_permutation(final_gamma, inv(s_m(path_perm)))


  V = map(abs, V)
  #Add the heuristic error. (Could optionally also take err_V instead?)
  for i in (1:m)
    for j in (1:g)
      t = final_gamma.integral_matrix[i,j]
      err_t = V[i,j]
      ccall((:acb_add_error_arb, Hecke.libflint), Cvoid, (Ref{AcbFieldElem}, Ref{ArbFieldElem}), t, err_t)
      final_gamma.integral_matrix[i,j] = t
    end
  end
  #Save integrals
  if k == 0 #Point at infinity
    RS.ajm_infinite_points = final_gamma
  else
    gamma.integral_matrix = final_gamma.integral_matrix
    gamma.sheets = yj_new
    assign_permutation(gamma, permutation(final_gamma))
  end
end

#Used to check the sheets a ramified points lies on. Neurohr does not do this, but his 
#output also seems to be incorrect to me. Might need to check and test more to be sure.
function ramification_point_sheets(RS::RiemannSurface, yk::Vector{AcbFieldElem}, k::Int)
  error = RS.extra_error
  prec = precision(RS)
  CC = AcbField(prec)
  RR = ArbField(prec)
  Cz, z = polynomial_ring(CC)
  v = RS.embedding
  fC = embed_mpoly(defining_polynomial(RS), v, prec)
  chain = RS.closed_chains[k]


  Sm = parent(permutation(chain))
  CC = chain.paths[1].C
  h = QQ(16//125)
  l = 1
  paths = chain.paths
#Find the beginning of the loop around the center.
  while (path_type(chain.paths[l])!= 1 && path_type(chain.paths[l])!= 2) || !contains(center(chain.paths[l]) - center(chain), CC(0))
    l+=1
  end

  loop = CPath[]
  while path_type(chain.paths[l]) != 0
    push!(loop, chain.paths[l])
    l += 1
  end

  loop_perm = permutation(CChain(loop))

  path = c_line(chain.paths[l].start_point_high, chain.paths[l].center_high)


  
  N = round(Int, 1//h * 72 //10)
  N2P1 = 2*N+1
  abscissae, weights = tanh_sinh_quadrature_integration_points(N, RR(h))
  push!(abscissae,RR(1))

  xj = start_point(path)
  xj_new = xj
	yj =  sort!(roots(fC(xj, z), initial_prec = prec), lt = sheet_ordering)
  yj_new = yj
  for i in (1:N2P1)
    xj_new = evaluate(path, abscissae[i+1])
    try
      yj_new, _ = Hecke.RiemannSurfaces.recursive_continuation_manual(fC, xj, xj_new, yj, error^2/4)
    catch
      break
    end
  end


  sigma = inv(Sm(sortperm(yj_new, lt = sheet_ordering)))


  if length(yk) < length(yj_new)
    for i in (1:length(yj_new))
      distance, index = closest_point(yj_new[i], yk)
      if distance < error
        yj_new[i] = yj_new[index]
      end
    end
    yk_sorted = [yj_new[sigma[k]] for k in (1:length(yj_new))]
  else
    yk_sorted = [yk[sigma[k]] for k in (1:length(yk))]
  end
  return yk_sorted, collect(cycles(loop_perm))
end

#Apply ajm_DE_discriminant_point to all critical points.
function ajm_discriminant_points(RS::RiemannSurface, k::Int)
  chain = RS.closed_chains[k]
  CC = chain.paths[1].C
  l = 1
  paths = chain.paths
#Find the beginning of the loop around the center.
  while (path_type(chain.paths[l])!= 1 && path_type(chain.paths[l])!= 2) || !contains(center(chain.paths[l]) - center(chain), CC(0))
    l+=1
  end
  test_chain_paths = CPath[]
  while path_type(chain.paths[l]) != 0
    push!(test_chain_paths, chain.paths[l])
    l += 1
  end
  test_chain = CChain(test_chain_paths)
  path_to_center = vcat(chain.paths[1:l-1], c_line(chain.paths[l-1].end_point_high, chain.center))
  
  ajm_DE_special_point(path_to_center[l], k, RS, test_chain)
  chain_to_center = CChain(path_to_center)

  perm = prod([ permutation(path_to_center[k]) for k in (1:l-1) ])
  chain_to_center.sheets = [ path_to_center[l].sheets[perm[k]] for k in (1:RS.degree[1]) ]

  RS.ajm_discriminant_points[k] = chain_to_center
end

@doc raw"""
    ramification_points(RS::RiemannSurface)

Return the ramification points of the Riemann surface.
"""
function ramification_points(RS::RiemannSurface)
  result = RiemannSurfacePoint[]
  for chain in vcat(RS.closed_chains, [RS.inf_chain])
    for P in chain.points
      if P.ramification_index > 1
        push!(result, P)
      end
    end
  end
  return result
end

