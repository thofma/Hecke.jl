################################################################################
#
#  RieSrf/SpecialPoints.jl : critical, singular and infinite points
#
################################################################################

#Analyzes all the special points on the Riemann surface.
#This includes:
# - infinite points: Points where the x-coordinate is infinity
# - y-infinite points: Points that correspond to [0:1:0] in projective coordinates
# - critical points: Points for which df/dy = 0
# - singular points: Points for which df/dy = df/dx = 0
function analyze_special_points(RS::RiemannSurfaceModel)
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

  # All discriminant points, also those with trivial monodromy: there the
  # fiber can still contain singular points (e.g. a node) or y-infinite points.
  chains = RS.pi1_chains
  K = length(chains)
  yks = Vector{Vector{AcbFieldElem}}(undef, K)
  ram = Vector{Any}(undef, K)
  Threads.@threads for k in 1:K
    yks[k] = fiber_repeated(RS, center(chains[k]))
    if length(yks[k]) > 0
      ram[k] = ramification_point_sheets(RS, yks[k], chains[k])
    end
  end

  for k in (1:K)
    chain = chains[k]
    chain.points = RiemannSurfacePoint[]
    xk = center(chain)

    yk = yks[k]

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
      yk_comp, cyc_decomp = ram[k]
      for l in (1:length(cyc_decomp))
        point = RiemannSurfacePoint(RS) 
        point.sheets = cyc_decomp[l]
        point.ramification_index = length(point.sheets)
        point.coordx = xk
        point.index = l
        # (yk_comp is indexed by the sheets)
        distance, index = closest_point(yk_comp[point.sheets[1]], yk)
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
            push!(critical_values, point.coordx)
            push!(critical_points, point)
          end
        end
        push!(chain.points, point)
      end
      @req length(chain.points) == length(cyc_decomp) "Error in analyzing special points."
    else
      yk, cyc_decomp = ram[k]
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
    end
  end
  RS.critical_points = critical_points
  RS.critical_values = collect(critical_values)
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

#Used to check the sheets a ramified points lies on. Neurohr does not do this, but his 
#output also seems to be incorrect to me. Might need to check and test more to be sure.
function ramification_point_sheets(RS::RiemannSurfaceModel, yk::Vector{AcbFieldElem}, chain::CChain)
  error = RS.computational_error
  prec = precision(RS)
  CC = AcbField(prec)
  RR = ArbField(prec)
  Cz, z = polynomial_ring(CC)
  v = RS.embedding
  fC = embed_mpoly(defining_polynomial(RS), v, prec)
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
	yj =  sort!(_accurate_roots(fC(xj, z), prec), lt = sheet_ordering)
  yj_new = yj
  ws = ContinuationWorkspace(_split_in_y(fC), Cz)   # once, not per step
  err2 = error^2/4
  for i in (1:N2P1)
    xj_new = evaluate(path, abscissae[i+1])
    try
      yj_new, _ = recursive_continuation_manual!(ws, xj, xj_new, yj, err2)
    catch
      break
    end
    # Continue from the point just reached.
    xj = xj_new
    yj = yj_new
  end

  sigma = inv(Sm(sortperm(yj_new, lt = sheet_ordering)))

  if length(yk) < length(yj_new)
    for i in (1:length(yj_new))
      distance, index = closest_point(yj_new[i], yk)
      if distance < error
        yj_new[i] = yk[index]
      end
    end
    yk_sorted = [yj_new[sigma[k]] for k in (1:length(yj_new))]
  else
    yk_sorted = [yk[sigma[k]] for k in (1:length(yk))]
  end
  return yk_sorted, collect(cycles(loop_perm))
end

@doc raw"""
    ramification_points(RS::RiemannSurfaceModel)

Return the ramification points of the Riemann surface.
"""
function ramification_points(RS::RiemannSurfaceModel)
  _ensure_special_points!(RS)
  result = RiemannSurfacePoint[]
  for chain in vcat(RS.pi1_chains, [RS.inf_chain])
    for P in chain.points
      if P.ramification_index > 1
        push!(result, P)
      end
    end
  end
  return result
end
