#Transform the output of the Abel-Jacobi map to an element of R^(2g)/Z^(2g)
#under the canonical isomorphism.
function period_lattice_reduction_real(V::AcbMatrix, RS::AbstractRiemannSurfaceModel)
  g = genus(RS)
  T = RS.real_reduction_matrix
  RR = base_ring(T)
  W = vcat(real(V), imag(V))
  W = T*W
  return matrix(RR, 2*g, 1, [w - round(ZZRingElem, w) for w in W])
end

#Transform the output of the Abel-Jacobi map to an element of C^g/(1, tau)
#under the canonical isomorphism.
function period_lattice_reduction_complex(V::AcbMatrix, RS::AbstractRiemannSurfaceModel)
  g = genus(RS)
  CC = parent(V[1,1])

  tau = small_period_matrix(RS)
  V = RS.complex_reduction_matrices[1] * V
  W = real(RS.complex_reduction_matrices[2]) * imag(V)
  V1 = matrix(CC, g, 1, [round(ZZRingElem, w) for w in W])
  V -= tau * V1
  CC = parent(V[1,1])
  return V - matrix(CC, g, 1,[round(ZZRingElem, real(v)) for v in V])
end

#Takes a given path as input and replaces it with a chain of paths
#avoiding problematic points if needed.
function find_path_on_sheet(gamma::CPath, RS::RiemannSurfaceModel)

  @req path_type(gamma) == 0 "Path needs to be a line."
  int_points = Tuple{Int64, AcbFieldElem, AcbFieldElem}[]
  discriminant_points = discriminant_points_high_prec(RS)
  for j in (1:length(discriminant_points))
    d_point = discriminant_points[j]
    circle = c_circle(d_point - RS.safe_radii[j], d_point)
    intersect_test, points = intersection_points(gamma, circle)
    if intersect_test
      push!(int_points, (j, points[1], points[2]))
    end
  end

  sort!(int_points)
  new_path = [gamma]
  base_point_x = RS.base_point.coordx
  CC = parent(base_point_x)
  i = onei(CC)

  for j in (1:length(int_points))
    if contains(start_point(new_path[end]), int_points[j][2])
      V = angle((discriminant_points[int_points[j][1]] - base_point_x) 
      * exp((-1)*angle(end_point(gamma) - base_point_x)*i))
      #In case V = 0, we put the orientation to -1
      arc_orientation = -1
      try
        arc_orientation = sign(Int, V)
      catch
      end

      next_arc = c_arc(int_points[j][2], int_points[j][3], discriminant_points[int_points[j][1]], orientation = arc_orientation)
      next_line = c_line(end_point(next_arc), end_point(gamma))
      pop!(new_path)
      new_path = vcat(new_path, [next_arc, next_line])
    else
      new_line = c_line(start_point(new_path[end]), int_points[j][2])
      V = angle((discriminant_points[int_points[j][1]] - base_point_x) 
      * exp((-1)*angle(end_point(gamma) - base_point_x)*i))
      #In case V = 0, we put the orientation to -1
      arc_orientation = -1
      try
        arc_orientation = sign(Int, V)
      catch
      end

      next_arc = c_arc(int_points[j][2], int_points[j][3], discriminant_points[int_points[j][1]], orientation = arc_orientation)
      next_line = c_line(end_point(next_arc), end_point(gamma))
      pop!(new_path)
      new_path = vcat(new_path, [new_line, next_arc, next_line])
    end
  end
  return new_path
end

#Integrate path to a given end point.
function integrate_on_sheet(paths::Vector{CPath}, end_point_y::AcbFieldElem, RS)

  comp_prec = RS.computational_precision
  CC = AcbField(comp_prec)
  RR = ArbField(comp_prec)
  Cz, z = polynomial_ring(CC)
  Cxy, (x,y) = polynomial_ring(CC,2)
  v = RS.embedding
  fC = embed_mpoly(defining_polynomial(RS), v, comp_prec)
  differentials, fm, mp, rp = differential_form_data(RS)
  embedded_differentials = [embed_mpoly(g, v, comp_prec) for g in differentials]
  err = RS.computational_error
  m = RS.degree[1]
  g = genus(RS)
  dcache = DifferentialFactorCache(embedded_differentials, fm, mp, rp)
  vals = [CC() for _ in 1:1, _ in 1:g]   # one sheet

  dfy = derivative(fC, 2)

  reverse_paths = reverse([ reverse(p) for p in paths ])

  x0 = start_point(reverse_paths[1])
	ys =  sort!(_accurate_roots(fC(x0, z), comp_prec), lt = sheet_ordering)
  dist, ind = closest_point(end_point_y, ys)

  for k in (1:length(reverse_paths))
    path = reverse_paths[k]
    gauss_legendre_path_parameters(RS.discriminant_points, path, RS.computational_error)
    integral_matrix = zero_matrix(CC, 1, g)
    int_schemes = RS.integration_schemes_GL

    for t in (1:length(path.sub_paths))
      subpath = path.sub_paths[t]
      i = maximum(filter(x -> (subpath.int_param_r > int_schemes[x].int_param_r), 1:length(int_schemes));init = 0)
      subpath.integration_scheme_index = i 
      if subpath.integration_scheme_index == 0
        subpath.integration_scheme_index = 1
         if subpath.int_param_r <= RR(1+QQ(1//50))
           r = (1/2)*(subpath.int_param_r+1)
         else
           r = subpath.int_param_r-RR(1/100)
         end
        
        compute_ellipse_bound_heuristic(subpath, embedded_differentials, [r], RS)
        bound = maximum(subpath.bounds)
        pushfirst!(RS.integration_schemes_GL, IntegrationSchemeGL(r, comp_prec+10, RS.computational_error, bound))
       end

			integration_scheme = RS.integration_schemes_GL[subpath.integration_scheme_index]

			path_difference_matrix = zero_matrix(CC, 1, g)
      abscissae = integration_scheme.abscissae
      weights = integration_scheme.weights
      N = length(abscissae)
			An_x, An_y = analytic_continuation(RS, subpath, abscissae, ys, comp_prec)

      # For every path, we compute the integrals for all g differential forms
      # at all m sheets at the same time.
			if path_type(subpath) == 0
				for i in (1:N)
          # For every abscissa we compute the value of the function at that
          # point, multiply it with the correct weight and add it to the
          # intrgral.
					evaluate_differential_factors_matrix!(vals, dcache, An_x[i+1], [An_y[i+1][ind]], CC(weights[i]))
					path_difference_matrix += matrix(CC, vals)
				end
        path_difference_matrix *= evaluate_d(subpath, abscissae[1])
				integral_matrix += path_difference_matrix
        assign_integral_matrix(subpath, path_difference_matrix)
			else
        for i in (1:N)
          # For arcs and circles we need to multiply with an additional dx.
					evaluate_differential_factors_matrix!(vals, dcache, An_x[i+1], [An_y[i+1][ind]], CC(weights[i] * evaluate_d(path, abscissae[i])))
					path_difference_matrix += matrix(CC, vals)
				end
				integral_matrix += path_difference_matrix
			end
      ys = An_y[end]
      paths[1].sheets = [An_y[end][ind]]

		end
    assign_integral_matrix(path, integral_matrix)
    
	end

  for k in (1:length(paths))
    assign_integral_matrix(paths[k], -reverse_paths[end-k+1].integral_matrix)
  end
end

@doc raw"""
    abel_jacobi_map(P::RiemannSurfacePoint, method = "swap", 
    reduction = "complex") -> AcbMatrix

Computes the image of the Abel-Jacobi map of the divisor P - P0 of a Riemann surface where
P0 is the internal base point of the Riemann surface.
"""
function abel_jacobi_map(P::RiemannSurfacePoint, method = "swap", reduction = "complex")
  return abel_jacobi_map(divisor([P],[1]), method, reduction)
end
@doc raw"""
    abel_jacobi_map(P::RiemannSurfacePoint, Q::RiemannSurfacePoint, method = "swap", 
    reduction = "complex") -> AcbMatrix

Computes the image of the Abel-Jacobi map of the divisor P - Q of a Riemann surface.
"""
function abel_jacobi_map(P::RiemannSurfacePoint, Q::RiemannSurfacePoint, method = "swap", reduction = "complex")
  return abel_jacobi_map(divisor([P,Q],[1,-1]), method, reduction)
end

@doc raw"""
    abel_jacobi_map(D::RiemannSurfaceDivisor, P0::RiemannSurfacePoint, method = 
    "swap", reduction = "complex") -> AcbMatrix

Computes the image of the Abel-Jacobi map of the divisor D - d*P0 where d is deg(D).
"""
function abel_jacobi_map(D::RiemannSurfaceDivisor, P0::RiemannSurfacePoint, method = "swap", reduction = "complex")
  return abel_jacobi_map(D - degree(D)*P0, method, reduction)
end

@doc raw"""
    abel_jacobi_map(D::RiemannSurfaceDivisor, method = 
    "swap", reduction = "complex") -> AcbMatrix

Computes the image of the Abel-Jacobi map of the divisor D of a Riemann surface with 
respect to the internal base point P0. I.e. if ``D = \sum_{j=1}^r n_j*D_j`` and given the basis of 
differential forms $\omega_i$ of the Riemann surface, the output matrix AJ(D) is gained by
computing ``\sum_{j=1}^r(n_j* \int_{P0}^{D_j} \omega_i dz)``.

The keyword method can be set to either 'swap' or 'direct'. 
- In the case of "swap", the abel-jacobi map of critical points is computed by swapping to
the Riemann surface f(y,x) = 0 if possible.
- In the case of "direct" the abel-jacobi map of critical points is computed by simply integrating
into the critical point. This method however is heuristic as error bounds at critical points
are not well-defined.

The keyword 'reduction' can be set to either "complex", "real" or "none". 
- In the case of "complex", the output of the abel-jacobi map is given in its image of C^g/(1, tau) where 
tau is the small period matrix of the Riemann surface.
- In the case of "real", the output of the abel-jacobi map is given in R^2g/Z^2g under the natural isomorphism
of the complex torus. 
In the case of "none", the output is given as it is computed.
"""
function abel_jacobi_map(D::RiemannSurfaceDivisor, method = "swap", reduction = "complex")
  V = _abel_jacobi_map(D, method, reduction)
  # the output type chosen for the RiemannSurface (AcbField or ComplexField)
  RS = riemann_surface(D)
  return isdefined(RS, :surface) ? _out(RS.surface, V) : V
end

function _abel_jacobi_map(D::RiemannSurfaceDivisor, method, reduction)
  @req reduction in ["none","real","complex"] "Reduction has to be either 'none', 'real' or 'complex'."
  @req method in ["swap","direct"] "Method has to be either 'swap' or 'direct'."
  RS = riemann_surface(D)
  # A divisor on another model of the same Riemann surface (e.g. points of the
  # curve as given, while the periods are computed on another model): move it
  # to the computational model, whose bases the result refers to.
  if isdefined(RS, :surface)
    C = computational_model(RS.surface)
    if C isa SuperellipticModel
      isdefined(D, :abel_jacobi_value) || (D.abel_jacobi_value = _se_abel_jacobi(C, D))
      reduction == "none" && return D.abel_jacobi_value
      compute_reduction_matrix(C, reduction)
      return reduction == "real" ? period_lattice_reduction_real(D.abel_jacobi_value, C) :
                                   period_lattice_reduction_complex(D.abel_jacobi_value, C)
    end
    if C !== RS
      if !isdefined(D, :abel_jacobi_value)
        big_period_matrix(C)     # before the points are created on C (monodromy as a by-product)
        D2 = _transfer_divisor(D, C)
        _abel_jacobi_map(D2, method, "none")
        D.abel_jacobi_value = D2.abel_jacobi_value
      end
      reduction == "none" && return D.abel_jacobi_value
      compute_reduction_matrix(C, reduction)
      return reduction == "real" ? period_lattice_reduction_real(D.abel_jacobi_value, C) :
                                   period_lattice_reduction_complex(D.abel_jacobi_value, C)
    end
  end
  big_period_matrix(RS)
  g = genus(RS)

  if reduction != "none"
    compute_reduction_matrix(RS, reduction)
  end

  if !isdefined(D, :abel_jacobi_value)
    CC = AcbField(RS.computational_precision)
    RR = ArbField(RS.computational_precision)
    infty = CC(1/0)
    total_complex_integral = zero_matrix(CC,1, g)
    s_to_s_integrals = RS.sheet_to_sheet_integrals
    points, mults = support(D)
    for k in (1:length(points))
      P = points[k] 
      mult = mults[k]
      #Case where the x-coordinate is infinity
      if P.coordx == infty
        s = P.sheets[1]
        @req s in (1:RS.degree[1]) "Error in Abel-Jacobi map."
        if !isdefined(RS, :ajm_infinite_points)
          ajm_DE_special_point(c_infinite_line(RS.base_point.coordx), 0, RS, RS.inf_chain)
        end
        sheet2 = inv(RS.ajm_infinite_points.permutation)[s]
        total_complex_integral += matrix(CC, 1,g, mult * (RS.ajm_infinite_points.integral_matrix[sheet2,:] + s_to_s_integrals[sheet2,:]))
        @warn "Heuristic methods have been used in this computation as the divisor included critical points for which we have no nice error bounds. The output is most likely still correct, but it is not provably correct." maxlog = 1
      else
        #Case where we are dealing with finite singularities and y-infinite points.
        # The special points lie on the chains around the discriminant points
        # (SpecialPoints.jl), and ajm_discriminant_points / ajm_DE_special_point
        # index these chains (RS.pi1_chains). (Not RS.discriminant_points: that
        # list is sorted differently.)
        dist, ind = _disc_chain_index(RS, P.coordx)
        if P.is_singular || P.coordy == infty
          @req contains(dist, RR(0)) "Error in Abel-Jacobi map."
          @req isdefined(P, :sheets) "Error in Abel-Jacobi map."
          if !isassigned(RS.ajm_discriminant_points, ind)
            ajm_discriminant_points(RS, ind)
          end
          disc_chain = RS.ajm_discriminant_points[ind]
          sheet2 = P.sheets[1]
          total_complex_integral += matrix(CC, 1,g, mult * (disc_chain.integral_matrix[sheet2,:] + s_to_s_integrals[sheet2,:]))
          @warn "Heuristic methods have been used in this computation as the divisor included critical points for which we have no nice error bounds. The output is most likely still correct, but it is not provably correct." maxlog = 1
        elseif P in RS.critical_points
          @req contains(dist, RR(0)) "Error in Abel-Jacobi map."
          if method == "direct"
            if !isassigned(RS.ajm_discriminant_points, ind)
              ajm_discriminant_points(RS, ind)
            end
            disc_chain = RS.ajm_discriminant_points[ind]
            # The sheets of a critical point are known (the fiber over it has a
            # multiple root, so it cannot be recomputed with isolated roots).
            @req isdefined(P, :sheets) "Error in Abel-Jacobi map."
            sheet2 = P.sheets[1]
            total_complex_integral += matrix(CC, 1,g, mult * (disc_chain.integral_matrix[sheet2,:] + s_to_s_integrals[sheet2,:]))
            @warn "Heuristic methods have been used in this computation as the divisor included critical points for which we have no nice error bounds. The output is most likely still correct, but it is not provably correct. It may be possible to use the method `swap` for provably correct results." maxlog = 1
          elseif method == "swap"
            swapped_surface(RS)
            Q = RS.swapped_surface([P.coordy, P.coordx])

            O = RS.swapped_surface([RS.base_point.coordy, RS.base_point.coordx])
            O_min_Q = O - Q
            _abel_jacobi_map(O_min_Q, method, "none")
            # (the swapped surface has its own working precision, e.g. from
            #  the magnitude guard bits of accuracy = :big/:both)
            total_complex_integral += mult * change_base_ring(CC, transpose(O_min_Q.abel_jacobi_value))
          else
            error("Unknown method.")
          end                                  
        else                                    
          # Generic finite point (not critical, not singular, not y-infinite)
          row = _ajm_generic_point(RS, P, CC, RR, g)
          total_complex_integral += matrix(CC, 1, g, mult * row)
        end                                     
      end                                       
      D.abel_jacobi_value = transpose(total_complex_integral)
    end
  end
  if reduction == "none"
    return D.abel_jacobi_value
  elseif reduction == "real"
    return period_lattice_reduction_real(D.abel_jacobi_value, RS)
  else
    return period_lattice_reduction_complex(D.abel_jacobi_value, RS)
  end
end

# Index (in RS.pi1_chains) of the chain around the discriminant point closest
# to x, and the distance.
function _disc_chain_index(RS::RiemannSurfaceModel, x::AcbFieldElem)
  return closest_point(x, [center(C) for C in RS.pi1_chains])
end

# Paths from the base point to the starting point of the path whose start is
# closest to x. May be empty (then the end point is the base point).
function _chain_to_closest_start(RS::RiemannSurfaceModel, x::AcbFieldElem)
  _, ind = closest_point(x, RS.ajm_starting_points)
  gens = RS.fundamental_group_of_P1[2]          # all generators, signed path indices
  chains = RS.pi1_chains                        # same order as gens
  for i in eachindex(gens)
    j = findfirst(t -> abs(t) == ind, gens[i])
    j === nothing && continue
    # forward occurrence: stop before the path (its start is the chain point);
    # reversed occurrence: include it (the reversed path ends at the start)
    k = gens[i][j] > 0 ? j - 1 : j
    return chains[i].paths[1:k]
  end
  error("Abel-Jacobi map: no generator of the fundamental group passes through the chosen starting point.")
end

# Contribution of a finite, non-critical point P to the Abel-Jacobi map.
function _ajm_generic_point(RS::RiemannSurfaceModel, P, CC::AcbField, RR::ArbField, g::Int)
  dist0, i0 = closest_point(P.coordx, RS.discriminant_points)
  if contains(dist0, zero(RR))
    return _ajm_regular_point_over_disc(RS, P, i0, CC, RR, g)
  end
  f = complex_defining_polynomial(RS)
  dist, sheet = closest_point(P.coordy, fiber(f, P.coordx))
  @req contains(dist, RR(0)) "Error in Abel-Jacobi map."
  base_point_x = RS.base_point.coordx
  s_to_s = RS.sheet_to_sheet_integrals

  if contains(abs(P.coordx - base_point_x), zero(RR))
    return [s_to_s[sheet, t] for t in 1:g]
  end

  prefix = _chain_to_closest_start(RS, P.coordx)
  x_start = isempty(prefix) ? base_point_x : end_point(prefix[end])

  # line from x_start to P (with detours around the safe circles)
  if contains(abs(P.coordx - x_start), zero(RR))
    sheet_start = sheet
    line_row = [zero(CC) for _ in 1:g]
  else
    path_to_x = find_path_on_sheet(c_line(x_start, P.coordx), RS)
    integrate_on_sheet(path_to_x, P.coordy, RS)
    dist, sheet_start = closest_point(path_to_x[1].sheets[1], fiber(f, x_start))
    @req contains(dist, RR(0)) "Error in Abel-Jacobi map."
    line_row = sum(p.integral_matrix[1, :] for p in path_to_x)
  end

  # chain from the base point to x_start
  if isempty(prefix)
    sheet0 = sheet_start
    chain_row = [zero(CC) for _ in 1:g]
  else
    new_chain = CChain(prefix)
    sheet0 = inv(new_chain.permutation)[sheet_start]
    chain_row = new_chain.integral_matrix[sheet0, :]
  end

  return s_to_s[sheet0, :] + chain_row + line_row
end

# A regular point P (f_y(P) != 0) whose x-coordinate is a discriminant point:
# other sheets meet over x(P), e.g. a point of the swapped surface lying over
# the image of a node. The fiber over x(P) cannot be isolated, so
#     AJ(P) = AJ(P1) + int_{P1}^{P} omega
# for the point P1 over x1 = x(P) + delta on the sheet of P (delta a quarter of
# the distance to the next discriminant point, away from it). y is an analytic
# function of x on the disk around x(P) up to the next discriminant point (P is
# a simple root), so the short integral is done with Gauss-Legendre and y by
# Newton's method along the segment. Heuristic, like the other special points.
function _ajm_regular_point_over_disc(RS::RiemannSurfaceModel, P, i0::Int, CC::AcbField,
                                      RR::ArbField, g::Int)
  prec = precision(CC)
  f = complex_defining_polynomial(RS, prec)
  fy = derivative(f, 2)
  x0 = CC(P.coordx)
  y0 = CC(P.coordy)
  @req !contains(fy(x0, y0), zero(CC)) "Error in Abel-Jacobi map: the point is critical."
  newton(x, y) = (for _ in 1:(ceil(Int, log2(prec)) + 4); y = _acb_mid(y - f(x, y)/fy(x, y)); end; y)

  D = RS.discriminant_points
  others = [CC(d) for (j, d) in enumerate(D) if j != i0]
  if isempty(others)
    delta, dir = RR(1)/4, one(CC)
  else
    rho, j = closest_point(x0, others)
    delta, dir = rho/4, (x0 - others[j])/abs(x0 - others[j])
  end
  x1 = _acb_mid(x0 + delta*dir)

  # y at x1 on the sheet of P: Newton in a few steps along the segment, then
  # the exact root of the (isolated) fiber over x1
  y = y0
  for k in 1:8
    y = newton(x0 + (x1 - x0)*QQ(k, 8), y)
  end
  ys1 = fiber(f, x1)
  _, s1 = closest_point(y, ys1)
  y1 = ys1[s1]
  row1 = _ajm_generic_point(RS, RS([x1, y1]), CC, RR, g)

  # int_{x1}^{x0} omega on the sheet of P
  N = Int(gauss_legendre_parameters(ArbField(prec)(4), RS.computational_error))
  abscissae, weights = gauss_legendre_integration_points(N, prec)
  factors = [embed_mpoly(q, RS.embedding, prec) for q in differential_form_data(RS)[1]]
  half = (x0 - x1)/2
  mid = (x0 + x1)/2
  integral = [zero(CC) for _ in 1:g]
  y = y0
  for k in sortperm(abscissae, by = t -> -_arb_mid_f64(t))   # from x0 towards x1
    x = mid + half*abscissae[k]
    y = newton(x, y)
    vals = evaluate_differential_factors_matrix(RS, factors, x, [y])
    for t in 1:g
      integral[t] += weights[k]*vals[1, t]*half
    end
  end
  return [row1[t] + integral[t] for t in 1:g]
end

#Compute the Abel-Jacobi map from the basepoint to a special point
#on all sheets using double-exponential integration. 

#Used for singular points, infinite points and y-infinite points.
#Can also be used for other critical points if the method `direct` is used.

#Note: This method is heuristic as we do not have proper error bounds.
#(Double exponential-integration is used because it is probably the 
#best method to compute problematic integrals).

#I opted not implement the algorithm in an adaptive way as the analytic continuation
#is not stable enough for this. (It works better when everything gets recomputed every iteration.)
#A potential speed increase would be to cut the path into two parts: 
# - A part that does not contain the integral to the problematic point and can be computed
# rigorously.
# - The second half of the integral computed as it is now.
#The question would be to decide where the cutoff point should be. Maybe a first probe using 
#analytic continuation could be helpful.
function ajm_DE_special_point(gamma::CPath, k::Int, RS::RiemannSurfaceModel, test_chain::CChain, max_iterations = 5)
        
  prec = RS.computational_precision
  new_prec = true
  go_on = true

  iterations = 1

  CC = complex_field(RS)

  if k == 0   #Point at infinity
    c = maximum([ length(cycle) for cycle in  collect(cycles(permutation(RS.inf_chain))) ])+1
  else
    c = maximum([ length(cycle) for cycle in  collect(cycles(permutation(RS.pi1_chains[k]))) ])+1
  end
  
  comp_error = RS.computational_error
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
    differentials, fm, mp, rp = differential_form_data(RS)
    embedded_differentials = [embed_mpoly(g, v, comp_prec) for g in differentials]
    # Built once per refinement round instead of once per abscissa
    ws = ContinuationWorkspace(_split_in_y(fC), Cz)
    dcache = DifferentialFactorCache(embedded_differentials, fm, mp, rp)
    vals = [CC() for _ in 1:m, _ in 1:g]

    if k == 0 #Point at infinity
      N_gamma = gamma
      err2 = (RR(1/2)*comp_error^(c+1))^2
    else
      N_gamma = c_line(CC(start_point(gamma)),CC(end_point((gamma))))
      err2 = comp_error^2/4
    end

    N = round(Int, 1//h * 72 //10)
    N2P1 = 2*N+1
    abscissae, weights = tanh_sinh_quadrature_integration_points(N, RR(h))
    push!(abscissae,RR(1))
    xj = start_point(N_gamma)
		yj =  sort!(_accurate_roots(fC(xj, z), comp_prec), lt = sheet_ordering)
    yj_new = yj

    path_difference_matrix = zero_matrix(CC, m, g)
    for i in (1:N2P1)
      xj_new = evaluate(N_gamma, abscissae[i+1])
      #Integrating into infnity gives problems when trying to do it with the more 
      #rigorous recursive_continuation. Therefore we forego the precision check and
      #use a sanity check later on to check if our result is heuristically correct.
      try
        yj_new, new_prec = recursive_continuation_manual!(ws, xj, xj_new, yj, err2, target_error)
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

      # weight (times dx) is folded into the evaluation
      wi = CC(weights[i] * evaluate_d(N_gamma, abscissae[i]))
      evaluate_differential_factors_matrix!(vals, dcache, xj, yj, wi)
      integral_matrix_contribution = matrix(CC, vals)
      
      max_abs = maximum([abs(c) for c in integral_matrix_contribution])
      if (i > N && max_abs < comp_error)
        break
      end

      xj = xj_new
      yj = yj_new
      
			path_difference_matrix += integral_matrix_contribution
		end

    assign_integral_matrix(N_gamma, path_difference_matrix)
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
        if s == 1
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
    assign_integral_matrix(gamma, final_gamma.integral_matrix)
    gamma.sheets = yj_new
    assign_permutation(gamma, permutation(final_gamma))
  end
end

#Apply ajm_DE_discriminant_point to all critical points.
function ajm_discriminant_points(RS::RiemannSurfaceModel, k::Int)
  chain = RS.pi1_chains[k]
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
