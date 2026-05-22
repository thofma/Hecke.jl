
#Transform the output of the Abel-Jacobi map to an element of R^(2g)/Z^(2g)
#under the canonical isomorphism.
function period_lattice_reduction_real(V::AcbMatrix, RS::RiemannSurface)
  g = genus(RS)
  T = RS.real_reduction_matrix
  RR = base_ring(T)
  W = vcat(real(V), imag(V))
  W = T*W
  return matrix(RR, 2*g, 1, [w - round(ZZRingElem, w) for w in W])
end

#Transform the output of the Abel-Jacobi map to an element of C^g/(1, tau)
#under the canonical isomorphism.
function period_lattice_reduction_complex(V::AcbMatrix, RS::RiemannSurface)
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
function find_path_on_sheet(gamma::CPath, RS::RiemannSurface)

  @req path_type(gamma) == 0 "Path needs to be a line."
  int_points = Tuple{Int64, AcbFieldElem, AcbFieldElem}[]
  discriminant_points = RS.discriminant_points_high_prec
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
      new_line = c_line(start_point(new_path[end]), integration_points[j][2])
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

  extra_prec = RS.extra_prec
  CC = AcbField(extra_prec)
  RR = ArbField(extra_prec)
  Cz, z = polynomial_ring(CC)
  Cxy, (x,y) = polynomial_ring(CC,2)
  v = RS.embedding
  fC = embed_mpoly(defining_polynomial(RS), v, extra_prec)
  differentials = RS.differential_form_data[1]
  embedded_differentials = [embed_mpoly(g, v, extra_prec) for g in differentials]
  err = RS.extra_error
  m = RS.degree[1]
  g = genus(RS)

  dfy = derivative(fC, 2)

  

  reverse_paths = reverse([ reverse(p) for p in paths ])

  x0 = start_point(reverse_paths[1])
	ys =  sort!(roots(fC(x0, z), initial_prec = extra_prec), lt = sheet_ordering)
  dist, ind = closest_point(end_point_y, ys)



  for k in (1:length(reverse_paths))
    path = reverse_paths[k]
    gauss_legendre_path_parameters(RS.discriminant_points, path, RS.extra_error)
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
        pushfirst!(RS.integration_schemes_GL, IntegrationSchemeGL(r, extra_prec+10, RS.extra_error, bound))
       end

			integration_scheme = RS.integration_schemes_GL[subpath.integration_scheme_index]

			path_difference_matrix = zero_matrix(CC, 1, g)
      abscissae = integration_scheme.abscissae
      weights = integration_scheme.weights
      N = length(abscissae)
			An_x, An_y = analytic_continuation(RS, subpath, abscissae, ys)

      # For every path, we compute the integrals for all g differential forms
      # at all m sheets at the same time.
			if path_type(subpath) == 0
				for i in (1:N)
          # For every abscissa we compute the value of the function at that
          # point, multiply it with the correct weight and add it to the
          # intrgral.
					integral_matrix_contribution = evaluate_differential_factors_matrix(RS, embedded_differentials, An_x[i+1], [An_y[i+1][ind]])
					integral_matrix_contribution = change_base_ring(CC, integral_matrix_contribution)
          integral_matrix_contribution *= weights[i]
					path_difference_matrix += integral_matrix_contribution
				end
        path_difference_matrix *= evaluate_d(subpath, abscissae[1])
				integral_matrix += path_difference_matrix
        subpath.integral_matrix = path_difference_matrix
			else
        for i in (1:N)
					integral_matrix_contribution = evaluate_differential_factors_matrix(RS, embedded_differentials, An_x[i+1], [An_y[i+1][ind]])
          integral_matrix_contribution = change_base_ring(CC, integral_matrix_contribution)
          # For arcs and circles we need to multiply with an additional dx.
          integral_matrix_contribution *= weights[i] * evaluate_d(path, abscissae[i])
					path_difference_matrix += integral_matrix_contribution
				end
				integral_matrix += path_difference_matrix
			end
      ys = An_y[end]
      paths[1].sheets = [An_y[end][ind]]

        # Copied from monodromy_representation to compute the monodromy representation
        # we just computed while computing periods.
       # There is probably a more clever way to avoid doubling code.
      #path_perm = sortperm(An[end][2], lt = sheet_ordering)
      #assign_permutation(path, inv(s_m(path_perm)))
		end
    path.integral_matrix = integral_matrix
    
	end

    

  for k in (1:length(paths))
    paths[k].integral_matrix = -reverse_paths[end-k+1].integral_matrix
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
function abel_jacobi_map( D::RiemannSurfaceDivisor, method = "swap", reduction = "complex")
  @req reduction in ["none","real","complex"] "Reduction has to be either 'none', 'real' or 'complex'."
  @req method in ["swap","direct"] "Method has to be either 'swap' or 'direct'."
  RS = riemann_surface(D)
  g = genus(RS)

  if reduction != "none"
    compute_reduction_matrix(RS, reduction)
  end

  if !isdefined(D, :abel_jacobi_value)
    CC = AcbField(RS.extra_prec)
    RR = ArbField(RS.extra_prec)
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
        println("Warning: Heuristic methods have been used in this computation as the divisor included critical points for which we have no nice error bounds. The output is most likely still correct, but it is not provably correct.")
      else
        #Case where we are dealing with finite singularities and y-infinite points.
        dist, ind = closest_point(P.coordx, RS.discriminant_points)
        if P.is_singular || P.coordy == infty
          @req contains(dist, RR(0)) "Error in Abel-Jacobi map."
          @req isdefined(P, :sheets) "Error in Abel-Jacobi map."
          if !isassigned(RS.ajm_discriminant_points, ind)
            ajm_discriminant_points(RS, ind)
          end
          disc_chain = RS.ajm_discriminant_points[ind]
          sheet2 = P.sheets[1]
          total_complex_integral += matrix(CC, 1,g, mult * (disc_chain.integral_matrix[sheet2,:] + s_to_s_integrals[sheet2,:]))
          println("Warning: Heuristic methods have been used in this computation as the divisor included critical points for which we have no nice error bounds. The output is most likely still correct, but it is not provably correct.")
        elseif P in RS.critical_points
          @req contains(dist, RR(0)) "Error in Abel-Jacobi map."
          if method == "direct"
            if !isassigned(RS.ajm_discriminant_points, ind)
              ajm_discriminant_points(RS, ind)
            end
            disc_chain = RS.ajm_discriminant_points[ind]

            fiber_x = fiber(complex_defining_polynomial(RS), P.coordx)

            dist2, sheet = closest_point(P.coordy, fiber_x)
            @req contains(dist, RR(0)) "Error in Abel-Jacobi map."
            sheet2 = sheet
            total_complex_integral += matrix(CC, 1,g, mult * (disc_chain.integral_matrix[sheet2,:] + s_to_s_integrals[sheet2,:]))
            println("Warning: Heuristic methods have been used in this computation as the divisor included critical points for which we have no nice error bounds. The output is most likely still correct, but it is not provably correct. It may be possible to use the method `swap` for provably correct results.")
          elseif method == "swap"
            swapped_surface(RS)
            Q = RS.swapped_surface([P.coordy, P.coordx])
        

            O = RS.swapped_surface([RS.base_point.coordy, RS.base_point.coordx])
            O_min_Q = O - Q
            V = abel_jacobi_map(O_min_Q, method, "none")
            total_complex_integral += mult * transpose(O_min_Q.abel_jacobi_value)
          else
            error("Unknown method.")
          end
        else
          #Base point?
          f = complex_defining_polynomial(RS)
          fiber_x = fiber(f, P.coordx)
          dist2, sheet = closest_point(P.coordy, fiber_x)
          @req contains(dist2, RR(0)) "Error in Abel-Jacobi map."
          base_point_x = RS.base_point.coordx
          if contains(abs(P.coordx-base_point_x), zero(RR)) 
            total_complex_integral += matrix(CC, 1,g, mult * s_to_s_integrals[sheet,:])
          else
            #Find starting point of path closest to P
            dist, ind = closest_point(P.coordx, RS.ajm_starting_points)
            # Find suitable closed chain
            closed_chains = RS.closed_chains
            paths, path_indices = RS.fundamental_group_of_P1
            for i in (1:length(closed_chains))
              chain = closed_chains[i]
              j = findfirst(x -> x == ind, path_indices[i])
              if j != nothing
                if j == 1
                  path_to_x = [ c_line(base_point_x, P.coordx) ]
                  integrate_on_sheet(path_to_x, P.coordy, RS)
                  dist, sheet2 = closest_point(path_to_x[1].sheets[1], fiber(f, base_point_x))
                  @req contains(dist, RR(0)) "Error in Abel-Jacobi map."
                  total_complex_integral += matrix(CC, 1,g, mult * (s_to_s_integrals[sheet2,:] + (path_to_x[1].integral_matrix[1,:])))
                else
                  new_chain = CChain(chain.paths[1:j-1])
                  if !contains(dist, RR(0))
                    path_to_x = find_path_on_sheet(c_line(end_point(new_chain.paths[j-1]), P.coordx), RS)
                    integrate_on_sheet(path_to_x, P.coordy, RS)
                    dist, sheet2 = closest_point(path_to_x[1].sheets[1], fiber(f, end_point(new_chain.paths[j-1])))
                    sigma = new_chain.permutation
                    sheet2 = inv(sigma)[sheet2]
                    @req contains(dist, RR(0)) "Error in Abel-Jacobi map."
                    

                    total_complex_integral += matrix(CC, 1,g, mult * (s_to_s_integrals[sheet2,:] + new_chain.integral_matrix[sheet2,:] + sum([ path.integral_matrix[1,:] for path in path_to_x])))
                  else
                    sigma = new_chain.permutation
                    sheet2 = inv(sigma)[sheet]
                    total_complex_integral += matrix(CC, 1,g, mult * (s_to_s_integrals[sheet2] + new_chain.integral_matrix[sheet2,:]))
                  end
                end
                break
              end
            end
          end
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

