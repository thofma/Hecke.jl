################################################################################
#
#  RieSrf/Discriminant.jl : discriminant points
#
################################################################################

function assure_has_discriminant_points(RS::RiemannSurfaceModel)
  if isdefined(RS, :discriminant_points)
    return nothing
  else

    f = defining_polynomial_univariate(RS)
    Kxy = parent(f)
    Kx = base_ring(f)

    v = embedding(RS)

    g = genus(RS)
    a0 = leading_coefficient(f)
    RR = ArbField(precision(RS))
    D_points, D1, D2 = _discriminant_points_to_prec(RS, 660)
    RS.discriminant_points = D_points
    v = embedding(RS)

    XB = maximum(abs(P) for P in D_points) + RR(max_radius(RS))

    if length(D2) == 0
      L0_safe_radius = RR(1)
    else
      D2_distance = minimum([closest_point(P, collect(setdiff(D_points, Set([P]))) )[1] for P in D2])
      L0_safe_radius = minimum([radius_factor(RS)*D2_distance, RR(max_radius(RS))])
    end

    low_prec = 66
    f_low_prec = embed_mpoly(defining_polynomial(RS), v, low_prec)
    C_low_prec = AcbField(low_prec)
    R_low_prec = ArbField(low_prec)
    R, x = polynomial_ring(C_low_prec, "x")

    #Bounds |y(x)| on f(x,y) = 0 for |x| < xb and |x-x_0| > dist for all zeros x_0 of LC */
    function bound_y_values(xb, dist)
      coeffs_y = reverse(coefficients(f_low_prec,2))
      coeffs_y = [ c(x, 0) for c in coeffs_y ]
      max_y_abs = R_low_prec(0)
      max_x_abs = R_low_prec(0)
      for k in (1:RS.degree[1]-1)
        coeffs_x = coefficients(coeffs_y[k+1])
        if length(coeffs_x) >= 0
                Ak = sum([ abs(coeffs_x[j]) * xb^(j) for j in (0:length(coeffs_x)-1) ]; init = R_low_prec(0))
                max_y_abs = maximum([max_y_abs, Ak/(abs(evaluate(leading_coefficient(a0), v.embedding, low_prec)*dist^degree(a0)))^(1/k)])
                max_x_abs = maximum([max_x_abs, Ak])
        end
      end
      return maximum([2*max_y_abs, max_x_abs])
    end
    YB = bound_y_values(XB, (100/101)*L0_safe_radius)
    DF_data = differential_form_data(RS)
    DFF = DF_data[1]
    DFF_emb = [embed_mpoly(g, v, low_prec) for g in DFF]
    max_diff_abs = ArbFieldElem[]
    for k in (1:length(DFF))
      omega = DFF_emb[k]
      coeffs = collect(coefficients(omega))
      mons = collect(monomials(omega))
      val = abs(sum([ abs(coeffs[j]) * mons[j](XB,YB) for j in (1:length(coeffs))];init = R_low_prec(0)))
      push!(max_diff_abs, maximum([val,R_low_prec(1)]))
    end
    one_vec = [R_low_prec(1) for i in (1:g)]
    for l in (1:length(DFF))
      val = max_diff_abs[l]
      fac_xys = [R_low_prec(1) for i in (1:DF_data[4][l]+1)]
      for k in (0:DF_data[4][l])
        if DF_data[3][l]+k <= 0 
          fac_xys[k+1] = R_low_prec(1)
        else
          fac_xys[k+1] = max_diff_abs[l]^(DF_data[3][l]+k)
        end
      end
      for k in (1:g)
        one_vec[k] *= fac_xys[DF_data[2][l, k]-DF_data[3][l]+1]
      end
    end
    bound = maximum(vcat(max_diff_abs, [YB], one_vec))

    additional_prec = ceil(Int, log(bound)/log(2))
    internal_prec = RS.computational_precision + maximum([additional_prec, 67])
    RS.internal_precision = internal_prec

    precision_for_DP = RS.degree[1] * internal_prec

    if precision_for_DP > 660
      D_points = _discriminant_points_to_prec(RS, precision_for_DP)[1]
    end

    RS.discriminant_points_high_prec = D_points

    RS.ajm_discriminant_points = Vector{CChain}(undef, length(D_points))
    _compute_disc_factor_data!(RS)

    return nothing
  end
end

@doc raw"""
function discriminant_points(RS::RiemannSurfaceModel, copy::Bool = true) -> Vector{AcbFieldElem}

Let f be the defining polynomial of the Riemann surface RS. 
Return the set of roots of the discriminant (and the leading coeﬃcients) of f as
a polynomial in y.
"""
function discriminant_points(RS::RiemannSurfaceModel, copy::Bool = true)
  assure_has_discriminant_points(RS)
  if copy
    return deepcopy(RS.discriminant_points)
  else
    return RS.discriminant_points
  end
end

function internal_discriminant_points(RS::RiemannSurfaceModel, copy::Bool = true)
  assure_has_discriminant_points(RS)
  if copy
    return deepcopy(RS.discriminant_points_high_prec)
  else
    return RS.discriminant_points_high_prec
  end
end

# The factors (in K[x]) of the discriminant of f with respect to y and of the
# leading coefficient of f in y. Computed once: the discriminant is expensive
# for large degrees and is needed several times.
function _discriminant_factors(RS::RiemannSurfaceModel)
  if !isdefined(RS, :discriminant_factors)
    f = defining_polynomial_univariate(RS)
    RS.discriminant_factors = ([p for (p, _) in factor(discriminant(f))],
                               [p for (p, _) in factor(leading_coefficient(f))])
  end
  return RS.discriminant_factors
end

function _discriminant_points_to_prec(RS::RiemannSurfaceModel, prec::Int)
    v = embedding(RS)
    disc_facs, a0_facs = _discriminant_factors(RS)
    disc_y_factors = AcbPolyRingElem[embed_poly(p, v, prec) for p in disc_facs]
    a0_factors = AcbPolyRingElem[embed_poly(p, v, prec) for p in a0_facs]

    D1 = vcat(AcbFieldElem[],[roots(fac, initial_prec = prec, max_prec = 8*prec) for fac in disc_y_factors]...)
    D2 = vcat(AcbFieldElem[],[roots(fac, initial_prec = prec, max_prec = 8*prec) for fac in a0_factors]...)
    D_points = sort!(union(D1, D2), lt = sheet_ordering)
    return D_points, D1, D2
  end
