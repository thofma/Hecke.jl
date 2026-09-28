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

    # The paths only need the points at a moderate precision; the Abel-Jacobi
    # map at points above discriminant points needs degree_y * internal_prec
    # (Neurohr), which is computed only on demand (discriminant_points_high_prec).
    # (Isolating the roots at that precision was ~15% of the time for f19.)
    path_prec = _path_point_precision(internal_prec)
    if path_prec > 660
      D_points = _discriminant_points_to_prec(RS, path_prec)[1]
    end

    RS.discriminant_points_internal = D_points

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
    return deepcopy(RS.discriminant_points_internal)
  else
    return RS.discriminant_points_internal
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

# Roots of an exact (squarefree) factor, embedded via v. If the roots cannot
# be isolated from the coefficients at precision prec (large coefficients,
# clustered roots), a higher working precision in the root finder does not
# help since the input balls stay the same: embed the factor again at twice
# the precision.
function _isolated_roots(p, v, prec::Int)
  q = prec
  while true
    try
      rts = roots(embed_poly(p, v, q), initial_prec = q, max_prec = 8*q)
      q == prec && return rts
      CC = AcbField(prec)
      return AcbFieldElem[CC(r) for r in rts]
    catch e
      (e isa ErrorException && startswith(e.msg, "unable to isolate all roots") &&
       q < 64*prec) || rethrow()
      q *= 2
    end
  end
end

# Precision of the discriminant points used for the paths. Twice the internal
# precision (working precision + bound bits) leaves room for a later increase
# of the working precision (magnitude guard bits, precision retry) without
# recomputing the paths.
_path_point_precision(internal_prec::Int) = 2 * internal_prec

# The discriminant points at degree_y * internal precision, in the order of
# internal_discriminant_points (the indices are shared with the chains and
# the safe radii). Computed on first use (Abel-Jacobi map).
function discriminant_points_high_prec(RS::RiemannSurfaceModel)
  isdefined(RS, :discriminant_points_high_prec) && return RS.discriminant_points_high_prec
  assure_has_discriminant_points(RS)
  D = RS.discriminant_points_internal
  p = RS.degree[1] * RS.internal_precision
  if p <= precision(parent(D[1]))
    RS.discriminant_points_high_prec = D
    return D
  end
  H = _discriminant_points_to_prec(RS, p)[1]
  @req length(H) == length(D) "Could not match the discriminant points at high precision."
  # match to the order of D (each high precision point lies in exactly one
  # of the balls of D, or is closest to it)
  Dhi = Vector{AcbFieldElem}(undef, length(D))
  taken = falses(length(D))
  Dm = [_c64(z) for z in D]
  for h in H
    hf = _c64(h)
    cand = [i for i in eachindex(D) if !taken[i] && overlaps(h, D[i])]
    i = length(cand) == 1 ? cand[1] :
        argmin([taken[i] ? Inf : abs(hf - Dm[i]) for i in eachindex(D)])
    @req !taken[i] "Could not match the discriminant points at high precision."
    taken[i] = true
    Dhi[i] = h
  end
  RS.discriminant_points_high_prec = Dhi
  return Dhi
end

function _discriminant_points_to_prec(RS::RiemannSurfaceModel, prec::Int)
    v = embedding(RS)
    disc_facs, a0_facs = _discriminant_factors(RS)
    D1 = vcat(AcbFieldElem[], [_isolated_roots(p, v, prec) for p in disc_facs]...)
    D2 = vcat(AcbFieldElem[], [_isolated_roots(p, v, prec) for p in a0_facs]...)
    D_points = sort!(union(D1, D2), lt = sheet_ordering)
    return D_points, D1, D2
  end
