################################################################################
#
#  RieSrf/Surface/Discriminant.jl : discriminant points
#
#  The discriminant points of the projection (x, y) -> x: the roots of the
#  discriminant of f with respect to y and of the leading coefficient of f in
#  y. They are computed from the exact factors, with a precision that adapts
#  to the curve (see _ensure_discriminant_points!), together with the
#  internal precision of the model.
#
#  Entry points: discriminant_points, internal_discriminant_points,
#  discriminant_points_high_prec.
#
################################################################################

# The discriminant points (at 660 bits for the user, at _path_point_precision
# for the paths) and the internal precision: the working precision plus the
# bits of a bound for |y| and the differentials near the discriminant points
# (Neurohr's bound).
function _ensure_discriminant_points!(RS::RiemannSurfaceModel)
  isdefined(RS, :discriminant_points) && return nothing
  f = defining_polynomial_univariate(RS)
  v = embedding(RS)
  g = genus(RS)
  a0 = leading_coefficient(f)
  RR = ArbField(precision(RS))
  disc_points, _, lc_points = _discriminant_points_to_prec(RS, 660)
  RS.discriminant_points = disc_points

  x_bound = maximum(abs(P) for P in disc_points) + RR(_max_radius(RS))
  # the distance of the circles around the roots of the leading coefficient
  if isempty(lc_points)
    lc_safe_radius = RR(1)
  else
    lc_distance = minimum([closest_point(P, collect(setdiff(disc_points, Set([P]))))[1] for P in lc_points])
    lc_safe_radius = minimum([_radius_factor(RS)*lc_distance, RR(_max_radius(RS))])
  end

  low_prec = 66
  f_low_prec = _embed_mpoly(defining_polynomial(RS), v, low_prec)
  R_low_prec = ArbField(low_prec)
  _, x = polynomial_ring(AcbField(low_prec), "x")

  # A bound for |y| on f(x, y) = 0 for |x| < xb and |x - x_0| > dist for all
  # roots x_0 of the leading coefficient.
  function bound_y_values(xb, dist)
    coeffs_y = [c(x, 0) for c in reverse(coefficients(f_low_prec, 2))]
    a0_leading = abs(_embed_coefficient(leading_coefficient(a0), v.embedding, low_prec))
    max_y_abs = R_low_prec(0)
    max_x_abs = R_low_prec(0)
    for k in 1:RS.degree[1]-1
      coeffs_x = coefficients(coeffs_y[k+1])
      Ak = sum([abs(coeffs_x[j]) * xb^j for j in 0:length(coeffs_x)-1]; init = R_low_prec(0))
      max_y_abs = maximum([max_y_abs, Ak/(a0_leading*dist^degree(a0))^(1/k)])
      max_x_abs = maximum([max_x_abs, Ak])
    end
    return maximum([2*max_y_abs, max_x_abs])
  end
  y_bound = bound_y_values(x_bound, (100/101)*lc_safe_radius)

  # bounds for the factors of the differentials and for the differentials
  factors, factor_matrix, min_pows, range_pows = differential_form_data(RS)
  embedded_factors = [_embed_mpoly(h, v, low_prec) for h in factors]
  factor_bounds = ArbFieldElem[]
  for h in embedded_factors
    coeffs = collect(coefficients(h))
    mons = collect(monomials(h))
    value = abs(sum([abs(coeffs[j]) * mons[j](x_bound, y_bound) for j in 1:length(coeffs)]; init = R_low_prec(0)))
    push!(factor_bounds, maximum([value, R_low_prec(1)]))
  end
  differential_bounds = [R_low_prec(1) for _ in 1:g]
  for l in 1:length(factors)
    power_bounds = [R_low_prec(1) for _ in 1:range_pows[l]+1]
    for k in 0:range_pows[l]
      if min_pows[l] + k > 0
        power_bounds[k+1] = factor_bounds[l]^(min_pows[l] + k)
      end
    end
    for k in 1:g
      differential_bounds[k] *= power_bounds[factor_matrix[l, k] - min_pows[l] + 1]
    end
  end
  bound = maximum(vcat(factor_bounds, [y_bound], differential_bounds))

  additional_prec = ceil(Int, log(bound)/log(2))
  internal_prec = RS.computational_precision + maximum([additional_prec, 67])
  RS.internal_precision = internal_prec

  # The paths only need the points at a moderate precision; the Abel-Jacobi
  # map at points above discriminant points needs degree_y * internal_prec
  # (Neurohr), which is computed only on demand (discriminant_points_high_prec).
  # (Isolating the roots at that precision was ~15% of the time for f19.)
  path_prec = _path_point_precision(internal_prec)
  if path_prec > 660
    disc_points = _discriminant_points_to_prec(RS, path_prec)[1]
  end
  RS.discriminant_points_internal = disc_points

  RS.ajm_discriminant_points = Vector{CChain}(undef, length(disc_points))
  _compute_disc_factor_data!(RS)
  return nothing
end

@doc raw"""
    discriminant_points(RS::RiemannSurfaceModel, copy::Bool = true) -> Vector{AcbFieldElem}

The roots of the discriminant and of the leading coefficient of the defining
polynomial f as a polynomial in y, sorted by `sheet_ordering`.
"""
function discriminant_points(RS::RiemannSurfaceModel, copy::Bool = true)
  _ensure_discriminant_points!(RS)
  if copy
    return deepcopy(RS.discriminant_points)
  else
    return RS.discriminant_points
  end
end

# The discriminant points at the precision of the paths (_path_point_precision);
# their order is the one used by the paths and chains.
function internal_discriminant_points(RS::RiemannSurfaceModel, copy::Bool = true)
  _ensure_discriminant_points!(RS)
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
      rts = roots(_embed_poly(p, v, q), initial_prec = q, max_prec = 8*q)
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
  _ensure_discriminant_points!(RS)
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

# All discriminant points (sorted), the roots of the discriminant and the
# roots of the leading coefficient, at precision prec.
function _discriminant_points_to_prec(RS::RiemannSurfaceModel, prec::Int)
  v = embedding(RS)
  disc_factors, lc_factors = _discriminant_factors(RS)
  disc_roots = vcat(AcbFieldElem[], [_isolated_roots(p, v, prec) for p in disc_factors]...)
  lc_roots = vcat(AcbFieldElem[], [_isolated_roots(p, v, prec) for p in lc_factors]...)
  return sort!(union(disc_roots, lc_roots), lt = sheet_ordering), disc_roots, lc_roots
end
