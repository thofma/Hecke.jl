
@doc raw"""
    weighted_equality(w1::Vector{T},w2::Vector{T}, ws::Vector{Int}) -> Bool

Given two points w1 and w2 in weighted projective space P with weights ws,
return true when w1 and w2 are equal.
"""
function weighted_equality(w1::Vector{T},w2::Vector{T}, ws::Vector{Int}) where T
#Only consider invertible elements
  non_zero = findall(is_unit, w1)
  if non_zero != findall(is_unit, w2)
    return false
  end
  isempty(non_zero) && return true

  # The points are equal iff w2[i] = lambda^ws[i] * w1[i] for all i. Get
  # mu = lambda^g, g the gcd of the weights, by the Euclidean algorithm on the
  # exponents. For equal points every intermediate value is lambda^e with
  # e <= maximum(ws); Bezout coefficients would blow up the entries instead.
  ratio(i) = divexact(w2[i], w1[i])
  e, mu = ws[non_zero[1]], ratio(non_zero[1])
  for i in non_zero[2:end]
    f, nu = ws[i], ratio(i)
    while f != 0
      q, r = divrem(e, f)
      e, mu, f, nu = f, nu, r, mu * inv(nu)^q
    end
  end

  for i in non_zero
    ratio(i) == mu^divexact(ws[i], e) || return false
  end
  return true
end

@doc raw"""
    weighted_multiply(w1::Vector{T}, ws::Vector{Int}, lambda::T) -> Vector{T}

Given a point w1 in weighted projective space P over the rationals with
weights ws, scale the invariants by the scalar lambda.
"""
function weighted_multiply(w1::Vector{T}, ws::Vector{Int}, lambda::T) where T <: FieldElem

    for i in (1:length(ws))
      w1[i] *= lambda^ws[i]
    end

    return w1
end

@doc raw"""
    weighted_reduction(w1::Vector{QQFieldElem}, ws::Vector{Int}) -> Vector{QQFieldElem}

Given a point w1 in weighted projective space P over the rationals with
weights ws, return the smallest equivalent point with integral coefficients.
"""
function weighted_reduction(w1::Vector{QQFieldElem}, ws::Vector{Int})

    #Clear the denominators
    dens = map(denominator, w1)
    den_lcm = lcm(dens)
    w1_integral = map(ZZ,[den_lcm^(ws[k]) * w1[k] for k in (1:length(w1))])

    primes = [ p for (p,e) in factor(gcd(w1_integral)) ]

    w1_min = w1_integral

    non_zero_i = filter(k -> w1_min[k]!=0, (1:length(w1_min)))

    #Divide out any common prime factors
    for p in primes
	    while all([valuation(w1_min[k], p) >= ws[k] for k in non_zero_i ])
        for k in non_zero_i
	        w1_min[k] = divexact(w1_min[k], p^ws[k])
        end
	    end
    end

    return w1_min
end
