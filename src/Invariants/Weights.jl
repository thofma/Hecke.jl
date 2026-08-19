
@doc raw"""
    weighted_equality(w1::Vector{T},w2::Vector{T}, ws::Vector{Int}) -> Bool

Given two points w1 and w2 in weighted projective space P with weights ws,
return true when w1 and w2 are equal.
"""
function weighted_equality(w1::Vector{T},w2::Vector{T}, ws::Vector{Int}) where T
#Only consider invertible elements
  non_zero = findall(map(is_unit, w1))
  non_zero_w2 = findall(map(is_unit, w2))

  if non_zero != non_zero_w2
    return false
  end

#Compute gcd of the weights
  _gcd_ws, B_coeffs = gcdx(Vector{ZZRingElem}(ws[non_zero]))
  gcd_ws = Int(_gcd_ws)

# Use Bezout coefficients to the scaling factors to get equality for an
# invariant whose weight is equal to the gcd of the weights.
# I.e. we want gcd_w1_scaling * gcd_w1 = gcd_w2_scaling * gcd_w2
# where gcd_wi is the value gotten by applying the B_coeffs to wi to
# get an invariant of weight gcd_w.
  gcd_w1_scaling = 1
  gcd_w2_scaling = 1
  for j in 1:length(non_zero)
	  if B_coeffs[j] >= 0
	    gcd_w2_scaling *= w1[non_zero[j]]^B_coeffs[j]
	    gcd_w1_scaling *= w2[non_zero[j]]^B_coeffs[j]
	  else
	    gcd_w2_scaling *= w2[non_zero[j]]^(-B_coeffs[j])
	    gcd_w1_scaling *= w1[non_zero[j]]^(-B_coeffs[j])
	  end
  end

  #Factor the weights by gcd_ws
  pows = [[i, div(ws[i], gcd_ws)] for i in non_zero]

  sort(pows, by = (x-> x[2]))

  w2_scaling_factor = 1
  w1_scaling_factor = 1
  pow = 0

  #For every weight we scale by an apprioriate multiple and test for equality
  for p in pows
	  if p[2] != pow
	    w2_scaling_factor *= gcd_w2_scaling^(p[2]-pow)
	    w1_scaling_factor *= gcd_w1_scaling^(p[2]-pow)
	    pow = p[2]
	  end
	  if w1[p[1]]*w1_scaling_factor - w2_scaling_factor*w2[p[1]] != 0
      return false
    end
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
      w1[i] *= lambda^ws
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
