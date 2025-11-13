
################################################################################
#
#  Helper functions for genus 2 curves.
#
################################################################################



@doc raw"""
    transvectant(f::MPolyRingElem{T}, g::MPolyRingElem{T}, k::Int) -> MPolyRingElem

Compute the transvectant (f, g)_k.
"""
function transvectant(f::MPolyRingElem{T}, g::MPolyRingElem{T}, k::Int) where T
  Kxy = parent(f)
  K = base_ring(Kxy)
  x, y = gens(Kxy)
  n = max(total_degree(f),k)
  m = max(total_degree(g),k)
  c = K(factorial(m-k) * factorial(n-k) // (factorial(m) * factorial(n)))

  Omega, (dfx, dfy, dgx, dgy) = polynomial_ring(K, ["dfx", "dfy", "dgx", "dgy"])
  diff_op = c * (dfx * dgy - dfy * dgx)^k

  result = Kxy(0)
  for mon in monomials(diff_op)
    dfxy_part = derivative(derivative(f, x, degree(mon, dfx)), y, degree(mon, dfy))
    dgxy_part = derivative(derivative(g, x, degree(mon, dgx)), y, degree(mon, dgy))
    
    result += coeff(diff_op,mon) * dfxy_part * dgxy_part
  end
  return result
end

function derivative(f::MPolyRingElem{T}, x::MPolyRingElem{T}, n::Int) where T
  @req n >= 0 "n needs to be non-zero."
  i = 0
  while n > i 
    f = derivative(f, x)
    i += 1
  end
return f
end

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
  A = gcdx(ws[non_zero]...)
  gcd_ws = A[1]
  
#And Bezout coefficients
  B_coeffs = A[2:end]

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
    weighted_reduction(w1::Vector{T}, ws::Vector{Int}) -> Bool

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

# Given a linear equation of the form f(x, y) = a * x + b * y = 0, 
# find the minimal x_0, y_0 such that f(x_0, y_0) = 0.
function minimize_linear_equation(f::MPolyRingElem{QQFieldElem})
  R = parent(f)
  x, y = gens(R)

  a_num = numerator(coeff(f, u))
  a_den = denominator(coeff(f, u))

  b_num = numerator(coeff(f, v))
  b_den = denominator(coeff(f, v))

  gcd_ab = gcd([a_num * b_den, b_num * a_den, a_den * b_den])

  C1 = divexact(a_num * b_den, gcd_ab)
  C2 = divexact(b_num * a_den, gcd_ab)
  C3 = divexact(a_den * b_den, gcd_ab)

  _, x0, y0 = C3 * collect(gcdx(C1, C2))

  return x0, y0
end