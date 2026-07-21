function shioda_invariants(f::MPolyRingElem{T}) where T

  K = base_ring(f)
  n = total_degree(f)
  @req n == 8 "Shioda invariants are only defined for a hyperelliptic curve of genus 3."

  if  0 < characteristic(K) <= 7
    error("Currently only implemented for characteristic greater than 7.")
  end

  g = transvectant(f, f, 4)
  k = transvectant(f, f, 6)
  h = transvectant(k, k, 2)
  m = transvectant(f, k, 4)
  n = transvectant(f, h, 4)
  p = transvectant(g, k, 4)
  q = transvectant(g, h, 4)

  J2 = transvectant(f, f, 8)
  J3 = transvectant(f, g, 8)
  J4 = transvectant(k, k, 4)
  J5 = transvectant(m, k, 4)
  J6 = transvectant(h, k, 4)
  J7 = transvectant(m, h, 4)
  J8 = transvectant(p, h, 4)
  J9 = transvectant(n, h, 4)
  J10 = transvectant(q, h, 4)

  return map(x-> K(evaluate(x, [0,0])),[J2, J3, J4, J5, J6, J7, J8, J9, J10])
end


@doc raw"""
    shioda_invariants(C::HypellCrv{T}) -> Vector{T}, Vector{Int}
Returns the Shioda invariants J2, ..., J10 for the genus 3 curve C
and the corresponding weights.
"""
function shioda_invariants(C::HypellCrv)
  f, h = hyperelliptic_polynomials(C)
  return shioda_invariants(f, h)
end

function shioda_invariants(f::PolyRingElem{T}) where T
  Rxz, (x, z) = polynomial_ring(K, ["x", "z"])
  coeff_f = coefficients(f)
  f_hom = sum([coeff_f[i]*x^i*z^(8 - i) for i in (0:8)];init = zero(Rxz))
  return shioda_invariants(f_hom), [2,3,4,5,6,7,8,9,10]
end

function shioda_invariants(f::PolyRingElem{T}, h::PolyRingElem{T}) where T  <: FieldElem
  return shioda_invariants(f + h^2/4)
end
