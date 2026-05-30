################################################################################
#
#  DrinfeldModule/CarlitzModule.jl : The Carlitz module and related functions
#
#  The Carlitz module is the simplest Drinfeld module of rank 1 over A = F_q[T].
#  It is defined by phi_T = gamma(T) + tau, where gamma: A -> K is the
#  structural morphism.
#
################################################################################

################################################################################
#
#  Carlitz module
#
################################################################################

@doc raw"""
    carlitz_module(A::PolyRing, gamma_T) -> DrinfeldModule

Return the Carlitz module over `A = F_q[T]` with structural morphism given
by `gamma_T`, i.e., the Drinfeld module `phi` with `phi_T = gamma_T + tau`.

`gamma_T` must be an element of some field `K` (the base field).
"""
function carlitz_module(A::PolyRing, gamma_T)
  K = parent(gamma_T)
  T = elem_type(K)
  return drinfeld_module(A, T[K(gamma_T), one(K)])
end

@doc raw"""
    carlitz_module(A::PolyRing) -> DrinfeldModule

Return the Carlitz module over `A = F_q[T]` with `phi_T = gen(F_q) + tau`,
where `F_q = base_ring(A)`.
"""
function carlitz_module(A::PolyRing)
  Fq = base_ring(A)
  @req Fq isa FinField "base ring of A must be a finite field"
  gamma_T = gen(Fq)
  return carlitz_module(A, gamma_T)
end

################################################################################
#
#  Carlitz factorial
#
#  The Carlitz factorial D_n is defined by:
#    D_0 = 1
#    D_n = D_{n-1}^q * (T^{q^n} - T)   (not the correct recurrence)
#
#  The correct definition uses the base-q expansion of n:
#  if n = c_0 + c_1*q + c_2*q^2 + ..., then
#    n! = prod_j E_j^{c_j}
#  where E_0 = 1, E_j = E_{j-1}^q * (T^{q^j} - T).
#
################################################################################

@doc raw"""
    carlitz_factorial(A::PolyRing, n::Integer) -> PolyRingElem

Return the `n`-th Carlitz factorial, an element of `A = F_q[T]`.

The Carlitz factorial is defined by expanding `n` in base `q = |F_q|` as
`n = sum_j c_j * q^j` and setting `n! = prod_j E_j^{c_j}`, where
`E_0 = 1` and `E_j = E_{j-1}^q * (T^{q^j} - T)`.
"""
function carlitz_factorial(A::PolyRing, n::Integer)
  @req n >= 0 "Carlitz factorial requires n >= 0"
  Fq = base_ring(A)
  @req Fq isa FinField "base ring of A must be a finite field"
  q = Int(order(Fq))
  T_gen = gen(A)

  if n == 0
    return one(A)
  end

  # Compute E_j iteratively and accumulate the product
  result = one(A)
  E = one(A)  # E_0 = 1
  j = 1
  remaining = n
  while remaining > 0
    remaining, c = divrem(remaining, q)
    # E_j = E_{j-1}^q * (T^{q^j} - T)
    E = E^q * (T_gen^(q^j) - T_gen)
    if c > 0
      result *= E^c
    end
    j += 1
  end
  return result
end
