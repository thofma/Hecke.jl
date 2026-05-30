################################################################################
#
#  DrinfeldModule/DrinfeldModule.jl : Drinfeld modules
#
#  A Drinfeld module is a ring homomorphism
#    phi: A = F_q[T] -> K{tau}
#  where K is an A-field (extension of F_q via a ring map gamma: A -> K).
#  It is uniquely determined by the image phi_T of the generator T, which
#  must have positive degree in K{tau} and constant coefficient gamma(T).
#
################################################################################

################################################################################
#
#  Constructors
#
################################################################################

@doc raw"""
    drinfeld_module(A::PolyRing, coeffs::Vector{T}) -> DrinfeldModule{T}

Construct the Drinfeld module over the polynomial ring `A = F_q[T]` whose
image of the generator `T` is the Ore polynomial
`phi_T = coeffs[1] + coeffs[2]*tau + ... + coeffs[r+1]*tau^r`.

The `coeffs` vector must have length at least 2, its last entry must be
nonzero, and all entries must lie in the same field `K` (the A-field).
The coefficient `coeffs[1] = gamma(T)` specifies the base morphism.
"""
function drinfeld_module(A::PolyRing, coeffs::Vector{T}) where {T}
  @req length(coeffs) >= 2 "need at least 2 coefficients (rank >= 1)"
  @req !iszero(coeffs[end]) "leading coefficient must be nonzero"
  K = parent(coeffs[1])
  for c in coeffs
    @req parent(c) === K "all coefficients must lie in the same field"
  end
  Fq = base_ring(A)
  q = ZZRingElem(order(Fq))
  R = OrePolyRing{T}(K, q, :tau)
  phi_T = OrePoly{T}(R, copy(coeffs))
  return DrinfeldModule{T}(A, phi_T)
end

function drinfeld_module(A::PolyRing, coeffs::AbstractVector)
  isempty(coeffs) && error("coefficient vector must be non-empty")
  K = parent(coeffs[1])
  T = elem_type(K)
  return drinfeld_module(A, T[K(c) for c in coeffs])
end

################################################################################
#
#  Basic accessors
#
################################################################################

@doc raw"""
    function_ring(phi::DrinfeldModule) -> PolyRing

Return the function ring `A = F_q[T]` of the Drinfeld module.
"""
function function_ring(phi::DrinfeldModule)
  return phi.function_ring
end

@doc raw"""
    base_ring(phi::DrinfeldModule) -> Ring

Return the base field `K` (the A-field) of the Drinfeld module.
"""
function base_ring(phi::DrinfeldModule)
  return base_ring(phi.ore_poly_ring)
end

@doc raw"""
    ore_polynomial_ring(phi::DrinfeldModule) -> OrePolyRing

Return the Ore polynomial ring `K{tau}` associated to `phi`.
"""
function ore_polynomial_ring(phi::DrinfeldModule)
  return phi.ore_poly_ring
end

@doc raw"""
    gen(phi::DrinfeldModule) -> OrePoly

Return the generator `phi_T` of the Drinfeld module, i.e., the image of
the generator `T` of the function ring.
"""
function gen(phi::DrinfeldModule)
  return phi.gen
end

@doc raw"""
    rank(phi::DrinfeldModule) -> Int

Return the rank of the Drinfeld module, i.e., the degree of `phi_T` in
`K{tau}`.
"""
function rank(phi::DrinfeldModule)
  return degree(gen(phi))
end

@doc raw"""
    constant_coefficient(phi::DrinfeldModule{T}) -> T

Return the constant coefficient of `phi_T`, i.e., the image `gamma(T)` of
the generator of the function ring under the base morphism.
"""
function constant_coefficient(phi::DrinfeldModule)
  return constant_coefficient(gen(phi))
end

@doc raw"""
    coefficient(phi::DrinfeldModule{T}, i::Int) -> T

Return the coefficient of `tau^i` in `phi_T`.
"""
function coefficient(phi::DrinfeldModule, i::Int)
  return coeff(gen(phi), i)
end

@doc raw"""
    coefficients(phi::DrinfeldModule{T}) -> Vector{T}

Return all coefficients of `phi_T` as a vector `[a_0, a_1, ..., a_r]`.
"""
function coefficients(phi::DrinfeldModule)
  return coefficients(gen(phi))
end

################################################################################
#
#  Equality
#
################################################################################

function ==(phi::DrinfeldModule{T}, psi::DrinfeldModule{T}) where {T}
  function_ring(phi) === function_ring(psi) || return false
  return coefficients(phi) == coefficients(psi)
end

function Base.hash(phi::DrinfeldModule, h::UInt)
  return hash(gen(phi), h)
end

################################################################################
#
#  Evaluation: compute phi_a for a in A
#
#  Since phi is a ring homomorphism A -> K{tau}, for a = c_d*T^d + ... + c_0
#  we compute phi_a = c_d*phi_T^d + ... + c_1*phi_T + c_0 via Horner's method.
#
################################################################################

@doc raw"""
    evaluate(phi::DrinfeldModule{T}, a::PolyRingElem) -> OrePoly{T}

Return the image `phi_a` of `a` in `K{tau}` under the Drinfeld module map.
"""
function evaluate(phi::DrinfeldModule{T}, a::PolyRingElem) where {T}
  @req parent(a) === function_ring(phi) "a must be in the function ring"
  R = ore_polynomial_ring(phi)
  K = base_ring(phi)
  d = degree(a)
  if d < 0
    return zero(R)
  end
  phi_T = gen(phi)
  # Horner evaluation: phi_a = ((...((c_d) * phi_T + c_{d-1}) * phi_T + ...) * phi_T + c_0
  result = R(K(leading_coefficient(a)))
  for i in d - 1:-1:0
    result = result * phi_T + R(K(coeff(a, i)))
  end
  return result
end

# Make DrinfeldModule callable
function (phi::DrinfeldModule)(a::PolyRingElem)
  return evaluate(phi, a)
end

################################################################################
#
#  Characteristic
#
#  The characteristic of (phi, K, gamma) is the kernel of gamma: A -> K.
#  For K a finite extension of F_q, this is the ideal generated by the
#  minimal polynomial of gamma(T) = constant_coefficient(phi_T) over F_q.
#
################################################################################

@doc raw"""
    characteristic(phi::DrinfeldModule) -> PolyRingElem

Return the characteristic of the Drinfeld module, i.e., the monic generator
of the kernel of the base morphism `gamma: A -> K`. This is the minimal
polynomial of `gamma(T)` over `F_q` (as an element of `A = F_q[T]`), or
the zero polynomial if `gamma(T)` is transcendental over `F_q`.
"""
function characteristic(phi::DrinfeldModule{T}) where {T}
  A = function_ring(phi)
  Fq = base_ring(A)
  K = base_ring(phi)
  gamma_T = constant_coefficient(phi)

  # Compute the Frobenius orbit of gamma_T under x -> x^q (q = order(Fq))
  q = ZZRingElem(order(Fq))
  conjs = T[gamma_T]
  el = gamma_T^q
  deg_K = degree(K)  # degree of K over its prime subfield
  for _ in 2:deg_K
    el == gamma_T && break
    push!(conjs, el)
    el = el^q
  end

  # Minimal polynomial = product of (T - c) for c in the orbit, in K[T]
  Kx, x = polynomial_ring(K, "x"; cached = false)
  min_poly_K = prod(x - Kx(c) for c in conjs; init = one(Kx))

  # Its coefficients must lie in Fq; coerce them to Fq and return as element of A
  coeffs_fq = elem_type(Fq)[]
  for i in 0:Nemo.degree(min_poly_K)
    c = Nemo.coeff(min_poly_K, i)
    push!(coeffs_fq, Fq(c))
  end
  return A(coeffs_fq)
end

################################################################################
#
#  Height
#
#  The height of a Drinfeld module of finite characteristic p is the
#  tau-adic valuation of phi_p (the image of the characteristic polynomial).
#
################################################################################

@doc raw"""
    height(phi::DrinfeldModule) -> Int

Return the height of the Drinfeld module. The characteristic must be a
nonzero prime of the function ring. The height is the smallest index `h`
such that the coefficient of `tau^h` in `phi_p` is nonzero, where `p` is
the characteristic polynomial.
"""
function height(phi::DrinfeldModule)
  p = characteristic(phi)
  @req !iszero(p) "characteristic must be a prime (nonzero) for height to be defined"
  phi_p = evaluate(phi, p)
  @req !iszero(phi_p) "phi_p is zero, which should not happen"
  return divexact(ore_poly_valuation(phi_p), degree(p))
end

################################################################################
#
#  j-invariants
#
#  For phi_T = Delta_0 + Delta_1*tau + ... + Delta_r*tau^r:
#
#  j_k(phi) = Delta_k^{(q^{r-k+1}-1)/(q-1)} / Delta_r^{(q^k-1)/(q-1)}
#
#  For rank 2: j_1 = Delta_1^{q+1} / Delta_2
#
################################################################################

@doc raw"""
    j_invariant(phi::DrinfeldModule{T}) -> T

Return the j-invariant of the rank-2 Drinfeld module `phi`. The j-invariant
is `Delta_1^{q+1} / Delta_2` where `phi_T = Delta_0 + Delta_1*tau + Delta_2*tau^2`
and `q` is the order of the base finite field `F_q`.

Raises an error for rank other than 2.
"""
function j_invariant(phi::DrinfeldModule{T}) where {T}
  @req rank(phi) == 2 "j_invariant is only defined for rank-2 Drinfeld modules"
  A = function_ring(phi)
  Fq = base_ring(A)
  q = ZZRingElem(order(Fq))
  D1 = coefficient(phi, 1)
  D2 = coefficient(phi, 2)
  return D1^(q + 1) * inv(D2)
end

@doc raw"""
    jk_invariants(phi::DrinfeldModule{T}) -> Dict{Int, T}

Return the dictionary of j_k invariants of `phi` for `k = 1, ..., rank-1`.
The j_k invariant is
```
  j_k = Delta_k^{(q^{r-k+1}-1)/(q-1)} / Delta_r^{(q^k-1)/(q-1)}
```
where `r = rank(phi)`, `q = order(F_q)`, and `Delta_i = coefficient(phi_T, i)`.
"""
function jk_invariants(phi::DrinfeldModule{T}) where {T}
  r = rank(phi)
  A = function_ring(phi)
  Fq = base_ring(A)
  q = ZZRingElem(order(Fq))
  Dr = coefficient(phi, r)
  result = Dict{Int, T}()
  for k in 1:r - 1
    Dk = coefficient(phi, k)
    # exponent for numerator: (q^{r-k+1}-1)/(q-1) = 1+q+...+q^{r-k}
    exp_num = divexact(q^(r - k + 1) - 1, q - 1)
    # exponent for denominator: (q^k-1)/(q-1) = 1+q+...+q^{k-1}
    exp_den = divexact(q^k - 1, q - 1)
    result[k] = Dk^exp_num * inv(Dr^exp_den)
  end
  return result
end

################################################################################
#
#  Velu isogeny formula
#
#  Given an isogeny kernel f in K{tau}, compute the codomain Drinfeld module.
#  The isogeny condition is: f * phi_T = psi_T * f.
#  Using right Euclidean division: f * phi_T = psi_T * f + 0.
#
################################################################################

@doc raw"""
    velu(phi::DrinfeldModule{T}, f::OrePoly{T}) -> DrinfeldModule{T}

Return the Drinfeld module `psi` such that `f: phi -> psi` is an isogeny,
using the Velu formula. The Ore polynomial `f` must satisfy
`f * phi_T = psi_T * f` (i.e., be a morphism kernel).

Raises an error if `f` does not define a valid isogeny.
"""
function velu(phi::DrinfeldModule{T}, f::OrePoly{T}) where {T}
  @req parent(f) === ore_polynomial_ring(phi) "f must be in K{tau}"
  @req !iszero(f) "isogeny kernel must be nonzero"
  phi_T = gen(phi)
  # compute the right quotient: f * phi_T = psi_T * f + r
  q, r = right_quo_rem(f * phi_T, f)
  @req iszero(r) "f is not an isogeny kernel (remainder is nonzero)"
  @req constant_coefficient(q) == constant_coefficient(phi_T) "base morphisms do not match"
  A = function_ring(phi)
  return drinfeld_module(A, coefficients(q))
end

################################################################################
#
#  Isomorphism check
#
#  phi and psi are isomorphic over K iff there exists u in K* with
#  psi_T = u * phi_T * u^{-1} in K{tau}.
#
#  This gives: psi_i = u^{1-q^i} * phi_i for i = 0, ..., r,
#  equivalently: u^{q^i - 1} = phi_i / psi_i for each nonzero pair.
#
#  We combine these equations by taking gcds and use Fermat's theorem
#  to check solvability in K*.
#
################################################################################

@doc raw"""
    is_isomorphic(phi::DrinfeldModule{T}, psi::DrinfeldModule{T}) -> Bool

Return whether the Drinfeld modules `phi` and `psi` are isomorphic over
the base field `K`.
"""
function is_isomorphic(phi::DrinfeldModule{T}, psi::DrinfeldModule{T}) where {T}
  base_ring(phi) === base_ring(psi) ||
    return false
  function_ring(phi) === function_ring(psi) ||
    return false
  rank(phi) == rank(psi) || return false
  phi == psi && return true

  # Constant terms must agree (same base morphism)
  constant_coefficient(phi) == constant_coefficient(psi) || return false

  K = base_ring(phi)
  r = rank(phi)
  A = function_ring(phi)
  Fq = base_ring(A)
  q = ZZRingElem(order(Fq))
  N = ZZRingElem(order(K)) - 1  # order of K*

  # Build up combined constraint u^e = ue, starting with e=1, ue=1 (trivial).
  # For each i, the new constraint is u^{q^i-1} = phi_i / psi_i.
  # Combine via xgcd.
  e = ZZRingElem(1)
  ue = one(K)

  for i in 1:r
    ai = coefficient(phi, i)
    bi = coefficient(psi, i)
    if iszero(ai) && iszero(bi)
      continue
    end
    if iszero(ai) || iszero(bi)
      return false
    end
    ci = ai * inv(bi)
    # New equation: u^{q^i - 1} = ci.
    # Combine with u^e = ue using xgcd(e, q^i-1).
    new_e, s, t = _gcd_ext(e, q^i - 1)
    ue = ue^s * ci^t
    e = new_e
  end

  # Check if u^e = ue has a solution in K*:
  # ue must be an e-th power in K*, i.e., ue^(N/gcd(e,N)) = 1.
  g = gcd(e, N)
  return isone(ue^divexact(N, g))
end

# Extended gcd returning (gcd, s, t) with s*a + t*b = gcd(a,b)
function _gcd_ext(a::ZZRingElem, b::ZZRingElem)
  return gcdx(a, b)
end

################################################################################
#
#  Minimal polynomial helper for characteristic computation
#
################################################################################

# Compute the minimal polynomial of a finite field element a
# over the field Fq, returned as an element of the polynomial ring Ax over Fq.
function _minpoly_over_base(a::T, Fq::Ring, Ax::PolyRing) where {T}
  K = parent(a)
  q = ZZRingElem(order(Fq))
  conjs = T[a]
  el = a^q
  deg_K = degree(K)
  for _ in 2:deg_K
    el == a && break
    push!(conjs, el)
    el = el^q
  end
  Kx, x = polynomial_ring(K, "x"; cached = false)
  min_poly_K = prod(x - Kx(c) for c in conjs; init = one(Kx))
  coeffs_fq = elem_type(Fq)[]
  for i in 0:Nemo.degree(min_poly_K)
    c = Nemo.coeff(min_poly_K, i)
    push!(coeffs_fq, Fq(c))
  end
  return Ax(coeffs_fq)
end

################################################################################
#
#  Show
#
################################################################################

function Base.show(io::IO, phi::DrinfeldModule)
  io = pretty(io)
  print(io, "Drinfeld module defined by ", gen(function_ring(phi)))
  print(io, " |-> ", gen(phi))
  println(io)
  print(io, Indent(), "over ", function_ring(phi), Dedent())
end
