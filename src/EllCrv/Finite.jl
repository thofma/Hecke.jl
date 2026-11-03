################################################################################
#
#          EllipticCurve/Finite.jl : Elliptic curves over finite fields
#
################################################################################

################################################################################
#
#  Random point
#
################################################################################

Random.gentype(::Type{EllipticCurve{T}}) where {T} = EllipticCurvePoint{T}

@doc raw"""
    rand(E::EllipticCurve) -> EllipticCurvePoint

Return a random point on the elliptic curve $E$ defined over a finite field.
"""
function rand(rng::AbstractRNG, Esp::Random.SamplerTrivial{<:EllipticCurve})
  # Algorithm 6 of Miller, "The Weil Pairing, and Its Efficient Calculation"
  E = Esp[]
  R = base_field(E)

  if E.short == false
    while true
      return_infinity = rand(rng, 0:order(R))
      if return_infinity == 1
        return infinity(E)
      end
      # choose random x-coordinate and check if there exists a corresponding y-coordinate
      x = rand(rng, R)
      a1, a2, a3, a4, a6 = a_invariants(E)
      Ry, y = polynomial_ring(R,"y")
      f = y^2 +a1*x*y + a3*y - x^3 - a2*x^2 - a4*x - a6
      ys = roots(f)
      if length(ys) != 0
        t = rand(rng, ys)
        P = E([x,t])
        return P
      end
    end
  end

  while true
  # choose random x-coordinate and check if it is a square in F_q
  # if not, choose new x-coordinate
    return_infinity = rand(rng, 0:order(R))
    if return_infinity == 1
      return infinity(E)
    end

    x = rand(rng, R)
    _,_,_, a4, a6 = a_invariants(E)
    Ry, y = polynomial_ring(R,"y")
    f = y^2 - x^3 - a4*x - a6
    ys = roots(f)
      if length(ys)!=0
        t = rand(rng, ys)
        P = E([x,t])
        return P
      end
  end
end

################################################################################
#
#  Point order
#
################################################################################

function _point_order_from_multiple(P::EllipticCurvePoint{<:FinFieldElem}, M::ZZRingElem, facM::Fac{ZZRingElem})
  ord = ZZ(1)

  for (p, e) in facM
    Q = divexact(M, p^e)*P
    while !is_infinite(Q)
      ord *= p
      Q = p * Q
    end
  end

  return ord
end

# d is known divisor of the *group* order
function _point_order_bsgs(P_in::EllipticCurvePoint{<:FinFieldElem}, d::ZZRingElem)
  is_infinite(P_in) && return ZZ(1)

  R = base_field(parent(P_in))
  p = characteristic(R)
  p == 0 && error("Base field must be finite")
  q = order(R)

  # Initially we have Hasse interval, which is centered at q+1
  # We set m = ceil(q^{1/4}) (half of the square root of interval length)
  #   and use stride 2m for giant steps
  # |E| = q + 1 - t, so the center is Q = [q+1]P = [t]P
  # Let H = [2m]P
  # Baby steps: we compute [j]P for j = 0..m
  # Giant steps: for k = -m..m check if Q + [k]H is +- [j]P
  # Note that we check both plus and minus, effectively having 2m+1 baby steps
  # So for a giant step k we check if t = +-j - 2m*k
  # Each such window is of length 2m + 1: consecutive windows overlap at one value
  # and in total we check 4m^2 values: we need 4*m^2 >= 4*sqrt(q)
  #
  # If a divisor d of group order is known, we can further optimize search:
  #   we consider [d]P instead: its order divides |E|/d
  # Thus we can shrink our search interval:
  # [L, R] -> [floor(L/d), ceil(R/d)]
  # We still want to have a centered search:
  #   center = (q+1)/d, and Q = center * [d]P
  # Half-width of original interval is bounded by 2*floor(sqrt(q)) + 2
  # After scaling by d, it is bound by 1 + (2*floor(sqrt(q)) + 2) / d
  # This gives us a bound for m^2
  local P, center, m_zz
  if d > 1
    P = d*P_in
    is_infinite(P) && return _point_order_from_multiple(P_in, d, factor(d))
    center = div(q + 1, d)
    m_zz = 1 + isqrt(1 + div(2*isqrt(q) + 2, d))
  else
    P = P_in
    center = q + 1
    m_zz = 1 + isqrt(isqrt(q))
  end

  # we need to allocate m baby steps, if m doesn't fit into Int we have no chance to do so
  !fits(Int, m_zz) && error("Elliptic curve group order is too large for BSGS")
  m = Int(m_zz)

  Q = center*P

  # Baby steps: j*P for j = 0..m
  baby = Dict{typeof(P), Int}()
  S = infinity(parent(P))
  for j in 0:m
    baby[S] = j
    S = S + P
  end

  # Giant steps: we use stride H = (2m)*P, and check if Q + [k]H is a baby step
  stride = 2*m_zz
  H = stride*P
  M = ZZ(0)

  for k in -m:m
    Snew = Q + k*H

    j = get(baby, Snew, -1)
    if j >= 0
      M = center + stride*k - j
      !is_zero(M) && break # non-trivial multiple of order
    end

    j = get(baby, -Snew, -1)
    if j >= 0
      M = center + stride*k + j
      !is_zero(M) && break # non-trivial multiple of order
    end
  end

  @assert !is_zero(M) "BSGS failed to find a multiple of the order"

  # TODO: we should combine factorizations
  if d > 1
    M = M*d
  end
  return _point_order_from_multiple(P_in, M, factor(M))
end

@doc raw"""
    elem_order_bsgs(P::EllipticCurvePoint) -> ZZRingElem

Calculate the order of a point $P$ on an elliptic curve given over a finite
field using Baby-step Giant-step (BSGS).
"""
function elem_order_bsgs(P::EllipticCurvePoint{T}) where T<:FinFieldElem
  return _point_order_bsgs(P, ZZ(1))
end

@doc raw"""
    order(P::EllipticCurvePoint, [fac::Fac{ZZRingElem}]) -> ZZRingElem

Given a point $P$ on an elliptic curve $E$ over a finite field, return the order
of this point.

Optionally, one can supply the factorization of a multiple of the point order,
for example the order of $E$.

# Examples

```jldoctest
julia> E = elliptic_curve(GF(101), [1, 2]);

julia> P = E([17, 65]);

julia> order(P)
100

julia> fac = factor(order(E))
2^2 * 5^2

julia> order(P, fac)
100
```
"""
function order(P::EllipticCurvePoint{T}) where T<:FinFieldElem
  # TODO: should we maybe check if order was factored already?
  #   in this case _point_order_from_multiple should be faster
  return elem_order_bsgs(P)
end

function order(P::EllipticCurvePoint{T}, fac::Fac{ZZRingElem}) where T<:FinFieldElem
  return _point_order_from_multiple(P, evaluate(fac), fac)
end

function _order_elem_via_fac(P::EllipticCurvePoint{<:FinFieldElem})
  E = parent(P)
  return _point_order_from_multiple(P, order(E), _order_factored(E))
end

################################################################################
#
#  Supersingular Elliptic Curves
#
################################################################################


# The j-invariants of the elliptic curves with complex multiplication by an
# imaginary quadratic order of class number 1, with the discriminant of the
# order, as in Table 3.1.1 of He-Korpal-Tran-Vincent, arXiv:2503.03478.
const _CLASS_NUMBER_ONE_J_INVARIANTS = (
  (-3, 0), (-4, 1728), (-7, -3375), (-8, 8000), (-11, -32768), (-12, 54000),
  (-16, 287496), (-19, -884736), (-27, -12288000), (-28, 16581375),
  (-43, -884736000), (-67, -147197952000), (-163, -262537412640768000))

@doc raw"""
    is_supersingular(E::EllipticCurve{T}) where T <: FinFieldElem

Returns `true` when the elliptic curve is supersingular and `false` otherwise,
by Algorithm 2 of [Sut12](@cite), with the optimization of section 5.1 there
when the $j$-invariant lies in the prime field. The result is proven to be
correct.
"""
function is_supersingular(E::EllipticCurve{T}) where T <: FinFieldElem
  K = base_field(E)

  p = characteristic(K)
  j = j_invariant(E)

  p <= 3 && return iszero(j)
  # For p > 3, the reduction of an elliptic curve with complex multiplication by
  # an order of discriminant d is supersingular if and only if p does not split
  # in Q(sqrt(d)) (Deuring; Lang, Elliptic Functions, Chapter 13, Theorem 12),
  # and whether E is supersingular depends only on j.
  for (d, jd) in _CLASS_NUMBER_ONE_J_INVARIANTS
    j == jd && return kronecker_symbol(ZZ(d), p) != 1
  end

  jp = j^p
  # supersingular j-invariants are in F_{p^2}, as is all of K if its degree is
  # at most 2
  absolute_degree(K) > 2 && jp^p != j && return false

  L = finite_field(p, 2)[1]
  if jp == j
    F = prime_field(K)
    jF = F(lift(ZZ, absolute_coordinates(j)[1]))
    return _is_supersingular_prime_field(jF, L)
  end
  Lx, X = polynomial_ring(L, :X; cached = false)

  # j is a root of X^2 - (j + j^p)*X + j^(p + 1), whose coefficients lie in F_p.
  # Conjugate j-invariants are both supersingular or both ordinary, so we need any conjugate
  jt = L(lift(ZZ, absolute_coordinates(j + jp)[1]))
  jn = L(lift(ZZ, absolute_coordinates(j * jp)[1]))
  jL = first(roots(X^2 - jt*X + jn))

  # The edges of the 2-isogeny graph are counted with multiplicity, so jL has
  # three neighbours if Phi_2(jL, X) has three roots counted so. A repeated
  # root gives the same paths twice, so each is followed once.
  a, b, c = _modular_polynomial_2(jL)
  rts = roots_with_multiplicities(X^3 + a*X^2 + b*X + c)
  sum(last, rts; init = 0) < 3 && return false
  js = first.(rts)

  # in Sutherland's paper the path length is checked up to floor( log_2(p) ) + 1
  # which is exactly the bitlength of p
  previous = fill(jL, length(js))
  for _ in 1:nbits(p)
    for i in eachindex(js)
      step = _next_2_isogeny_step(js[i], previous[i])
      step === nothing && return false
      previous[i] = js[i]
      js[i] = first(step)
    end
  end
  return true
end

# Algorithm 2 of [Sut12] for j in the prime field F = F_p, with the
# optimization of section 5.1 there: the paths are walked in G_2(F_p) until one
# reaches a vertex with only one neighbour in F_p; that path alone goes on in
# G_2(F_{p^2}) = G_2(L), since if E is ordinary, the edges leaving F_p from that
# vertex descend.
function _is_supersingular_prime_field(j::FinFieldElem, L::FinField)
  F = parent(j)
  p = characteristic(F)
  m = nbits(p)
  Fx, X = polynomial_ring(F, :X; cached = false)
  a, b, c = _modular_polynomial_2(j)
  rts = roots_with_multiplicities(X^3 + a*X^2 + b*X + c)
  # irreducible over F_p, so also over F_{p^2}: j has fewer than 3 neighbours
  isempty(rts) && return false
  if length(rts) == 1 && rts[1][2] == 1
    # j has one neighbour in F_p
    back, cur = rts[1][1], j
  else
    # all three neighbours of j are in F_p
    js = first.(rts)
    previous = fill(j, length(js))
    k = 0
    for _ in 1:m
      for i in eachindex(js)
        step = _next_2_isogeny_step(js[i], previous[i])
        if step === nothing
          k = i
          break
        end
        previous[i] = js[i]
        js[i] = first(step)
      end
      k > 0 && break
    end
    # every path has length m + 1, as in Algorithm 2
    k == 0 && return true
    back, cur = previous[k], js[k]
  end
  # cur has the one neighbour back in F_p; go on through one of the other two
  back, cur = L(lift(ZZ, back)), L(lift(ZZ, cur))
  for _ in 0:m
    step = _next_2_isogeny_step(cur, back)
    step === nothing && return false
    back, cur = cur, first(step)
  end
  return true
end

# The coefficients (a, b, c) of Phi_2(y, X) = X^3 + a*X^2 + b*X + c, the
# classical modular polynomial of level 2 with one variable specialised at y.
function _modular_polynomial_2(y::FinFieldElem)
  y2 = y * y
  return (-y2 + 1488 * y - 162000,
          1488 * y2 + 40773375 * y + 8748000000,
          y2 * y - 162000 * y2 + 8748000000 * y - 157464000000000)
end

# The two roots of Phi_2(j, X)/(X - back) in the field of j, or `nothing` if
# they do not lie in it, for a root `back` of Phi_2(j, X): one step of a path
# in the 2-isogeny graph that does not go back [Sut12, Algorithm 2, step 5],
# by the quadratic formula as in section 4.2 there, for odd characteristic.
function _next_2_isogeny_step(j::T, back::T) where T <: FinFieldElem
  # Phi_2(j, X) = (X - back) * (X^2 + q1*X + q0)
  a, b, _ = _modular_polynomial_2(j)
  q1 = a + back
  q0 = b + back * q1
  fl, s = is_square_with_sqrt(q1^2 - 4*q0)
  fl || return nothing
  return (divexact(-q1 + s, 2), divexact(-q1 - s, 2))
end

@doc raw"""
    is_ordinary(E::EllipticCurve{T}) where T <: FinFieldElem

Returns `true` when the elliptic curve is ordinary and `false` otherwise.
"""
function is_ordinary(E::EllipticCurve{T}) where T <: FinFieldElem
  return !is_supersingular(E)
end

#Following Identifying supersingular elliptic curves - Andrew V. Sutherland
@doc raw"""
    is_probable_supersingular(E::EllipticCurve{T}) where T <: FinFieldElem

Uses a probabilistic algorithm to test whether $E$ is supersingular.
A return value of `false` constitutes a proof that the curve $E$ is ordinary.
A return value of `true` indicates that the curve $E$ is supersingular with high probability,
but it does not prove that $E$ is supersingular.
"""
function is_probable_supersingular(E::EllipticCurve{T}) where T <: FinFieldElem
  j = j_invariant(E)
  K = base_field(E)
  p = characteristic(K)

  local degj::Int

  if degree(K) == 1
    degj = 1
  else
    degj = degree(minpoly(j))
  end

  if degj == 1
    return monte_carlo_test(E, p+1)
  elseif degj == 2
    return monte_carlo_test(E, p+1) || monte_carlo_test(E, p-1)
  else
    return false
  end
end

function monte_carlo_test(E, n)
  E_O = infinity(E)

  for i in (1:10)
    P = rand(E)
    if n*P != E_O
      return false
    end
  end

  return true
end

# Inspired from Sage implementation in ell_finite_field.py
@doc raw"""
    supersingular_polynomial(p::IntegerUnion)

Returns the polynomial whose roots correspond to j-invariants
of supersingular elliptic curves of characteristic p.
"""
function supersingular_polynomial(p::IntegerUnion)
  _p = ZZRingElem(p)
  K = GF(_p)
  KJ, J = polynomial_ring(K, "J")
  if _p < 3
    return J
  end

  m = divexact((_p -1 ), 2)
  KXT, (X, T) = polynomial_ring(K, ["X", "T"], cached = false)
  H = sum(elem_type(KXT)[binomial(m, i)^2 *T^i for i in 0:m])
  F = T^2 * (T - 1)^2 * X - 256 * (T^2 - T + 1)^3
  R = resultant(F, H, 2)
  factors = factor(evaluate(R, [J, zero(KJ)]))
  S = elem_type(KJ)[f for (f, e) in factors]
  R = prod(S; init = one(KJ))
  return R
end

################################################################################
#
#  Group structure
#
################################################################################

# return (m, d) and (P, Q) such that d divides m, P, Q generate E(K),
# P has order m = lcm(d, m) = exp(E(K)), and
# E(K) = Z/d x Z/m.
#
# If m = 1, return [1], []
# If m != 1, d = 1, return [m], [P] (cyclic)
# If m != 1, d != 1, return [m, d], [P, Q]
#
# Not that Q does not necessarily has order d, nor that
# E(K) = <P> x <Q>
#
# Algorithm 2 from
# "The Weil Pairing, and Its Efficient Calculation", Victor S. Miller
# J. Cryptology (2004) 17: 235–261
# DOI: 10.1007/s00145-004-0315-8
#
#
@attr Tuple{Vector{ZZRingElem}, Vector{EllipticCurvePoint{T}}} function _grp_struct_with_gens(E::EllipticCurve{T}) where {T <: FinFieldElem}
  N = order(E)
  K = base_field(E)
  # TODO:
  # we do not have a multiplicative_order for field elements, so go
  # via disc_log :(
  A, AtoK = unit_group(K)
  f = _order_factored(E)

  if is_one(order(E))
    return ZZRingElem[], elem_type(E)[]
  end

  while true
    P, Q = rand(E), rand(E)
    s = _order_elem_via_fac(P)
    t = _order_elem_via_fac(Q)
    m = lcm(s, t)
    zeta = weil_pairing(P, Q, Int(m))
    d = order(AtoK\(zeta))
    if m*d == N
      if s != m && t != m
        continue
      end

      if t == m
        P, Q = Q, P
      end

      @assert Hecke._order_elem_via_fac(P) == m

      if is_one(m)
        return [m], typeof(P)[]
      elseif is_one(d)
        return [m], [P]
      else
        return [m, d], [P, Q]
      end
    end
  end
end

@doc raw"""
    gens(E::EllipticCurve{<:FinFieldElem}) -> Vector{EllipticCurvePoint}

Return a list of generators of the group of rational points on $E$.

# Examples

```jldoctest; filter = r"\(.*"
julia> E = elliptic_curve(GF(101, 2), [1, 2]);

julia> gens(E)
2-element Vector{EllipticCurvePoint{FqFieldElem}}:
 (13*o + 83 : 90*o + 25 : 1)
 (61*o + 62 : 19*o + 24 : 1)

julia> E = elliptic_curve(GF(101), [1, 2]);

julia> gens(E)
1-element Vector{EllipticCurvePoint{FqFieldElem}}:
 (27 : 57 : 1)
```
"""
function gens(E::EllipticCurve{T}) where {T <: FinFieldElem}
  return _grp_struct_with_gens(E)[2]
end

@doc raw"""
    abelian_group(E::EllipticCurve{<:FinFieldElem}) -> FinGenAbGroup, Map

Return an abelian group $A$ isomorphic to the group of rational points of $E$
and a map $E \to A$.

!!! warning
    The map is not implemented yet.

```jldoctest
julia> E = elliptic_curve(GF(101, 2), [1, 2]);

julia> A, _ = abelian_group(E);

julia> A
Z/2 x Z/5200
```
"""
function abelian_group(E::EllipticCurve{U}) where {U <: FinFieldElem}
  _invdiv, _gens = _grp_struct_with_gens(E)
  if length(_gens) == 0
    strct = ZZRingElem[]
    gens = elem_type(E)[]
  elseif length(_gens) == 1
    strct = copy(_invdiv)
    gens = _gens[1]
  elseif length(_gens) == 2
    P, Q = _gens
    # P generates a cyclic group of maximal order.
    # We change Q to Q - l*P, to make it not intersect
    # <P> (and still have the correct order)
    n1, n2 = _invdiv
    n = order(E)
    @assert Hecke._order_elem_via_fac(P) == n1
    @assert n2 == divexact(n, n1)
    _, k = ppio(n1, n2)
    Q = k * Q
    nQ = n2 * _order_elem_via_fac(n2 * Q) # could use that n2 * Q is killed by n1/k/n2
    S = divexact(n, nQ) * P
    T = n2 * Q
    x = disc_log(S, T, divexact(nQ, n2))
    Q = Q - x * divexact(n1, nQ) * P
    @assert _order_elem_via_fac(Q) == n2
    gens = Q, P
    strct = [n2, n1]
  end
  dlog = function(Q)
    error("Not implemented yet")
  end
  return abelian_group(strct), dlog
end

################################################################################
#
#  Discrete logarithm
#
################################################################################

# Just piggy back on the generic one

@doc raw"""
    disc_log(P::EllipticCurvePoint, Q::EllipticCurvePoint, [n::IntegerUnion]) -> ZZRingElem

Return the discrete logarithm $m$ of $Q$ with respect to the base $P$, that is,
$mP = Q$.

If a multiple $n$ of the order of $P$ is known, this can be supplied as an optional
argument.

```jldoctest
julia> E = elliptic_curve(GF(101), [1, 2]);

julia> P = E([6, 74])
(6 : 74 : 1)

julia> Q = E([85, 43])
(85 : 43 : 1)

julia> disc_log(P, Q)
13
```
"""
function disc_log(P::EllipticCurvePoint, Q::EllipticCurvePoint)
  @req parent(P) === parent(Q) "Points must lie on the same elliptic curve"
  n = _order_elem_via_fac(P)
  return disc_log(P, Q, n)
end

# n must be a multiple of the order of P
function disc_log(P::EllipticCurvePoint{T}, Q::EllipticCurvePoint{T}, n::IntegerUnion) where {T <: FinFieldElem}
  @req parent(P) === parent(Q) "Points must lie on the same elliptic curve"
  return disc_log_ph(P, Q, n, 1, (x, y) -> x + y, x -> -x, (x, n) -> n*x)
end
