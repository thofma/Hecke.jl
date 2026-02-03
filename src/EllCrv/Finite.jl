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

# section 4.3.4
@doc raw"""
    elem_order_bsgs(P::EllipticCurvePoint) -> ZZRingElem

Calculate the order of a point $P$ on an elliptic curve given over a finite
field using Baby-step Giant-step (BSGS).
"""
function elem_order_bsgs(P::EllipticCurvePoint{T}) where T<:FinFieldElem
  R = base_field(P.parent)
  p = characteristic(R)
  p == 0 && error("Base field must be finite")
  q = order(R) # R = F_q

  # step 1
  Q = Int(q + 1) * P

  # step 2
  m = Int(ceil(Int(q)^(1//4)))

  list_points = []
  for j = 0:m
    S = j*P
    push!(list_points, S)
  end

  # step 3
  k = -m
  H = (2*m)*P
  M = ZZ(0) # initialize M, so that it is known after the while loop

  while k < m + 1
    Snew = Q + (k*H)

    i = 1
    while i < m + 2 # is there a match?
      if Snew == list_points[i]
        M = q + 1 + (2*m*k) - (i-1)

        if M != 0
          i = m + 2 # leave both while loops
          k = m + 1
        else
          i = i + 1 # search on if M == 0
        end

      elseif Snew == -(list_points[i])
        M = q + 1 + (2*m*k) + (i-1) # step 4

        if M != 0
          i = m + 2 # leave both while loops
          k = m + 1
        else
          i = i + 1 # search on if M == 0
        end
      else
        i = i + 1
      end
    end

    k = k + 1
  end

  # step 5
  gotostep5 = true
  while gotostep5
    fac = factor(M)
    primefactors = []
    for i in fac
      push!(primefactors, i[1])
    end
    r = length(primefactors)

    # step 6
    i = 1
    while i < (r + 1)
      U = Int(divexact(M, primefactors[i]))*P
      if U.is_infinite == true
        M = divexact(M, primefactors[i])
        i = r + 2  # leave while-loop
      else
        i = i + 1
      end
    end

    if i == r + 1  # then (M/p_i)P != oo for all i
      gotostep5 = false
    end
  end

  return abs(ZZ(M))
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
  return elem_order_bsgs(P)
end

function order(P::EllipticCurvePoint{T}, fac::Fac{ZZRingElem}) where T<:FinFieldElem
  return _order_elem_via_fac(P, fac)
end

function _order_elem_via_fac(P::EllipticCurvePoint{<:FinFieldElem}, fn = _order_factored(parent(P)))
  E = parent(P)
  n = order(E)
  o = one(ZZ)
  for (p, e) in fn
    q = p^e
    m = divexact(n, q)
    Q = m*P # order dividing q = p^e
    for i in 0:e
      if is_infinite(Q)
        break
      else
        o = o * p
        Q = p * Q
      end
    end
  end
  return o
end

################################################################################
#
#  Supersingular Elliptic Curves
#
################################################################################


#Following Identifying supersingular elliptic curves - Andrew V. Sutherland
@doc raw"""
    is_supersingular(E::EllipticCurve{T}) where T <: FinFieldElem

Returns `true` when the elliptic curve is supersingular and `false` otherwise.
The result is proven to be correct.
"""
function is_supersingular(E::EllipticCurve{T}) where T <: FinFieldElem
  K = base_field(E)

  p = characteristic(K)
  j = j_invariant(E)

  if j^(p^2) != j
    return false
  end

  if p<= 3
    return j == 0
  end

  L = Native.GF(p, 2)
  Lx, X = polynomial_ring(L, "X")
  Lxy, Y = polynomial_ring(Lx, "Y")
  Phi2 = X^3 + Y^3 - X^2*Y^2 + 1488*(X^2*Y + Y^2*X) - 162000*(X^2 + Y^2) + 40773375*X*Y + 8748000000*(X + Y) - 157464000000000

  jL = _embed_into_p2(j, L)

  js = roots(Phi2(jL))

  if length(js) < 3
    return false
  end

  newjs = [jL, jL, jL]
  f = zeros_array(Lx, 3)

  m = nbits(p) - 1
  for k in (1 : m)
    for i in (1 : 3)
      f[i] = divexact(Phi2(js[i]), X - newjs[i])
      newjs[i] = js[i]
      froots = roots(f[i])
      if isempty(froots)
        return false
      end
      js[i] = froots[1]
    end
  end
  return true
end

function _to_z(a::Union{fpFieldElem, FpFieldElem})
  return lift(a)
end

function _to_z(a::Union{fqPolyRepFieldElem, FqPolyRepFieldElem})
  return coeff(a, 0)
end

function _to_z(a::FqFieldElem)
  return lift(ZZ, a)
end

function _embed_into_p2(j, L)
  K = parent(j)
  # The easy case
  if degree(K) == 1
    return L(_to_z(j))
  else
    p = minpoly(j)
    # Easy case
    if degree(p) <= 1
      return L(_to_z(j))
    end
    F, a = finite_field(p)
    e = embed(F, L)
    return e(gen(F))
  end
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
