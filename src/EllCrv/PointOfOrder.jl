################################################################################
#
#  EllipticCurve/PointOfOrder.jl : Curves over finite fields with a point of
#  prescribed order, from the raw form of the modular curve X_1(N)
#
################################################################################

@doc raw"""
    elliptic_curve_with_point_of_order(K::FinField, N::IntegerUnion;
                                       rng::AbstractRNG = Random.default_rng())
                                       -> EllipticCurve, EllipticCurvePoint

Return a random elliptic curve over the finite field $K$ and a point on it of
order exactly $N$, by the construction of [Sut12*1](@cite).

The order $N \geq 2$ must be prime to the characteristic of $K$. For
$N \geq 4$ the curve is the Tate normal form $y^2 + (1 - c)xy - by = x^3 - bx^2$
and the point is $(0, 0)$; for $N \geq 6$, $(b, c)$ comes from a point of the
raw form $F_N(r, s) = 0$ of $X_1(N)$, which Algorithm 1 of [Sut12*1](@cite)
computes the first time it is needed in a session. Its cost grows quickly
with $N$, from instant for small $N$ to minutes around $N = 100$. Equations
of lower degree for $X_1(N)$, which would make large $N$ faster, are
available at <https://math.mit.edu/~drew/X1_altcurves.html>.

An error is raised when no elliptic curve over $K$ has a point of order $N$,
as for $N = 13$ over $\mathbb{F}_2$; at once when $N > q + 1 + 2\sqrt{q}$,
$q$ the order of $K$, the Hasse bound on the number of points.

# Examples

```jldoctest
julia> E, P = elliptic_curve_with_point_of_order(GF(101), 7);

julia> order(P)
7
```
"""
function elliptic_curve_with_point_of_order(
    K::FinField, N::IntegerUnion; rng::AbstractRNG = Random.default_rng())
  @req N >= 2 "N must be at least 2"
  @req N <= typemax(Int) "N must fit in an Int"
  n = Int(N)
  p = characteristic(K)
  @req !is_divisible_by(ZZ(n), p) "N must be prime to the characteristic"
  q = order(K)
  # N divides the number of points, at most q + 1 + 2 sqrt(q) (Hasse)
  n > q + 1 + isqrt(4 * q) &&
    error("no elliptic curve over $K has a point of order $n")
  a = _first_curve(_point_of_order_curves(K, n, rng), K, rng)
  a === nothing && error("no elliptic curve over $K has a point of order $n")
  E = elliptic_curve(K, a; check = false)
  return E, E([zero(K), zero(K)])
end

# The first value of `curves(u, all)` for u in K: u drawn at random, with
# all = false, so that the curve is random; then every u, with all = true, so
# that the search is exhaustive on any field; nothing if every u gives none.
# `curves(u, all)` returns a vector of a-invariants of nonsingular curves with
# (0, 0) of order N: every one from u when all is true, else at least one if
# there is one. In practice the draws succeed at once unless K is tiny; the
# result never depends on it.
function _first_curve(curves, K::FinField, rng::AbstractRNG)
  for _ in 1:Int(min(order(K), ZZ(1000)))
    cs = curves(rand(rng, K), false)
    isempty(cs) || return rand(rng, cs)
  end
  for u in K
    cs = curves(u, true)
    isempty(cs) || return first(cs)
  end
  return nothing
end

# The function `curves` of `_first_curve` for N.
function _point_of_order_curves(K::FinField, N::Int, rng::AbstractRNG)
  o = zero(K)
  if N == 2
    # y^2 = x^3 + a2 x^2 + a4 x, where (0, 0) has order 2, a4 = u; nonsingular
    # unless a4 (a2^2 - 4 a4) = 0 (Silverman, The Arithmetic of Elliptic
    # Curves, III.1), so for a2 = 0 whenever u != 0, p being odd.
    return function (u, all)
      is_zero(u) && return Vector{elem_type(K)}[]
      a2 = rand(rng, K)
      is_zero(a2^2 - 4 * u) && (a2 = o)
      return [[o, a2, o, u, o]]
    end
  elseif N == 3
    # y^2 + a1 xy + a3 y = x^3, where (0, 0) is a flex, of order 3, a3 = u;
    # nonsingular unless a3 (a1^3 - 27 a3) = 0 (ibid.), so for a1 = 0 whenever
    # u != 0, p not being 3.
    return function (u, all)
      is_zero(u) && return Vector{elem_type(K)}[]
      a1 = rand(rng, K)
      is_zero(a1^3 - 27 * u) && (a1 = o)
      return [[a1, o, u, o, o]]
    end
  elseif N == 4
    # E(b, c) with c = 0, [Sut12*1], section 2
    return (u, all) -> _tate_normal_curves([(u, o)])
  elseif N == 5
    # E(b, c) with b = c, ibid.
    return (u, all) -> _tate_normal_curves([(u, u)])
  end
  # N >= 6: the points (r, s) of F_N(r, s) = 0 with the drawn coordinate u, and
  # b = rs(r - 1), c = s(r - 1), ibid.
  solve_r, coeffs = _x1_raw_form_coefficients(K, N)
  Kt, _ = polynomial_ring(K, :t; cached = false)
  T = elem_type(K)
  return function (u, all)
    g = Kt([evalpoly(u, v) for v in coeffs])
    # F_N is zero on the line through u only if u is a common root of all its
    # coefficients, possible for even N, where F_N is not monic in the solved
    # variable; then every value of that variable is a root
    vs = is_zero(g) ? (all ? collect(K) : [rand(rng, K)]) : roots(g)
    all || isempty(vs) || (vs = [rand(rng, vs)])
    points = Tuple{T, T}[solve_r ? (v * u * (v - 1), u * (v - 1)) :
                                   (u * v * (u - 1), v * (u - 1)) for v in vs]
    return _tate_normal_curves(points)
  end
end

# The a-invariants of the nonsingular Tate normal forms
# E(b, c) : y^2 + (1 - c)xy - by = x^3 - bx^2 among the given (b, c), by the
# discriminant b^3 (16 b^2 - 8 b c^2 - 20 b c + b + c (c - 1)^3), [Sut12*1],
# (1) and (3).
function _tate_normal_curves(bc::Vector{Tuple{T, T}}) where {T <: FinFieldElem}
  curves = Vector{T}[]
  for (b, c) in bc
    delta = b^3 * (16 * b^2 - 8 * b * c^2 - 20 * b * c + b + c * (c - 1)^3)
    is_zero(delta) && continue
    o = zero(b)
    push!(curves, [1 - c, -b, -b, o, o])
  end
  return curves
end

################################################################################
#
#  The raw form F_N(r, s) = 0 of X_1(N), by Algorithm 1 of [Sut12*1]
#
################################################################################

# By Proposition 1 of [Sut12*1], for (r, s) with Delta(b, c) != 0 in a field of
# characteristic not dividing N, (0, 0) on E(b, c) has order N exactly when
# F_N(r, s) = 0; and every curve with a point P of order N >= 6 is some E(b, c)
# with P = (0, 0) ([Sut12*1], section 2), with r = b/c, s = c^2/(b - c). So the
# search of `_first_curve` over the points of F_N = 0 finds a curve whenever
# there is one.

const _X1_RAW_FORMS = Dict{Int, ZZMPolyRingElem}()
const _X1_RAW_FORM_TABLES = Dict{Int, Tuple{Bool, Vector{Vector{ZZRingElem}}}}()

# (solve_r, coefficients) of `_x1_raw_form_table(N)` mapped into K; kept on K
# when K stores attributes, since mapping them is a fifth of a call.
function _x1_raw_form_coefficients(K::FinField, N::Int)
  solve_r, table = _x1_raw_form_table(N)
  map_into_K() = [[K(a) for a in v] for v in table]
  is_attribute_storing(K) || return solve_r, map_into_K()
  T = elem_type(K)
  cache = get_attribute!(K, :x1_raw_form_coefficients) do
    Dict{Int, Vector{Vector{T}}}()
  end
  return solve_r, get!(map_into_K, cache, N)
end

# (solve_r, table): F_N as a polynomial in the variable of smaller positive
# degree (r if solve_r, else s), for each of its powers, constant term first,
# the integer coefficients in the other variable, constant term first.
function _x1_raw_form_table(N::Int)
  haskey(_X1_RAW_FORM_TABLES, N) && return _X1_RAW_FORM_TABLES[N]
  F = _x1_raw_form(N)
  dr, ds = degree(F, 1), degree(F, 2)
  solve_r = dr > 0 && (dr <= ds || ds == 0)
  i, j = solve_r ? (1, 2) : (2, 1)
  table = [zeros(ZZRingElem, degree(F, j) + 1) for _ in 0:degree(F, i)]
  for (a, e) in zip(coefficients(F), exponent_vectors(F))
    table[e[i] + 1][e[j] + 1] = a
  end
  return _X1_RAW_FORM_TABLES[N] = (solve_r, table)
end

# F_N(r, s) in ZZ[r, s], N >= 6, by Algorithm 1 of [Sut12*1]: the numerator of
# x_m - x_n, m = floor(N/2) + 1, n = N - m, where nP = (x_n, y_n) on E(b, c),
# b = rs(r - 1), c = s(r - 1), and P = (0, 0); without the powers of r, s,
# r - 1 and F_M, M > 5 a proper divisor of N; made square-free. Computed once.
function _x1_raw_form(N::Int)
  @assert N >= 6
  haskey(_X1_RAW_FORMS, N) && return _X1_RAW_FORMS[N]
  R, (r, s) = polynomial_ring(ZZ, [:r, :s])
  Q = fraction_field(R)
  b = Q(r * s * (r - 1))
  c = Q(s * (r - 1))
  m = div(N, 2) + 1
  n = N - m
  # 2P = (b, bc), and (4): x_{k+1} = b y_k / x_k^2,
  # y_{k+1} = b^2 (x_k^2 - y_k) / x_k^3
  xs = [zero(Q), b]
  xk, yk = b, b * c
  for _ in 3:m
    xk, yk = divexact(b * yk, xk^2), divexact(b^2 * (xk^2 - yk), xk^3)
    push!(xs, xk)
  end
  G = numerator(xs[m]) * denominator(xs[n]) -
      numerator(xs[n]) * denominator(xs[m])
  divisors_M = [_x1_raw_form(M) for M in 6:(N - 1) if N % M == 0]
  for f in vcat([r, s, r - 1], divisors_M)
    _, G = remove(G, f)
  end
  G = prod(p for (p, _) in factor_squarefree(G))
  return _X1_RAW_FORMS[N] = G
end
