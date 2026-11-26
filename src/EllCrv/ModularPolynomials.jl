const default_class_mod_pol_db = joinpath(artifact"ClassicalModularPolynomialsDB", "ClassicalModularPolynomialsDB", "data")

const _classical_modular_polynomial_cache = Dict{Any, Any}()

@doc raw"""
    classical_modular_polynomial([R::MPolyRing,] n::Int) -> Poly

Return the classical modular polynomial of level $n$ in $\mathbf{Z}[x, y]$. If
a bivariate polynomial ring $R$ is supplied, return the polynomial in $R$ with
coefficients mapped to its base ring.

Levels $1 \le n \le 59$ are available from a database. For $n > 59$, only
prime levels are supported, using the isogeny volcano method of [BLS12](@cite).
"""
classical_modular_polynomial

function classical_modular_polynomial(n::Int)
  return classical_modular_polynomial(Globals.Zxy, n)
end

function classical_modular_polynomial(R::MPolyRing, n::Int)
  @req nvars(R) == 2 "Polynomial ring must have two variables"
  @req n >= 1 "Level ($n) must be positive"
  @req n <= 59 || is_prime(n) "Classical modular polynomials of level above " *
                               "59 are only available for prime levels"
  get!(_classical_modular_polynomial_cache, (R, n)) do
    # a dynamic call, so that reading the database does not compile the
    # algorithm
    n > 59 && return Base.invokelatest(_classical_modular_polynomial_crt, R, n)
    open(joinpath(default_class_mod_pol_db, "$n")) do io
      b, exps = _parse(Vector{Vector{Int}}, io)
      @assert Char(b) == ','
      b, coeffs = _parse(Vector{ZZRingElem}, io)
      C = MPolyBuildCtx(R)
      for i in 1:length(exps)
        push_term!(C, base_ring(R)(coeffs[i]), exps[i])
        if exps[i][1] != exps[i][2]
          push_term!(C, base_ring(R)(coeffs[i]), reverse(exps[i]))
        end
      end
      return finish(C)
    end
  end::elem_type(R)
end

const default_atkin_mod_pol_db = joinpath(artifact"AtkinModularPolynomialsDB", "AtkinModularPolynomialsDB", "data")

const _atkin_modular_polynomial_cache = Dict{Any, Any}()

@doc raw"""
    atkin_modular_polynomial([R::MPolyRing,] n::Int) -> Poly

Returns the Atkin modular polynomial of prime level $n as an element of
$\mathbf{Z}[x, y]$. If an optional bivariate polynomial $R$ is specified,
the polynomial will be evaluated at the variables of $R$.

Atkin modular polynomials are available up to level `400`.
"""
atkin_modular_polynomial

function atkin_modular_polynomial(n::Int)
  return atkin_modular_polynomial(Globals.Zxy, n)
end

function atkin_modular_polynomial(R::MPolyRing, n::Int)
  @req is_prime(n) "Level ($n) must be prime"
  @req 1 <= n <= 400 "Database only contains Atkin modular polynomials up to level 400"
  get!(_atkin_modular_polynomial_cache, (R, n)) do
    open(joinpath(default_atkin_mod_pol_db, "$n")) do io
      b, m = _parse(Int, io)
      @assert n == m
      @assert Char(b) == ','
      b, exps = _parse(Vector{Vector{Int}}, io)
      @assert Char(b) == ','
      b, coeffs = _parse(Vector{ZZRingElem}, io)
      C = MPolyBuildCtx(R)
      for i in 1:length(exps)
        push_term!(C, base_ring(R)(coeffs[i]), exps[i])
      end
      return finish(C)
    end
  end::elem_type(R)
end

################################################################################
#
#  Classical modular polynomials of prime level above the database
#
################################################################################

# Phi_l for a prime l > 59 by Algorithm 6.1 of [BLS12]: Phi_l modulo primes p
# from isogeny volcanoes over F_p (Algorithm 2.1), then the Chinese remainder
# theorem. The output is always correct; random choices affect the running
# time only.
function _classical_modular_polynomial_crt(R::MPolyRing, l::Int)
  m = characteristic(base_ring(R))
  isone(m) && return zero(R)
  ord = _modular_polynomial_order(l)
  ps = _modular_polynomial_crt_primes(l, ord.D)
  # For m = 0, and for m beyond the product of the primes, the coefficients
  # over Z are needed; they are computed once, in Zxy, and mapped.
  if iszero(m) || m > prod(ZZ(p) for (p, _) in ps)
    if R !== Globals.Zxy
      return _map_symmetric(R, classical_modular_polynomial(Globals.Zxy, l))
    end
    c = _modular_polynomial_coefficients(l, ord, ps)
    return _symmetric_from_triangle(R, l, c)
  end
  c = _modular_polynomial_coefficients_mod(l, ord, ps, m)
  return _symmetric_from_triangle(R, l, c)
end

# The image in R of f in Zxy, coefficient by coefficient, as for the database.
function _map_symmetric(R::MPolyRing, f::ZZMPolyRingElem)
  C = MPolyBuildCtx(R)
  for (c, e) in zip(coefficients(f), exponent_vectors(f))
    push_term!(C, base_ring(R)(c), e)
  end
  return finish(C)
end

# The coefficients of a symmetric polynomial of degree l + 1 in each variable
# are stored as the triangle of x^a y^b with a >= b, in the order of
# _triangle_index.
_triangle_index(a::Int, b::Int) = div(a * (a + 1), 2) + b + 1

function _symmetric_from_triangle(R::MPolyRing, l::Int, c::Vector{ZZRingElem})
  C = MPolyBuildCtx(R)
  for a in 0:(l + 1), b in 0:a
    x = c[_triangle_index(a, b)]
    iszero(x) && continue
    push_term!(C, base_ring(R)(x), [a, b])
    a != b && push_term!(C, base_ring(R)(x), [b, a])
  end
  return finish(C)
end

# The class group of positive definite binary quadratic forms of discriminant
# d < 0, its elements the reduced forms: product, identity, inverse, power.
function _class_group_mul(f::QuadBin{ZZRingElem}, g::QuadBin{ZZRingElem})
  return reduction(compose(f, g))
end

function _class_group_one(d::ZZRingElem)
  b = mod(d, 2)
  return binary_quadratic_form(one(ZZ), b, divexact(b^2 - d, 4))
end

function _class_group_inv(f::QuadBin{ZZRingElem})
  return reduction(binary_quadratic_form(f[1], -f[2], f[3]))
end

function _class_group_pow(f::QuadBin{ZZRingElem}, n::Int)
  r = _class_group_one(discriminant(f))
  x = f
  # ends: n is halved at each step
  while n > 0
    isodd(n) && (r = _class_group_mul(r, x))
    n >>= 1
    n > 0 && (x = _class_group_mul(x, x))
  end
  return r
end

# Whether the class of f has order exactly N.
function _class_group_has_order(f::QuadBin{ZZRingElem}, N::Int)
  e = _class_group_one(discriminant(f))
  _class_group_pow(f, N) == e || return false
  return all(_class_group_pow(f, div(N, Int(q))) != e for (q, _) in factor(N))
end

# The k in [0, N) with [f]^k = [x], [f] of order N, by baby steps and giant
# steps; nothing if [x] is not a power of [f]. The m giant steps cover every
# k < m^2, and m^2 > N.
function _class_group_dlog(f::QuadBin{ZZRingElem}, x::QuadBin{ZZRingElem},
                           N::Int)
  m = isqrt(N) + 1
  baby = Dict{QuadBin{ZZRingElem}, Int}()
  y = _class_group_one(discriminant(f))
  for j in 0:(m - 1)
    get!(baby, y, j)
    y = _class_group_mul(y, f)
  end
  g = _class_group_inv(_class_group_pow(f, m))
  z = x
  for i in 0:(m - 1)
    j = get(baby, z, -1)
    j >= 0 && return mod(i * m + j, N)
    z = _class_group_mul(z, g)
  end
  return nothing
end

_prime_form_class(d::ZZRingElem, q::Int) = reduction(prime_form(d, ZZ(q)))

# A presentation, in the sense of [BLS12], Sections 5.1 and 6.6, of the class
# group of discriminant d < -4, of order N, by prime forms: cyclic, generated
# by the class g0 of a prime form of norm l0 (n = N, g1 = nothing); or split,
# g0 of order n = N/2 and the class g1 of a prime form of norm l1, a prime
# dividing d, not a power of g0. As l1 ramifies, g1 has order 2, so the group
# is <g0> x <g1>. Nothing if neither holds (l1 = 0: no second generator).
function _class_group_presentation(d::ZZRingElem, N::Int, l0::Int, l1::Int)
  g0 = _prime_form_class(d, l0)
  _class_group_has_order(g0, N) && return (g0 = g0, n = N, g1 = nothing)
  (l1 == 0 || isodd(N)) && return nothing
  n = div(N, 2)
  _class_group_has_order(g0, n) || return nothing
  g1 = _prime_form_class(d, l1)
  @assert _class_group_mul(g1, g1) == _class_group_one(d)
  _class_group_dlog(g0, g1, n) === nothing || return nothing
  return (g0 = g0, n = n, g1 = g1)
end

# The exponents (x0, x1) with [x] = g0^x0 g1^x1 in the presentation P
# (x1 = 0 if P is cyclic): every class of the group has them.
function _class_group_exponents(P, x::QuadBin{ZZRingElem})
  k = _class_group_dlog(P.g0, x, P.n)
  k === nothing || return (k, 0)
  @assert P.g1 !== nothing
  # x g1 = g0^k, so x = g0^k g1, as g1 = g1^-1
  k = _class_group_dlog(P.g0, _class_group_mul(x, P.g1), P.n)
  @assert k !== nothing
  return (k, 1)
end

# x + s y for exponent vectors of the presentation P.
function _class_group_exponents_add(P, x::Tuple{Int, Int}, y::Tuple{Int, Int},
                                    s::Int = 1)
  return (mod(x[1] + s * y[1], P.n),
          P.g1 === nothing ? 0 : mod(x[2] + s * y[2], 2))
end

# A generator of the kernel of cl(R) -> cl(O), R = Z + l O, O of
# discriminant D, l split in O ([BLS12], Lemmas 3.1 and 3.2): the kernel is
# cyclic of order l - 1, and its nontrivial elements are the classes of the
# invertible R-ideals l S_i of norm l^2, S_i = l Z + (-b + sqrt(D))/2 Z, the
# forms (l^2, l b, (b^2 - D)/4) with b = D mod 2 and l not dividing
# (b^2 - D)/4. One of them has order l - 1; b runs over l residues mod 2l, so
# the loop ends.
function _class_group_kernel_generator(D::ZZRingElem, l::Int)
  for b in Int(mod(D, 2)):2:(2 * l - 1)
    c = divexact(b^2 - D, 4)
    is_divisible_by(c, l) && continue
    f = reduction(binary_quadratic_form(ZZ(l)^2, ZZ(l) * b, c))
    _class_group_has_order(f, l - 1) && return f
  end
  error("no generator of the kernel found")
end

# The largest |d_K| of an imaginary quadratic field of class number at most
# 59: 615883, of class number 57 (Watkins's classification of the fields of
# class number at most 100, Math. Comp. 73 (2004), Table 4).
const _class_number_at_most_59_max_disc = 615883

# h[d] for every d <= N with -d = 1 mod 8 a fundamental discriminant: the
# number of reduced forms (a, b, c) of discriminant -d, |b| <= a <= c and
# b >= 0 if |b| = a or a = c, all primitive as -d is fundamental; b is odd
# as -d = 1 mod 8. Other entries are not class numbers.
function _class_numbers_1_mod_8(N::Int)
  h = zeros(Int32, N)
  for a in 1:isqrt(div(N, 3)), b in (-a + 1):a
    isodd(b) || continue
    for c in a:div(N + b^2, 4 * a)
      (c == a && b < 0) && continue
      d = 4 * a * c - b^2
      mod(d, 8) == 7 && (h[d] += 1)
    end
  end
  return h
end

# The order of [BLS12], Section 6.6, for an odd prime l, with the small prime
# l0 = 2 ("typically l0 = 2") and the bound b = 59, so that every Phi_q used,
# q <= b, is in the database. The discriminant of O is D = u^2 d_K, with
# (1) d_K < -4 fundamental, (d_K/l) = 1, h(d_K) <= b and u b-smooth, and
# h(O) >= l + 2, so that a root of H_O comes from one of H_{O_K}
# (_descend_to_order); here also (d_K/2) = 1 and u odd (2 splits in O, O is
# maximal at 2), and l^2 |D| + 4 <= 4 typemax(Int), else no prime of the CRT
# fits an Int; (2) cl(O) and cl(R), R = Z + l O, generated by the class of an
# ideal of norm 2 or by it and that of a ramified prime l1 <= b
# (_class_group_presentation). As Section 6.6 does, for each d_K the
# conductors u at which h(u^2 d_K) is "slightly greater than l + 2" are
# tested by (2), and of those that pass the order of least h(O), then least
# |D|. The candidates are those of _modular_polynomial_conductors for each
# d_K up to _class_number_at_most_59_max_disc, each tested once: about 10^4
# at level 61 and 3.5 * 10^5 at level 7411, all of them tested in 4 s and
# 3 minutes; if none passes, an ArgumentError.
function _modular_polynomial_order(l::Int)
  dmax = div(4 * Int128(typemax(Int)) - 4, Int128(l)^2)
  primes_u = [r for r in 3:59 if is_prime(r) && r != l]
  N = Int(min(_class_number_at_most_59_max_disc, dmax))
  hs = _class_numbers_1_mod_8(N)
  # (h(O), |D|, d, u)
  cands = Tuple{Int, Int, Int, Int}[]
  for d in 7:8:N
    (hs[d] <= 59 && is_fundamental_discriminant(-d) &&
     kronecker_symbol(-d, l) == 1) || continue
    for (h, u) in _modular_polynomial_conductors(l, d, Int(hs[d]), primes_u,
                                                 dmax)
      push!(cands, (h, u^2 * d, d, u))
    end
  end
  sort!(cands)
  for (h, _, d, u) in cands
    ord = _modular_polynomial_order_presentation(l, -d, u, h)
    ord === nothing || return ord
  end
  throw(ArgumentError("No order of Broker-Lauter-Sutherland's family for " *
                      "level $l fits the word size"))
end

# The conductors u for d_K = -d with h(d_K) = h0 at which h(u^2 d_K) first
# reaches l + 2, as (h(u^2 d_K), u): u is built from the primes in primes_u
# in increasing order, each u once, by
# h(u^2 d_K) = h0 u prod_{r | u} (1 - (d_K/r)/r) ([BLS12], (5)), and is not
# extended once h(u^2 d_K) >= l + 2 (h only grows with u). Ends: u grows by
# a factor r >= 3 at each step, and u^2 d <= dmax.
function _modular_polynomial_conductors(l::Int, d::Int, h0::Int,
                                        primes_u::Vector{Int}, dmax::Int128)
  res = Tuple{Int, Int}[]
  stack = [(1, h0, 1)]
  while !isempty(stack)
    u, h, i = pop!(stack)
    if h >= l + 2
      push!(res, (h, u))
      continue
    end
    for k in i:length(primes_u)
      r = primes_u[k]
      Int128(u * r)^2 * d <= dmax || break
      hh = h * (is_divisible_by(u, r) ? r : r - kronecker_symbol(-d, r))
      push!(stack, (u * r, hh, k))
    end
  end
  return res
end

# The data of _modular_polynomial_order for the candidate D0 = d_K, u, h, or
# nothing: l1 = 0 (no second generator) or a prime l1 <= 59 dividing D0, not
# dividing u l (ramified in O), tried in this order; the presentations of
# cl(O) and cl(R); e, the exponents of the class of an ideal of norm l in
# cl(O); kappa, those of a generator of the kernel of cl(R) -> cl(O).
function _modular_polynomial_order_presentation(l::Int, D0::Int, u::Int,
                                                h::Int)
  D = ZZ(u)^2 * D0
  dR = ZZ(l)^2 * D
  # h(R) = (l - 1) h, as l splits and O* = R* = {1, -1}
  hR = (l - 1) * h
  ram = [q for q in 3:59 if is_prime(q) && q != l &&
                            is_divisible_by(D0, q) && !is_divisible_by(u, q)]
  for l1 in (0, ram...)
    PO = _class_group_presentation(D, h, 2, l1)
    PO === nothing && continue
    PR = _class_group_presentation(dR, hR, 2, l1)
    PR === nothing && continue
    return (D = Int(D), D0 = D0, u = u, h = h, l1 = l1, PO = PO, PR = PR,
            e = _class_group_exponents(PO, _prime_form_class(D, l)),
            kappa = _class_group_exponents(PR,
                                           _class_group_kernel_generator(D, l)))
  end
  return nothing
end

# The height bound of [BS10] for Phi_l: the smaller of Corollary 9 and
# Theorem 1, a bound for log max |c| over the coefficients c (natural log).
function _modular_polynomial_height_bound(l::Int)
  return 6 * l * log(l) + min(18 * l, 16 * l + 14 * sqrt(l) * log(l))
end

# The CRT primes of [BLS12], (12): p = (t^2 - v^2 l^2 D)/4 with t = 2 mod l,
# v >= 1 and l not dividing v, which split completely in the ray class field
# of conductor l of O and not in the ring class field of Z + l^2 O
# (Theorem 4.1). Also gcd(v, D) = 1, so that l1 and the primes q | u, which
# divide D, do not divide v: the l1-volcanoes have depth 0 (Section 4.3) and
# the q-volcanoes depth v_q(u) (_descend_to_order); v is even, as D = 1 mod 8,
# and not divisible by 4, so that the 2-volcanoes have depth 1; l^3 does not
# divide p + 1 - t, so that the l-Sylow subgroup of the curves of
# Algorithm 2.1 is E[l]. With t and v varying such primes have
# positive density (Theorem 4.4); the smallest are taken, until their product
# exceeds 4 exp(B), B the height bound, as the explicit CRT needs
# (Section 6.2); the summand 1 absorbs rounding in the logarithms. The bound Y
# on p doubles up to typemax(Int), so the loop ends; beyond it, an
# ArgumentError.
function _modular_polynomial_crt_primes(l::Int, D::Int)
  target = _modular_polynomial_height_bound(l) + log(4) + 1
  W = Int128(typemax(Int))
  Y = max(div(Int128(l)^2 * abs(D), 4), Int128(1))
  # ends: Y doubles until it reaches W
  while true
    Y = min(Y, W)
    ps = _modular_polynomial_crt_primes_upto(l, D, Y)
    s = 0.0
    for k in eachindex(ps)
      s += log(ps[k][1])
      s > target && return ps[1:k]
    end
    @req Y < W "Level $l is too large: the primes of the Chinese remainder " *
               "theorem exceed the word size"
    Y = 2 * Y
  end
end

# The primes of _modular_polynomial_crt_primes up to Y, with their traces t,
# in increasing order. v runs while v^2 l^2 |D| <= 4Y and t over the
# residues 2 mod l with t^2 <= 4Y, so both loops are finite.
function _modular_polynomial_crt_primes_upto(l::Int, D::Int, Y::Int128)
  w = Int128(l)^2 * abs(D)
  ps = Tuple{Int, Int}[]
  v = 0
  while true
    v += 1
    r = 4 * Y - Int128(v)^2 * w
    r < 0 && break
    (is_divisible_by(v, l) || is_divisible_by(v, 4) ||
     !isone(gcd(ZZ(v), ZZ(D)))) && continue
    tmax = isqrt(r)
    # t = 2 + k l with |t| <= tmax
    for k in -div(tmax + 2, l):div(tmax - 2, l)
      t = 2 + k * l
      abs(t) <= tmax || continue
      q4 = Int128(t)^2 + Int128(v)^2 * w
      iszero(mod(q4, 4)) || continue
      p = Int(div(q4, 4))
      is_prime(p) || continue
      is_divisible_by(ZZ(p) + 1 - t, ZZ(l)^3) && continue
      push!(ps, (p, t))
    end
  end
  sort!(ps)
  # the trace t = 2 mod l fixes the Frobenius up to conjugation, so a prime
  # comes from one pair (t, v) only
  @assert allunique(first.(ps))
  return ps
end

# Phi_l(X, Y) as the table of its coefficients, the entry [a + 1, b + 1] that
# of X^a Y^b, for l <= 59.
function _modular_polynomial_table(l::Int)
  phi = classical_modular_polynomial(l)
  T = zero_matrix(ZZ, l + 2, l + 2)
  for (c, e) in zip(coefficients(phi), exponent_vectors(phi))
    T[e[1] + 1, e[2] + 1] = c
  end
  return T
end

# Phi(X, j) in Fx, T the table of Phi over F_p: the table times the vector of
# powers of j, by FLINT.
function _modular_polynomial_at(Fx::fpPolyRing, T::fpMatrix, j::fpFieldElem)
  pw = Vector{UInt}(undef, ncols(T))
  x = one(j)
  for b in eachindex(pw)
    pw[b] = data(x)
    x *= j
  end
  return Fx(mul!(Vector{UInt}(undef, nrows(T)), T, pw))
end

# The n j-invariants j_0, j_1, ... of the 2-isogeny cycle from j0 on the
# surface of its 2-volcano of depth 1 ([Sut11], Section 4.2, WalkSurfacePath
# with d = 1); j_1 is second if given (one of the two surface neighbours of
# j0), else either. A surface vertex j_k has three neighbours: j_{k-1},
# j_{k+1} and one on the floor, which has no neighbour but j_k. So of the two
# steps from j_k that do not go back (_next_2_isogeny_step, the quadratic
# formula), j_{k+1} is the one from which a path goes on, and the steps from
# it are the next candidates.
function _isogeny_cycle(Fx::fpPolyRing, j0, n::Int; second = nothing)
  if second === nothing
    # the first step, once per cycle: a surface root of Phi_2(j0, X)
    a, b, c = _modular_polynomial_2(j0)
    X = gen(Fx)
    second = first(r for r in roots(X^3 + a * X^2 + b * X + c)
                   if _next_2_isogeny_step(r, j0) !== nothing)
  end
  J = [j0, second]
  next = _next_2_isogeny_step(second, j0)
  # ends: one j-invariant more at each step
  while length(J) < n
    c1, c2 = next
    c = c1
    next = _next_2_isogeny_step(c1, J[end])
    if next === nothing
      c = c2
      next = _next_2_isogeny_step(c2, J[end])
    end
    push!(J, c)
  end
  return J
end

# The codomain of the l-isogeny with kernel generated by the point P of order
# l on y^2 = x^3 + A x + B: Velu's formulas as in Algorithm 6.4 of [BLS12].
function _velu_codomain(A, B, P, l::Int)
  t = zero(A)
  w = zero(A)
  Q = set!(infinity(parent(P)), P)
  for _ in 1:div(l - 1, 2)
    s = 6 * Q[1]^2 + 2 * A
    t += s
    w += 4 * Q[2]^2 + s * Q[1]
    add!(Q, Q, P)
  end
  return A - 5 * t, B - 7 * w
end

_short_weierstrass_j_invariant(A, B) = 6912 * A^3 // (4 * A^3 + 27 * B^2)

# Step 4 of Algorithm 2.1: an l-isogenous curve of j with endomorphism ring R,
# that is, whose j-invariant is not on the surface. The curve
# y^2 = x^3 + 3k x + 2k with k = j/(1728 - j) has j-invariant j; it or its
# quadratic twist by the non-square c has trace t, and Section 6.3 tells
# which by generating a point of order l: on the curve of trace t the l-Sylow
# subgroup is E[l] (Theorem 4.1; l^3 does not divide N = p + 1 - t), so
# P = (N/l^2) Q is a uniform point of E[l], while the twist has
# p + 1 + t = 4 mod l points and no point of order l.
function _floor_isogenous_j_invariant(F, j, p::Int, t::Int, l::Int, c, surface)
  k = j // (1728 - j)
  A, B = 3 * k, 2 * k
  E = elliptic_curve(F, [A, B])
  n = Int(divexact(ZZ(p) + 1 - t, l^2))
  # ends with probability 1: on the curve of trace t, P != 0 with probability
  # 1 - 1/l^2, and at most 2 of the l + 1 subgroups of order l lead to the
  # surface (Section 6.3); on the twist, a P != 0 has l P != 0, so the twist
  # is left at the first such P
  while true
    P = n * rand(E)
    is_infinite(P) && continue
    if !is_infinite(l * P)
      A, B = A * c^2, B * c^3
      E = elliptic_curve(F, [A, B])
      continue
    end
    jc = _short_weierstrass_j_invariant(_velu_codomain(A, B, P, l)...)
    haskey(surface, jc) || return jc
  end
end

# The CM torsor of a class group with presentation P ([BLS12], Sections 5.3
# and 6.6) from j0: the j-invariants j0 g0^x0 g1^x1 as C[x1 + 1][x0 + 1],
# 0 <= x0 < P.n, by 2-isogeny cycles. If P is split, the second cycle starts
# at the only root of Phi_{l1}(X, j0) in F_p (T1; l1 ramified and its volcano
# of depth 0) and is oriented as the first by the only root of
# Phi_{l1}(X, C[1][2]), a 2-neighbour of that start: one extra l1-isogeny, as
# in Section 6.6.
function _cm_torsor(Fx::fpPolyRing, T1, j0, P)
  C = [_isogeny_cycle(Fx, j0, P.n)]
  P.g1 === nothing && return C
  a = _only_root(_modular_polynomial_at(Fx, T1, j0))
  b = _only_root(_modular_polynomial_at(Fx, T1, C[1][2]))
  push!(C, _isogeny_cycle(Fx, a, P.n; second = b))
  return C
end

function _only_root(f::PolyRingElem)
  r = roots(f)
  @assert length(r) == 1
  return r[1]
end

# A j-invariant with endomorphism ring O from a root j of H_{O_K} in F_p, as
# condition (1) of [BLS12], Section 6.6 allows: for each prime q | u, the
# floor of the q-volcano of j, whose depth is v_q(u), as the conductor of
# Z[pi] is u l v and q divides neither l nor v. A walk in a q-volcano changes
# only the q-part of the conductor of the endomorphism ring ([Sut11],
# Proposition 2), so H_O itself is never needed.
function _descend_to_order(Fx::fpPolyRing, T::Dict{Int, fpMatrix},
                           j::fpFieldElem, u::Int)
  for (q, d) in factor(u)
    j = _volcano_floor(Fx, T[q], j, d)
  end
  return j
end

# A vertex on the floor of the q-volcano of depth d >= 1 of j, from j on its
# surface ([Sut11], Section 4.1, Algorithm Descend). A path that never steps
# back and has left the surface goes down at every step, so it reaches the
# floor, where a vertex has no neighbour but its parent, after d steps; a
# path that starts along the surface does not. At most two neighbours of j
# lie on the surface, so one of the first three gives the floor.
function _volcano_floor(Fx::fpPolyRing, T::fpMatrix, j::fpFieldElem, d::Int)
  X = gen(Fx)
  cofactor(c, prev) = divexact(_modular_polynomial_at(Fx, T, c), X - prev)
  for c in Iterators.take(roots(_modular_polynomial_at(Fx, T, j)), 3)
    prev, cur = j, c
    for _ in 2:d
      prev, cur = cur, first(roots(cofactor(cur, prev)))
    end
    isempty(roots(cofactor(cur, prev))) && return cur
  end
  error("no path to the floor of the volcano")
end

# The polynomials in Y of degree below n = length(nodes) through the points
# (nodes[i], A[i, k]), one for each column k of A, as the columns of the
# result (constant term first): Step 7 of Algorithm 2.1 of [BLS12], by fast
# interpolation on the product tree of the nodes, as in its Section 6.5, by
# FLINT. The tree and the interpolation weights depend only on the nodes, so
# they are built once for all columns.
function _interpolate_columns(F::fpField, nodes::Vector{fpFieldElem},
                              A::Matrix{UInt})
  n = length(nodes)
  @assert size(A, 1) == n
  m = Nemo.nmod_t(F)
  xs = UInt[data(x) for x in nodes]
  w = Vector{UInt}(undef, n)
  C = similar(A)
  tree = @ccall libflint._nmod_poly_tree_alloc(n::Int)::Ptr{Ptr{UInt}}
  try
    GC.@preserve xs w A C begin
      @ccall libflint._nmod_poly_tree_build(tree::Ptr{Ptr{UInt}},
        pointer(xs)::Ptr{UInt}, n::Int, m::Nemo.nmod_t)::Nothing
      @ccall libflint._nmod_poly_interpolation_weights(pointer(w)::Ptr{UInt},
        tree::Ptr{Ptr{UInt}}, n::Int, m::Nemo.nmod_t)::Nothing
      for k in axes(A, 2)
        o = (k - 1) * n + 1
        @ccall libflint._nmod_poly_interpolate_nmod_vec_fast_precomp(
          pointer(C, o)::Ptr{UInt}, pointer(A, o)::Ptr{UInt},
          tree::Ptr{Ptr{UInt}}, pointer(w)::Ptr{UInt}, n::Int,
          m::Nemo.nmod_t)::Nothing
      end
    end
  finally
    @ccall libflint._nmod_poly_tree_free(tree::Ptr{Ptr{UInt}}, n::Int)::Nothing
  end
  return C
end

# Algorithm 2.1 of [BLS12]: the triangle of Phi_l mod p, for a prime p of
# _modular_polynomial_crt_primes with trace t. The surface Ell_O(F_p) is the
# CM torsor of cl(O), the l-neighbours of the curve at x on it are at x +- e;
# the floor Ell_R(F_p) is that of cl(R), and the floor l-neighbours of a
# surface curve are the coset y + <kappa> of one of them, y, under the kernel
# of cl(R) -> cl(O), of order l - 1 (Lemmas 3.1 and 3.2). Phi_l(X, j) is the
# product over the l + 1 neighbours, for l + 2 of the surface curves; then
# interpolation in Y.
function _modular_polynomial_mod_p(l::Int, ord, HK::ZZPolyRingElem,
                    tables::Dict{Int, ZZMatrix}, p::Int, t::Int)
  F = Native.GF(p; cached = false)
  Fx, X = polynomial_ring(F, :X; cached = false)
  T = Dict(q => change_base_ring(F, M) for (q, M) in tables)
  T1 = ord.l1 == 0 ? nothing : T[ord.l1]
  PO, PR = ord.PO, ord.PR
  at(C, x) = C[x[2] + 1][x[1] + 1]
  points(P, C) = Iterators.product(0:(P.n - 1), 0:(length(C) - 1))
  c = F(2)
  # ends: p is odd, so F_p has a non-square
  while is_square(c)
    c += 1
  end
  jK = first(roots(map_coefficients(F, HK; parent = Fx)))
  J = _cm_torsor(Fx, T1, _descend_to_order(Fx, T, jK, ord.u), PO)
  surface = Dict(at(J, x) => x for x in points(PO, J))
  @assert length(surface) == ord.h
  nodes = [at(J, x) for x in points(PO, J)][1:(l + 2)]
  children = [_floor_isogenous_j_invariant(F, j, p, t, l, c, surface)
              for j in nodes]
  JR = _cm_torsor(Fx, T1, children[1], PR)
  floor = Dict(at(JR, y) => y for y in points(PR, JR))
  @assert length(floor) == (l - 1) * ord.h
  A = Matrix{UInt}(undef, l + 2, l + 2)
  for i in 1:(l + 2)
    x = surface[nodes[i]]
    nbrs = [at(J, _class_group_exponents_add(PO, x, ord.e, 1)),
            at(J, _class_group_exponents_add(PO, x, ord.e, -1))]
    y = floor[children[i]]
    append!(nbrs, at(JR, _class_group_exponents_add(PR, y, ord.kappa, s))
                  for s in 0:(l - 2))
    f = from_roots(Fx, nbrs)
    for a in 0:(l + 1)
      A[i, a + 1] = data(coeff(f, a))
    end
  end
  # B[b + 1, a + 1] is the coefficient of X^a Y^b
  B = _interpolate_columns(F, nodes, A)
  res = Vector{Int}(undef, _triangle_index(l + 1, l + 1))
  for a in 0:(l + 1), b in 0:a
    res[_triangle_index(a, b)] = Int(B[b + 1, a + 1])
  end
  return res
end

# The data that every prime needs: H_{O_K} over Z (Nemo's, of degree
# h(d_K) <= 59; Step 1 of Algorithm 6.1 with Section 6.6) and the coefficient
# tables of Phi_{l1} and of Phi_q for the primes q | u.
function _modular_polynomial_crt_setup(ord)
  Zx, _ = polynomial_ring(ZZ, :x; cached = false)
  HK = hilbert_class_polynomial(ord.D0, Zx)
  qs = [ord.l1 == 0 ? Int[] : [ord.l1]; [q for (q, _) in factor(ord.u)]]
  return HK, Dict(q => _modular_polynomial_table(q) for q in qs)
end

# The triangle of Phi_l over Z: the residues of every prime, then the CRT with
# symmetric residues, the product of the primes exceeding twice every
# coefficient ([BLS12], Section 6.2).
function _modular_polynomial_coefficients(l::Int, ord,
                                          ps::Vector{Tuple{Int, Int}})
  HK, tables = _modular_polynomial_crt_setup(ord)
  n = _triangle_index(l + 1, l + 1)
  res = Matrix{Int}(undef, n, length(ps))
  for (i, (p, t)) in enumerate(ps)
    res[:, i] = _modular_polynomial_mod_p(l, ord, HK, tables, p, t)
  end
  env = crt_env(ZZRingElem[ZZ(p) for (p, _) in ps])
  b = ZZRingElem[ZZ() for _ in ps]
  c = Vector{ZZRingElem}(undef, n)
  for k in 1:n
    for i in eachindex(ps)
      set!(b[i], res[k, i])
    end
    c[k] = crt_signed(b, env)
  end
  return c
end

# The triangle of Phi_l mod m by the explicit CRT ([BLS12], Section 6.2;
# [Sut11], Section 6): with M the product of the primes p_i, M_i = M/p_i and
# a_i = 1/M_i mod p_i, every coefficient c of Phi_l satisfies
# c = sum_i d_i M_i - r M with d_i = c a_i mod p_i, where r is the integer
# closest to s = sum_i d_i/p_i, as M > 4|c| (Bernstein). Only C = sum d_i M_i
# mod m and s are kept, so the memory is that of Phi_l mod m. In double
# precision each summand of s has error below 3 * 2^-53, and the sum of n
# summands below n (n + 3) 2^-53, under the 1/4 that rounding to r tolerates
# when n < 2^25.
function _modular_polynomial_coefficients_mod(l::Int, ord,
                                              ps::Vector{Tuple{Int, Int}},
                           m::ZZRingElem)
  @assert length(ps) < 2^25
  HK, tables = _modular_polynomial_crt_setup(ord)
  n = _triangle_index(l + 1, l + 1)
  M = prod(ZZ(p) for (p, _) in ps)
  C = ZZRingElem[ZZ() for _ in 1:n]
  s = zeros(Float64, n)
  for (p, t) in ps
    Mi = divexact(M, p)
    ai = Int(invmod(mod(Mi, p), ZZ(p)))
    Mim = mod(Mi, m)
    r = _modular_polynomial_mod_p(l, ord, HK, tables, p, t)
    for k in 1:n
      d = Int(mod(Int128(r[k]) * ai, p))
      addmul!(C[k], Mim, d)
      s[k] += d / p
    end
    for k in 1:n
      mod!(C[k], m)
    end
  end
  Mm = mod(M, m)
  return ZZRingElem[mod(C[k] - round(Int, s[k]) * Mm, m) for k in 1:n]
end
