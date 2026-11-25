const default_class_mod_pol_db = joinpath(artifact"ClassicalModularPolynomialsDB", "ClassicalModularPolynomialsDB", "data")

const _classical_modular_polynomial_cache = Dict{Any, Any}()

@doc raw"""
    classical_modular_polynomial([R::MPolyRing,] n::Int) -> Poly

Returns the classical modular polynomial of level $n as an element of
$\mathbf{Z}[x, y]$. If an optional bivariate polynomial $R$ is specified,
the polynomial will be evaluated at the variables of $R$.

Modular polynomials of level up to `59` are read from a database. For a prime
level $n > 59$ the polynomial is computed by the algorithm of
[BLS12](@cite), from isogeny volcanoes over finite fields and the Chinese
remainder theorem, with the height bound of [BS10](@cite). If the base ring
of $R$ has positive characteristic $m$, the polynomial is computed modulo $m$
by the explicit Chinese remainder theorem [Sut11](@cite), so that the memory
used is that of the result (for $m$ beyond the product of the primes used,
over $\mathbf{Z}$ and then reduced). The result is always correct; only the
running time depends on random choices. Under the GRH it grows like $n^3$ up
to logarithmic factors [BLS12](@cite): on a laptop, about 3 seconds for
$n = 61$, 20 seconds for $n = 101$ and 30 seconds for $n = 131$, whatever the
ring, and a few seconds more on the first call, for compilation. Composite
levels above `59` are not supported. Precomputed classical modular
polynomials of every level up to 400 and of prime level up to 1000 are
available at
<https://math.mit.edu/~drew/ClassicalModPolys.html>.

Results are cached for each ring and level.
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
    n > 59 && return Base.invokelatest(_classical_modular_polynomial_bls, R, n)
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
function _classical_modular_polynomial_bls(R::MPolyRing, l::Int)
  m = characteristic(base_ring(R))
  isone(m) && return zero(R)
  ord = _bls_order(l)
  ps = _bls_primes(l, ord.D)
  # For m = 0, and for m beyond the product of the primes, the coefficients
  # over Z are needed; they are computed once, in Zxy, and mapped.
  if iszero(m) || m > prod(ZZ(p) for (p, _) in ps)
    if R !== Globals.Zxy
      return _map_symmetric(R, classical_modular_polynomial(Globals.Zxy, l))
    end
    return _symmetric_from_triangle(R, l, _bls_crt(l, ord, ps))
  end
  return _symmetric_from_triangle(R, l, _bls_explicit_crt(l, ord, ps, m))
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

# The order of [BLS12], Section 6.6, with conductor 1: the maximal order O of
# discriminant D, the first fundamental discriminant D < -4 by |D| with
# (D/l) = 1, so that O is not Z[i] or Z[zeta_3] and l splits, with
# l + 2 <= h(O) <= 5(l + 2)/4, and with cl(O) and cl(R), R = Z + l O,
# generated by the class of one prime ideal of odd prime norm l0 <= 59,
# l0 != l (Phi_{l0} is in the database), so that the walks never need to tell
# an ideal from its inverse. The class groups are those of positive definite
# binary quadratic forms. The two ideals of norm l have classes [l0]^e and
# [l0]^(-e), with 2e != 0 mod h, so that the two l-isogenies of the surface
# lead to distinct curves.
function _bls_order(l::Int)
  d = 4
  while true
    d += 1
    D = -d
    is_fundamental_discriminant(D) || continue
    kronecker_symbol(D, l) == 1 || continue
    # h(O), from the definite branch of binary_quadratic_form_representatives
    h = length(_binary_quadratic_form_representatives_definite(ZZ(D), true,
                                                               true))
    l + 2 <= h && 4 * h <= 5 * (l + 2) || continue
    ord = _bls_order_presentation(D, h, l)
    ord === nothing || return ord
  end
end

# The class group of positive definite binary quadratic forms of discriminant
# d < 0, its elements the reduced forms: product, identity, inverse, power.
function _bls_mul(f::QuadBin{ZZRingElem}, g::QuadBin{ZZRingElem})
  return reduction(compose(f, g))
end

function _bls_one(d::ZZRingElem)
  b = mod(d, 2)
  return binary_quadratic_form(one(ZZ), b, divexact(b^2 - d, 4))
end

function _bls_inv(f::QuadBin{ZZRingElem})
  return reduction(binary_quadratic_form(f[1], -f[2], f[3]))
end

function _bls_pow(f::QuadBin{ZZRingElem}, n::Int)
  r = _bls_one(discriminant(f))
  x = f
  while n > 0
    isodd(n) && (r = _bls_mul(r, x))
    n >>= 1
    n > 0 && (x = _bls_mul(x, x))
  end
  return r
end

# Whether the class of f generates the class group, of order N.
function _bls_generates(f::QuadBin{ZZRingElem}, N::Int)
  e = _bls_one(discriminant(f))
  return all(_bls_pow(f, div(N, Int(q))) != e for (q, _) in factor(N))
end

# The k in [0, N) with [f]^k = [x], [f] of order N, by baby steps and giant
# steps.
function _bls_dlog(f::QuadBin{ZZRingElem}, x::QuadBin{ZZRingElem}, N::Int)
  m = isqrt(N) + 1
  baby = Dict{QuadBin{ZZRingElem}, Int}()
  y = _bls_one(discriminant(f))
  for j in 0:(m - 1)
    get!(baby, y, j)
    y = _bls_mul(y, f)
  end
  g = _bls_inv(_bls_pow(f, m))
  z = x
  i = 0
  while !haskey(baby, z)
    i += 1
    @assert i <= m
    z = _bls_mul(z, g)
  end
  return mod(i * m + baby[z], N)
end

_bls_prime_class(d::ZZRingElem, q::Int) = reduction(prime_form(d, ZZ(q)))

function _bls_order_presentation(D::Int, h::Int, l::Int)
  dO = ZZ(D)
  dR = ZZ(l)^2 * dO
  # h(R) = (l - 1) h, as l splits and O* = R* = {1, -1}
  hR = (l - 1) * h
  for l0 in 3:59
    (is_prime(l0) && l0 != l && kronecker_symbol(D, l0) == 1) || continue
    g = _bls_prime_class(dO, l0)
    _bls_generates(g, h) || continue
    gR = _bls_prime_class(dR, l0)
    _bls_generates(gR, hR) || continue
    e = _bls_dlog(g, _bls_prime_class(dO, l), h)
    iszero(mod(2 * e, h)) && continue
    return (D = D, h = h, l0 = l0, e = e,
            aux = _bls_auxiliary(dO, l, l0, g, h),
            auxR = _bls_auxiliary(dR, l, l0, gR, hR))
  end
  return nothing
end

# An auxiliary prime l1 for the walks by gcds of [ES10], Section 2.3: an odd
# prime l1 <= 59, l1 != l0, l, split, whose class is [l0]^k in the class group
# of discriminant d, of order N and generated by [l0] = [g], with
# 2 <= k <= N/2; the one with the least k, so that most steps of a walk can
# use it. Nothing if there is none.
function _bls_auxiliary(d::ZZRingElem, l::Int, l0::Int, g::QuadBin{ZZRingElem},
                        N::Int)
  best = nothing
  for l1 in 3:59
    (is_prime(l1) && l1 != l0 && l1 != l && kronecker_symbol(d, l1) == 1) ||
      continue
    x = _bls_dlog(g, _bls_prime_class(d, l1), N)
    k = min(x, N - x)
    k >= 2 || continue
    if best === nothing || k < best[2]
      best = (l1, k)
    end
  end
  return best
end

# The height bound of [BS10] for Phi_l: the smaller of Corollary 9 and
# Theorem 1, a bound for log max |c| over the coefficients c (natural log).
function _bls_height_bound(l::Int)
  return 6 * l * log(l) + min(18 * l, 16 * l + 14 * sqrt(l) * log(l))
end

# The CRT primes of [BLS12], Section 6.1: 4p = t^2 - v^2 l^2 D with
# t = 2 mod l, v = 2 if D = 1 mod 8 and v = 1 otherwise, so l does not divide
# v; t runs through 2, 2 +- l, 2 +- 2l, ... Primes with l^3 | p + 1 - t are
# skipped: there the l-Sylow subgroup of the curves of Algorithm 2.1 is larger
# than E[l], which the construction of points of order l relies on. The
# product of the primes exceeds 4 exp(B), B the height bound, as the explicit
# CRT needs (Section 6.2); the summand 1 absorbs rounding in the logarithms.
function _bls_primes(l::Int, D::Int)
  v = mod(D, 8) == 1 ? 2 : 1
  target = _bls_height_bound(l) + log(4) + 1
  ps = Tuple{Int, Int}[]
  s = 0.0
  k = 0
  while s <= target
    for t in (k == 0 ? (2,) : (2 + k * l, 2 - k * l))
      iseven(t - v * D) || continue
      q = divexact(ZZ(t)^2 - ZZ(v)^2 * ZZ(l)^2 * D, 4)
      @req fits(Int, q) "Level $l is too large: it needs primes beyond " *
                        "the word size"
      p = Int(q)
      is_prime(p) || continue
      is_divisible_by(ZZ(p + 1 - t), ZZ(l)^3) && continue
      push!(ps, (p, t))
      s += log(p)
      s > target && break
    end
    k += 1
  end
  return ps
end

# Phi_{l0}(X, j) for j in F, from the coefficient table T of Phi_{l0} over F:
# T[a + 1, b + 1] the coefficient of X^a Y^b.
function _bls_specialize(Fx::PolyRing, T::Matrix, pw::Vector)
  n = size(T, 1)
  return Fx([sum(T[a, b] * pw[b] for b in 1:n) for a in 1:n])
end

# The n j-invariants j_0, j_1, ... of an l0-isogeny cycle from j0, on a
# volcano of depth 0, where every vertex has exactly two l0-neighbours. With an
# auxiliary prime l1 of class [l0]^k (T1 the table of Phi_{l1}), j_i is also a
# root of Phi_{l1}(X, j_{i-k}), whichever way the walk goes, so a gcd of degree
# 1 gives it without root-finding ([ES10], Section 2.3); otherwise the roots
# are found.
function _bls_cycle(Fx::PolyRing, T::Matrix, j0, n::Int,
                    T1::Union{Nothing, Matrix} = nothing, k::Int = 0)
  X = gen(Fx)
  J = [j0]
  r = roots(_bls_specialize(Fx, T, powers(j0, size(T, 1) - 1)))
  @assert length(r) == 2
  push!(J, r[1])
  while length(J) < n
    f = _bls_specialize(Fx, T, powers(J[end], size(T, 1) - 1))
    f = divexact(f, X - J[end - 1])
    if T1 !== nothing && length(J) >= k
      pw = powers(J[end + 1 - k], size(T1, 1) - 1)
      g = gcd(f, _bls_specialize(Fx, T1, pw))
      if degree(g) == 1
        push!(J, -coeff(g, 0) // coeff(g, 1))
        continue
      end
    end
    r = roots(f)
    @assert length(r) == 1
    push!(J, r[1])
  end
  return J
end

# The codomain of the l-isogeny with kernel generated by the point P of order
# l on y^2 = x^3 + A x + B: Velu's formulas as in Algorithm 6.4 of [BLS12].
function _bls_velu_codomain(A, B, P, l::Int)
  t = zero(A)
  w = zero(A)
  Q = P
  for _ in 1:div(l - 1, 2)
    s = 6 * Q[1]^2 + 2 * A
    t += s
    w += 4 * Q[2]^2 + s * Q[1]
    Q += P
  end
  return A - 5 * t, B - 7 * w
end

_bls_j(A, B) = 6912 * A^3 // (4 * A^3 + 27 * B^2)

# Step 4 of Algorithm 2.1: an l-isogenous curve of j with endomorphism ring R,
# that is, whose j-invariant is not on the surface. Of the curve
# y^2 = x^3 + 3k x + 2k with k = j/(1728 - j), whose j-invariant is j, and its
# quadratic twist by the non-square c, the one with trace t is decided by a
# point killed by exactly one of p + 1 - t and p + 1 + t. Its l-Sylow subgroup
# is E[l] (Theorem 4.1, and l^3 does not divide p + 1 - t), so n Q with
# n = (p + 1 - t)/l^2 is a uniform point of E[l].
function _bls_floor_neighbour(F, j, p::Int, t::Int, l::Int, c, surface)
  k = j // (1728 - j)
  A, B = 3 * k, 2 * k
  N = ZZ(p + 1 - t)
  Nt = ZZ(p + 1 + t)
  E = elliptic_curve(F, [A, B])
  while true
    Q = rand(E)
    a, b = is_infinite(N * Q), is_infinite(Nt * Q)
    a == b && continue
    if b
      A, B = A * c^2, B * c^3
      E = elliptic_curve(F, [A, B])
    end
    break
  end
  n = divexact(N, l^2)
  while true
    P = n * rand(E)
    is_infinite(P) && continue
    jc = _bls_j(_bls_velu_codomain(A, B, P, l)...)
    haskey(surface, jc) || return jc
  end
end

# Algorithm 2.1 of [BLS12]: the triangle of Phi_l mod p, for a prime p of
# _bls_primes with trace t. The surface Ell_O(F_p) is one l0-cycle J of
# length h, the l-neighbours of J[i] on it are J[i +- e]; the floor Ell_R(F_p)
# is one l0-cycle of length (l - 1) h, and the floor l-neighbours of J[i] are
# the coset of one of them under the subgroup of order l - 1 generated by
# [l0]^h, positions h apart on that cycle (Lemmas 3.1 and 3.2). Phi_l(X, J[i])
# is the product over the l + 1 neighbours, for l + 2 of the J[i]; then
# interpolation in Y.
function _bls_mod_p(l::Int, ord, HO::ZZPolyRingElem,
                    tables::Dict{Int, Matrix{ZZRingElem}}, p::Int, t::Int)
  F = Native.GF(p; cached = false)
  Fx, X = polynomial_ring(F, :X; cached = false)
  h, e = ord.h, ord.e
  T = map(F, tables[ord.l0])
  walk(j0, n, aux) = aux === nothing ? _bls_cycle(Fx, T, j0, n) :
    _bls_cycle(Fx, T, j0, n, map(F, tables[aux[1]]), aux[2])
  c = F(2)
  while is_square(c)
    c += 1
  end
  J = walk(first(roots(map_coefficients(F, HO; parent = Fx))), h, ord.aux)
  surface = Dict(j => i for (i, j) in enumerate(J))
  @assert length(surface) == h
  children = [_bls_floor_neighbour(F, J[i], p, t, l, c, surface)
              for i in 1:(l + 2)]
  JR = walk(children[1], (l - 1) * h, ord.auxR)
  floor = Dict(j => i for (i, j) in enumerate(JR))
  @assert length(floor) == (l - 1) * h
  A = Matrix{elem_type(F)}(undef, l + 2, l + 2)
  for i in 1:(l + 2)
    k = mod(floor[children[i]] - 1, h)
    nbrs = [J[mod(i - 1 + e, h) + 1], J[mod(i - 1 - e, h) + 1]]
    append!(nbrs, JR[k + s * h + 1] for s in 0:(l - 2))
    f = from_roots(Fx, nbrs)
    for a in 0:(l + 1)
      A[i, a + 1] = coeff(f, a)
    end
  end
  nodes = J[1:(l + 2)]
  res = Vector{Int}(undef, _triangle_index(l + 1, l + 1))
  for a in 0:(l + 1)
    phi = interpolate(Fx, nodes, A[:, a + 1])
    for b in 0:a
      res[_triangle_index(a, b)] = Int(lift(coeff(phi, b)))
    end
  end
  return res
end

# The data that every prime needs: H_O over Z (Nemo's, from FLINT; Step 1 of
# Algorithm 6.1) and the coefficient tables of Phi_{l0} and of the auxiliary
# Phi_{l1}, T[a + 1, b + 1] the coefficient of X^a Y^b.
function _bls_setup(ord)
  Zx, _ = polynomial_ring(ZZ, :x; cached = false)
  HO = hilbert_class_polynomial(ord.D, Zx)
  tables = Dict{Int, Matrix{ZZRingElem}}()
  for q in (ord.l0, (a[1] for a in (ord.aux, ord.auxR) if a !== nothing)...)
    T = [ZZ() for _ in 1:(q + 2), _ in 1:(q + 2)]
    phi = classical_modular_polynomial(q)
    for (c, ex) in zip(coefficients(phi), exponent_vectors(phi))
      T[ex[1] + 1, ex[2] + 1] = c
    end
    tables[q] = T
  end
  return HO, tables
end

# The triangle of Phi_l over Z: the residues of every prime, then the CRT with
# symmetric residues, the product of the primes exceeding twice every
# coefficient ([BLS12], Section 6.2).
function _bls_crt(l::Int, ord, ps::Vector{Tuple{Int, Int}})
  HO, tables = _bls_setup(ord)
  n = _triangle_index(l + 1, l + 1)
  res = Matrix{Int}(undef, n, length(ps))
  for (i, (p, t)) in enumerate(ps)
    res[:, i] = _bls_mod_p(l, ord, HO, tables, p, t)
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
function _bls_explicit_crt(l::Int, ord, ps::Vector{Tuple{Int, Int}},
                           m::ZZRingElem)
  @assert length(ps) < 2^25
  HO, tables = _bls_setup(ord)
  n = _triangle_index(l + 1, l + 1)
  M = prod(ZZ(p) for (p, _) in ps)
  C = ZZRingElem[ZZ() for _ in 1:n]
  s = zeros(Float64, n)
  for (p, t) in ps
    Mi = divexact(M, p)
    ai = Int(invmod(mod(Mi, p), ZZ(p)))
    Mim = mod(Mi, m)
    r = _bls_mod_p(l, ord, HO, tables, p, t)
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
