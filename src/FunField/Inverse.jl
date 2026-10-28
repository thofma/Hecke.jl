################################################################################
#
#  FunField/Inverse.jl : Inverses in function fields k(x)[y]/(f)
#
################################################################################

# Let F = k(x)[y]/(f) and a = A/c with A in k[x][y] of y-degree dA and c in
# k[x]; f = numerator(F) has y-degree n and need not be monic. Every nonzero a
# satisfies
#
#   a^-1 = c * B / N,   N = Res_y(A, f) in k[x],   B = N * A^-1 mod f,
#
# where B has y-degree < n. N and the coefficients of B are (up to sign)
# maximal minors and cofactors of the Sylvester matrix of A and f, which has
# dA rows of coefficients of f and n rows of coefficients of A. Hence:
#
# - deg_x N, deg_x B_i <= dA * df + n * da =: D - 1, where df and da bound the
#   x-degrees of the coefficients of f and A;
# - over Z, all coefficients of N and B are bounded by |f|_1^dA * |A|_1^n,
#   where |P|_1 is the sum of the absolute values of all coefficients of P.
#
# Instead of the extended Euclidean algorithm over k[x][y] (AbstractAlgebra's
# generic inv), N and B are computed by evaluation at x = alpha in F_p and
# interpolation, and over Q and number fields modulo many primes and lifted by
# the CRT. If the y-leading coefficients of f and A do not vanish at alpha,
# the Sylvester matrix specialises entrywise, so
# N(alpha) = Res(A(alpha), f(alpha)) and, if N(alpha) != 0,
# B(alpha) = N(alpha) * A(alpha)^-1 mod f(alpha). This is
# the modular approach to resultants and the extended Euclidean algorithm, see
# von zur Gathen, Gerhard, Modern Computer Algebra, Sections 5.2, 5.4 and 6.11,
# and, for algebraic function fields, van Hoeij, Monagan, "Algorithms for
# polynomial GCD computation over algebraic function fields", ISSAC 2004.

################################################################################
#
#  Dispatch
#
################################################################################

function inv(a::Generic.AbsSimpleFunctionFieldElem{T}) where {T <: Union{
    FqFieldElem, fpFieldElem, QQFieldElem, AbsSimpleNumFieldElem}}
  b = is_zero(a) ? nothing : _inv_modular(a)
  if b === nothing
    # not covered (or not invertible): AbstractAlgebra's generic algorithm
    return invoke(inv, Tuple{Generic.AbsSimpleFunctionFieldElem}, a)
  end
  return b
end

# a^-1 = c * B / N in canonical form
function _inv_from_cofactor(a::Generic.AbsSimpleFunctionFieldElem,
                            B::PolyRingElem, N::PolyRingElem)
  F = parent(a)
  c = denominator(a, false)
  num, den = Generic._rat_poly_canonicalise(B * c, N)
  return F(num, den)
end

function _inv_degree_bound(f::PolyRingElem, A::PolyRingElem)
  df = maximum(degree(coeff(f, i)) for i in 0:degree(f))
  da = maximum(degree(coeff(A, i)) for i in 0:degree(A))
  return degree(A) * df + degree(f) * da + 1
end

################################################################################
#
#  Over F_p: evaluation and interpolation
#
################################################################################

#=
Given the y-coefficients fy, ay of f and A over F_p[x] and the degree bound D,
return (N, [B_0, ..., B_(n-1)]) over F_p[x], or `nothing` if F_p does not have
D good evaluation points.
=#
function _inv_cofactor_eval(fy::Vector{fpPolyRingElem},
                            ay::Vector{fpPolyRingElem}, D::Int)
  Fpx = parent(fy[1])
  Fp = base_ring(Fpx)
  Fpy, _ = polynomial_ring(Fp, :y; cached = false)
  n = length(fy) - 1
  xs = elem_type(Fp)[]
  Nv = elem_type(Fp)[]
  Bv = [elem_type(Fp)[] for _ in 1:n]
  for i in 0:min(characteristic(Fp) - 1, ZZ(typemax(Int)))
    length(xs) == D && break
    alpha = Fp(i)
    fa = Fpy([evaluate(g, alpha) for g in fy])
    aa = Fpy([evaluate(g, alpha) for g in ay])
    (degree(fa) < n || degree(aa) < length(ay) - 1) && continue
    r = resultant(aa, fa)
    is_zero(r) && continue
    s = r * invmod(aa, fa)
    push!(xs, alpha)
    push!(Nv, r)
    for j in 1:n
      push!(Bv[j], coeff(s, j - 1))
    end
  end
  length(xs) < D && return nothing
  return interpolate(Fpx, xs, Nv), [interpolate(Fpx, xs, v) for v in Bv]
end

function _inv_modular(a::Generic.AbsSimpleFunctionFieldElem{T}) where {
    T <: Union{FqFieldElem, fpFieldElem}}
  F = parent(a)
  kx = parent(denominator(a, false))
  k = base_ring(kx)
  if k isa FqField
    # only prime fields of word-size characteristic
    (degree(k) == 1 && fits(UInt, characteristic(k))) || return nothing
    Fp = Native.GF(UInt(characteristic(k)); cached = false)
    to_fp = c -> Fp(lift(ZZ, c))
    from_fp = c -> k(lift(c))
  else
    Fp = k
    to_fp = from_fp = identity
  end
  Fpx, _ = polynomial_ring(Fp, :x; cached = false)
  f = numerator(F)
  A = numerator(a, false)
  D = _inv_degree_bound(f, A)
  # not enough points for small p
  D <= characteristic(Fp) || return nothing
  fy = [map_coefficients(to_fp, coeff(f, i); parent = Fpx) for i in 0:degree(f)]
  ay = [map_coefficients(to_fp, coeff(A, i); parent = Fpx) for i in 0:degree(A)]
  res = _inv_cofactor_eval(fy, ay, D)
  res === nothing && return nothing
  N, B = res
  N = map_coefficients(from_fp, N; parent = kx)
  B = parent(f)([map_coefficients(from_fp, b; parent = kx) for b in B])
  return _inv_from_cofactor(a, B, N)
end

################################################################################
#
#  Over Q: multimodular
#
################################################################################

# polynomials over Q scaled by a common integer to polynomials over Z
function _integral_scaling(Zx::ZZPolyRing, qs::Vector{QQPolyRingElem})
  d = reduce(lcm, (denominator(q) for q in qs); init = ZZ(1))
  return [numerator(d * q, Zx) for q in qs], d
end

# upper bound for the sum of the absolute values of the coefficients
_norm_1(g::ZZPolyRingElem) = (degree(g) + 1) * height(g)

# Number of consecutive bad primes after which a is treated as not invertible
const _INV_MAX_BAD_PRIMES = 20

function _inv_modular(a::Generic.AbsSimpleFunctionFieldElem{QQFieldElem})
  F = parent(a)
  # for extensions of small degree the generic algorithm is faster
  degree(F) <= 3 && return nothing
  Qx = parent(denominator(a, false))
  Zx = Globals.Zx
  f = numerator(F)
  A = numerator(a, false)
  D = _inv_degree_bound(f, A)
  fz, _ = _integral_scaling(Zx, [coeff(f, i) for i in 0:degree(f)])
  az, s = _integral_scaling(Zx, [coeff(A, i) for i in 0:degree(A)])
  bound = sum(_norm_1, fz)^degree(A) * sum(_norm_1, az)^degree(f)
  # N and B modulo primes p until their product exceeds 2 * bound
  primes = ZZRingElem[]
  Ns = fpPolyRingElem[]
  Bs = Vector{fpPolyRingElem}[]
  M = ZZ(1)
  bad = 0
  for p in PrimesSet(p_start, -1)
    M > 2 * bound && break
    Fp = Native.GF(p; cached = false)
    Fpx, _ = polynomial_ring(Fp, :x; cached = false)
    red = g -> change_base_ring(Fp, g; parent = Fpx)
    res = _inv_cofactor_eval(red.(fz), red.(az), D)
    if res === nothing
      bad += 1
      bad > _INV_MAX_BAD_PRIMES && return nothing
      continue
    end
    bad = 0
    push!(primes, ZZ(p))
    push!(Ns, res[1])
    push!(Bs, res[2])
    M *= p
  end
  # symmetric lift by the CRT
  ce = crt_env(primes)
  lift_Q = L -> change_base_ring(QQ, mod_sym!(induce_crt(L, ce; parent = Zx),
                                              M); parent = Qx)
  N = lift_Q(Ns)
  B = [lift_Q([b[i] for b in Bs]) for i in 1:degree(f)]
  # a^-1 = c / A = c s / (s A) = c s B / N
  return _inv_from_cofactor(a, parent(f)([s * b for b in B]), N)
end

################################################################################
#
#  Over number fields: multimodular with totally split primes
#
################################################################################

# For K = Q(theta) with monic integral defining polynomial and c in Z[theta],
# let |c| be the sum of the absolute values of the coordinates of c in the
# power basis, and |P| the sum of |coefficients| for P in Z[theta][x]. Then
# |PQ| <= mu |P| |Q| with mu = max_{0 <= l, m < d} |theta^(l + m)|, so the
# coordinates of N and B are bounded by
#   mu^(dA + n - 1) * |f|_1^dA * |A|_1^n.
function _power_basis_mu(K::AbsSimpleNumField)
  th = gen(K)
  mu = ZZ(1)
  for e in 0:2 * degree(K) - 2
    c = th^e
    mu = max(mu, sum(abs(numerator(coeff(c, l))) for l in 0:degree(K) - 1))
  end
  return mu
end

function _norm_1(c::AbsSimpleNumFieldElem)
  return sum(abs(numerator(coeff(c, l))) for l in 0:degree(parent(c)) - 1)
end

_norm_1(g::Generic.Poly{AbsSimpleNumFieldElem}) =
  sum(_norm_1, coefficients(g); init = ZZ(0))

function _integral_scaling(qs::Vector{Generic.Poly{AbsSimpleNumFieldElem}})
  d = ZZ(1)
  for q in qs, c in coefficients(q)
    d = lcm(d, denominator(c))
  end
  return [d * q for q in qs], d
end

function _inv_modular(
    a::Generic.AbsSimpleFunctionFieldElem{AbsSimpleNumFieldElem})
  F = parent(a)
  Kx = parent(denominator(a, false))
  K = base_ring(Kx)
  g = defining_polynomial(K)
  # Z[theta] must be a ring, so that N and B have integral coordinates
  (is_monic(g) && isone(denominator(g))) || return nothing
  d = degree(K)
  f = numerator(F)
  A = numerator(a, false)
  D = _inv_degree_bound(f, A)
  fz, _ = _integral_scaling([coeff(f, i) for i in 0:degree(f)])
  az, s = _integral_scaling([coeff(A, i) for i in 0:degree(A)])
  bound = _power_basis_mu(K)^(degree(A) + degree(f) - 1) *
          sum(_norm_1, fz)^degree(A) * sum(_norm_1, az)^degree(f)
  N = Kx()
  B = [Kx() for _ in 1:degree(f)]
  M = ZZ(1)
  bad = 0
  for p in PrimesSet(p_start, -1)
    M > 2 * bound && break
    local me
    try
      me = modular_init(K, p; deg_limit = 1)
    catch e
      e isa BadPrime || rethrow()
      continue
    end
    # only primes that split completely
    (isdefined(me, :fld) && length(me.fld) == d) || continue
    Fpx, _ = polynomial_ring(Native.GF(p; cached = false), :x; cached = false)
    # projections to the residue fields F_p[x] at the d roots
    Fp = base_ring(Fpx)
    to_fp = h -> map_coefficients(c -> Fp(coeff(c, 0)), h; parent = Fpx)
    fp = [to_fp.(modular_proj(h, me)) for h in fz]
    ap = [to_fp.(modular_proj(h, me)) for h in az]
    res = [_inv_cofactor_eval([u[j] for u in fp], [u[j] for u in ap], D)
           for j in 1:d]
    if any(isnothing, res)
      bad += 1
      bad > _INV_MAX_BAD_PRIMES && return nothing
      continue
    end
    bad = 0
    # back to K[x] modulo p
    to_fq = (v, j) -> map_coefficients(c -> me.fld[j](lift(c)), v;
                                       parent = me.fldx[j])
    lift_K = v -> modular_lift([to_fq(v[j], j) for j in 1:d], me)
    Np = lift_K([r[1] for r in res])
    Bp = [lift_K([r[2][i] for r in res]) for i in 1:degree(f)]
    # symmetric representatives modulo M * p
    q = ZZ(p)
    N, _ = induce_crt(N, M, Np, q, true)
    B = [induce_crt(B[i], M, Bp[i], q, true)[1] for i in 1:length(B)]
    M *= q
  end
  return _inv_from_cofactor(a, parent(f)([K(s) * b for b in B]), N)
end
