################################################################################
#
#  FunField/Inverse.jl : Inverses in function fields k(x)[y]/(f)
#
################################################################################

# References
#
#   [Col71] G. E. Collins, The calculation of multivariate polynomial
#           resultants, J. ACM 18 (1971), 515-532.
#   [GG13]  J. von zur Gathen, J. Gerhard, Modern Computer Algebra, 3rd ed.,
#           Cambridge University Press, 2013.
#   [HM04]  M. van Hoeij, M. Monagan, Algorithms for polynomial GCD computation
#           over algebraic function fields, ISSAC 2004.
#
# Notation as in [GG13, Section 6.3]
#
# Algorithm
#
#   r and s are computed with Collins' modular method for
#   resultants [Col71], [GG13, Sections 5.5 and 6.11]:
#
#   - Over F_p, evaluate at D points u in F_p and interpolate
#     [GG13, Section 5.2]. If lc_y(g)(u) != 0 and lc_y(f)(u) != 0, the
#     Sylvester matrix of g(u), f(u) in F_p[y] is the image of Syl(g, f), so
#
#       r(u) = res(g(u), f(u)),  s(u) = r(u) g(u)^-1 mod f(u)
#
#     (the latter if r(u) != 0, which makes g(u) invertible modulo f(u).)
#     Points where one of these leading coefficients or r(u)
#     vanishes are skipped.
#   - Over Q, do this modulo word-size primes p and combine the results with
#     the Chinese Remainder Algorithm [GG13, Section 5.4], until the product
#     M of the primes exceeds 2B. Symmetric residues then give r and s.
#   - Over a number field K = Q(theta), use primes p that split completely in
#     Z[theta], so that Z[theta]/p = F_p^d, and proceed as over Q.
#
################################################################################

# Try the modular algorithm first.
# It returns `nothing` if it does not apply.
function inv(a::Generic.AbsSimpleFunctionFieldElem{T}) where {T <: Union{
    FqFieldElem, fpFieldElem, QQFieldElem, AbsSimpleNumFieldElem}}
  b = is_zero(a) ? nothing : _inv_modular(a)
  if b === nothing
    # Not covered (or if a = 0), fall back to the generic algorithm
    return invoke(inv, Tuple{Generic.AbsSimpleFunctionFieldElem}, a)
  end
  return b
end

# Given a = g/c, the cofactor s of g and r = res_y(g, f), return
# a^-1 = c s / r in canonical form.
function _inv_from_cofactor(a::Generic.AbsSimpleFunctionFieldElem,
                            s::PolyRingElem, r::PolyRingElem)
  F = parent(a)
  c = denominator(a, false)
  num, den = Generic._rat_poly_canonicalise(s * c, r)
  return F(num, den)
end

# Number D of evaluation points: deg_x r, deg_x s_i <= m d_f + n d_g = D - 1.
function _inv_degree_bound(f::PolyRingElem, g::PolyRingElem)
  d_f = maximum(degree(coeff(f, i)) for i in 0:degree(f))
  d_g = maximum(degree(coeff(g, i)) for i in 0:degree(g))
  return degree(g) * d_f + degree(f) * d_g + 1
end

################################################################################
#
#  Over F_p: evaluation and interpolation
#
################################################################################

#=
Given the y-coefficients fy = [f_0, ..., f_n] and gy = [g_0, ..., g_m] of f
and g over F_p[x] and the number D of points, return
(r, [s_0, ..., s_(n-1)]) over F_p[x], where r = res_y(g, f) and
s = sum_i s_i y^i is the cofactor of g. Return `nothing` if
F_p has fewer than D good evaluation points, or if p is unsuitable (see
max_bad below).

This is evaluation and interpolation [GG13, Section 5.2] applied to the
resultant and the cofactor, as in Collins' algorithm [Col71].
=#
function _inv_cofactor_eval(fy::Vector{fpPolyRingElem},
                            gy::Vector{fpPolyRingElem}, D::Int)
  Fpx = parent(fy[1])
  Fp = base_ring(Fpx)
  Fpy, _ = polynomial_ring(Fp, :y; cached = false)
  n = length(fy) - 1
  m = length(gy) - 1
  # A point u is bad if lc_y(f)(u) = 0, lc_y(g)(u) = 0 or r(u) = 0. If none
  # of lc_y(f), lc_y(g), r vanishes in F_p[x], there are at most
  # deg lc_y(f) + deg lc_y(g) + deg r bad points, and deg r <= D - 1. More
  # bad points mean that p is unsuitable (p divides one of these polynomials).
  max_bad = degree(fy[n + 1]) + degree(gy[m + 1]) + D - 1
  bad = 0
  us = elem_type(Fp)[]                     # the good points u
  rv = elem_type(Fp)[]                     # the values r(u)
  sv = [elem_type(Fp)[] for _ in 1:n]      # sv[i + 1] holds the values s_i(u)
  for i in 0:min(characteristic(Fp) - 1, ZZ(typemax(Int)))
    length(us) == D && break
    u = Fp(i)
    fu = Fpy([evaluate(h, u) for h in fy])
    gu = Fpy([evaluate(h, u) for h in gy])
    ru = zero(Fp)
    if degree(fu) == n && degree(gu) == m
      # Syl(g(u), f(u)) is the image of Syl(g, f), so r(u) = res(g(u), f(u))
      ru = resultant(gu, fu)
    end
    if is_zero(ru)
      bad += 1
      bad > max_bad && return nothing
      continue
    end
    # s(u) is the unique polynomial of degree < n with s(u) g(u) = r(u)
    # modulo f(u)
    su = ru * invmod(gu, fu)
    push!(us, u)
    push!(rv, ru)
    for j in 1:n
      push!(sv[j], coeff(su, j - 1))
    end
  end
  length(us) < D && return nothing
  return interpolate(Fpx, us, rv), [interpolate(Fpx, us, v) for v in sv]
end

# k = F_p, given as a prime field of word-size characteristic. For other
# finite fields, or if F_p has fewer than D elements, return `nothing`.
function _inv_modular(a::Generic.AbsSimpleFunctionFieldElem{T}) where {
    T <: Union{FqFieldElem, fpFieldElem}}
  F = parent(a)
  kx = parent(denominator(a, false))
  k = base_ring(kx)
  if k isa FqField
    # Only prime fields of word-size characteristic
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
  g = numerator(a, false)
  D = _inv_degree_bound(f, g)
  # Not enough evaluation points in F_p
  D <= characteristic(Fp) || return nothing
  fy = [map_coefficients(to_fp, coeff(f, i); parent = Fpx) for i in 0:degree(f)]
  gy = [map_coefficients(to_fp, coeff(g, i); parent = Fpx) for i in 0:degree(g)]
  res = _inv_cofactor_eval(fy, gy, D)
  res === nothing && return nothing
  r, s = res
  r = map_coefficients(from_fp, r; parent = kx)
  s = parent(f)([map_coefficients(from_fp, si; parent = kx) for si in s])
  return _inv_from_cofactor(a, s, r)
end

################################################################################
#
#  Over Q: multimodular
#
################################################################################

# Polynomials over Q scaled by the lcm d of their denominators to polynomials
# over Z. Returns the scaled polynomials and d.
function _integral_scaling(Zx::ZZPolyRing, qs::Vector{QQPolyRingElem})
  d = reduce(lcm, (denominator(q) for q in qs); init = ZZ(1))
  return [numerator(d * q, Zx) for q in qs], d
end

# Upper bound for |h|_1, the sum of the absolute values of the coefficients
# (cheaper than computing |h|_1 itself).
_norm_1(h::ZZPolyRingElem) = (degree(h) + 1) * height(h)

# Number of consecutive unsuitable primes after which we give up and use the
# generic algorithm. A prime is unsuitable only if it divides lc_y(f), lc_y(g)
# or r over Z, so this does not happen for the word-size primes used here
# unless the input is chosen against them.
const _INV_MAX_BAD_PRIMES = 20

function _inv_modular(a::Generic.AbsSimpleFunctionFieldElem{QQFieldElem})
  F = parent(a)
  # For extensions of small degree the generic algorithm is faster
  degree(F) <= 3 && return nothing
  Qx = parent(denominator(a, false))
  Zx = Globals.Zx
  f = numerator(F)
  g = numerator(a, false)
  D = _inv_degree_bound(f, g)
  # Integral multiples c_f f and c_g g. Their resultant and cofactor are
  # r' = c_g^n c_f^m r and s' with s' (c_g g) = r' modulo f, so
  # g^-1 = c_g s' / r' and a^-1 = c c_g s' / r'.
  fz, _ = _integral_scaling(Zx, [coeff(f, i) for i in 0:degree(f)])
  gz, c_g = _integral_scaling(Zx, [coeff(g, i) for i in 0:degree(g)])
  # B = |f|_1^m |g|_1^n bounds the coefficients of r' and s' (see header)
  B = sum(_norm_1, fz)^degree(g) * sum(_norm_1, gz)^degree(f)
  # r' and s' modulo primes p until their product M exceeds 2 B
  primes = ZZRingElem[]
  rs = fpPolyRingElem[]                    # r' mod p
  ss = Vector{fpPolyRingElem}[]            # coefficients of s' mod p
  M = ZZ(1)
  bad = 0
  for p in PrimesSet(p_start, -1)
    M > 2 * B && break
    Fp = Native.GF(p; cached = false)
    Fpx, _ = polynomial_ring(Fp, :x; cached = false)
    red = h -> change_base_ring(Fp, h; parent = Fpx)
    res = _inv_cofactor_eval(red.(fz), red.(gz), D)
    if res === nothing
      bad += 1
      bad > _INV_MAX_BAD_PRIMES && return nothing
      continue
    end
    bad = 0
    push!(primes, ZZ(p))
    push!(rs, res[1])
    push!(ss, res[2])
    M *= p
  end
  # Chinese remaindering [GG13, Section 5.4] with symmetric residues in
  # (-M/2, M/2], which recovers r' and s' since M > 2 B
  ce = crt_env(primes)
  lift_Q = L -> change_base_ring(QQ, mod_sym!(induce_crt(L, ce; parent = Zx),
                                              M); parent = Qx)
  r = lift_Q(rs)
  s = [lift_Q([si[i] for si in ss]) for i in 1:degree(f)]
  # a^-1 = c c_g s' / r'
  return _inv_from_cofactor(a, parent(f)([c_g * si for si in s]), r)
end

################################################################################
#
#  Over number fields: multimodular with totally split primes
#
################################################################################

# Coefficient bound over K = Q(theta) with monic integral defining polynomial
# h of degree d. For z in Z[theta]
# let |z| be the sum of the absolute values of its coordinates in the power
# basis 1, theta, ..., theta^(d - 1), and |P| the sum of the |coefficients|
# for P in Z[theta][x][y]. Since theta^l theta^k = theta^(l + k) with
# l + k <= 2d - 2,
#
#   |z w| <= mu |z| |w|,   mu = max_{0 <= e <= 2d - 2} |theta^e|,
#
# and a product of m + n entries of Syl(g, f) has norm at most
# mu^(m + n - 1) times the product of their norms. Hence the coordinates of r
# and s are bounded by
#
#   B = mu^(m + n - 1) |f|^m |g|^n.
# mu = max_{0 <= e <= 2d - 2} |theta^e| for K = Q(theta)
function _power_basis_mu(K::AbsSimpleNumField)
  th = gen(K)
  mu = ZZ(1)
  for e in 0:2 * degree(K) - 2
    z = th^e
    mu = max(mu, sum(abs(numerator(coeff(z, l))) for l in 0:degree(K) - 1))
  end
  return mu
end

# |z| for z in Z[theta].
function _norm_1(z::AbsSimpleNumFieldElem)
  return sum(abs(numerator(coeff(z, l))) for l in 0:degree(parent(z)) - 1)
end

_norm_1(P::Generic.Poly{AbsSimpleNumFieldElem}) =
  sum(_norm_1, coefficients(P); init = ZZ(0))

# Polynomials over K scaled by the lcm d of the denominators of all
# coordinates, so that their coefficients lie in Z[theta]. Returns the scaled
# polynomials and d.
function _integral_scaling(qs::Vector{Generic.Poly{AbsSimpleNumFieldElem}})
  d = ZZ(1)
  for q in qs, z in coefficients(q)
    d = lcm(d, denominator(z))
  end
  return [d * q for q in qs], d
end

# K = Q(theta) with monic integral defining polynomial h, so that Z[theta] is
# a ring. For a prime p that splits completely in Z[theta], with
# h = prod_j (x - rho_j) modulo p, the maps theta -> rho_j give
# Z[theta]/p = F_p^d. r and s are computed over
# each F_p with _inv_cofactor_eval, mapped back to (Z[theta]/p)[x] and
# combined over the primes as over Q. The maps are those of Hecke's
# modular_init, modular_proj and modular_lift.
function _inv_modular(
    a::Generic.AbsSimpleFunctionFieldElem{AbsSimpleNumFieldElem})
  F = parent(a)
  Kx = parent(denominator(a, false))
  K = base_ring(Kx)
  h = defining_polynomial(K)
  # Z[theta] must be a ring, so that r and s have integral coordinates
  (is_monic(h) && isone(denominator(h))) || return nothing
  d = degree(K)
  f = numerator(F)
  g = numerator(a, false)
  D = _inv_degree_bound(f, g)
  # Integral multiples c_f f, c_g g, as over Q
  fz, _ = _integral_scaling([coeff(f, i) for i in 0:degree(f)])
  gz, c_g = _integral_scaling([coeff(g, i) for i in 0:degree(g)])
  B = _power_basis_mu(K)^(degree(g) + degree(f) - 1) *
      sum(_norm_1, fz)^degree(g) * sum(_norm_1, gz)^degree(f)
  r = Kx()
  s = [Kx() for _ in 1:degree(f)]
  M = ZZ(1)
  bad = 0
  for p in PrimesSet(p_start, -1)
    M > 2 * B && break
    local me
    try
      me = modular_init(K, p; deg_limit = 1)
    catch e
      e isa BadPrime || rethrow()
      continue
    end
    # Only primes that split completely
    (isdefined(me, :fld) && length(me.fld) == d) || continue
    Fpx, _ = polynomial_ring(Native.GF(p; cached = false), :x; cached = false)
    # The images under theta -> rho_j, j = 1, ..., d, in F_p[x]
    Fp = base_ring(Fpx)
    to_fp = P -> map_coefficients(z -> Fp(coeff(z, 0)), P; parent = Fpx)
    fp = [to_fp.(modular_proj(P, me)) for P in fz]
    gp = [to_fp.(modular_proj(P, me)) for P in gz]
    res = [_inv_cofactor_eval([u[j] for u in fp], [u[j] for u in gp], D)
           for j in 1:d]
    if any(isnothing, res)
      bad += 1
      bad > _INV_MAX_BAD_PRIMES && return nothing
      continue
    end
    bad = 0
    # Back to (Z[theta]/p)[x]
    to_fq = (v, j) -> map_coefficients(z -> me.fld[j](lift(z)), v;
                                       parent = me.fldx[j])
    lift_K = v -> modular_lift([to_fq(v[j], j) for j in 1:d], me)
    rp = lift_K([t[1] for t in res])
    sp = [lift_K([t[2][i] for t in res]) for i in 1:degree(f)]
    # Chinese remaindering coordinatewise, with symmetric residues modulo M p
    q = ZZ(p)
    r, _ = induce_crt(r, M, rp, q, true)
    s = [induce_crt(s[i], M, sp[i], q, true)[1] for i in 1:length(s)]
    M *= q
  end
  # a^-1 = c c_g s' / r', as over Q
  return _inv_from_cofactor(a, parent(f)([K(c_g) * si for si in s]), r)
end
