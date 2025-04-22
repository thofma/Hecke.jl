################################################################################
#
#  Basis matrix
#
################################################################################

function basis_matrix(A::Vector{AbsSimpleNumFieldElem}, ::Type{FakeFmpqMat})
  @assert length(A) > 0
  n = length(A)
  d = degree(parent(A[1]))

  M = zero_matrix(ZZ, n, d)

  deno = one(ZZ)
  dummy = one(ZZ)

  for i in 1:n
    deno = lcm(deno, denominator(A[i]))
  end

  for i in 1:n
    elem_to_mat_row!(M, i, dummy, A[i])
    temp_den = divexact(deno, dummy)
    for j in 1:d
      M[i, j] = mul!(M[i, j], M[i, j], temp_den)
    end
  end
  return FakeFmpqMat(M, deno)
end

function basis_matrix(A::Vector{AbsSimpleNumFieldElem})
  @assert length(A) > 0
  n = length(A)
  d = degree(parent(A[1]))

  M = zero_matrix(QQ, n, d)

  for i in 1:n
    for j in 1:d
      M[i, j] = coeff(A[i], j - 1)
    end
  end
  return M
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function set_den!(a::AbsSimpleNumFieldElem, d::ZZRingElem)
  ccall((:nf_elem_set_den, libantic), Nothing,
        (Ref{AbsSimpleNumFieldElem}, Ref{ZZRingElem}, Ref{AbsSimpleNumField}),
        a, d, parent(a))
end

function set_num_coeff!(a::AbsSimpleNumFieldElem, i::Int, b::ZZRingElem)
  ccall((:_nf_elem_set_coeff_num_fmpz, libantic), Nothing,
        (Ref{AbsSimpleNumFieldElem}, Int, Ref{ZZRingElem}, Ref{AbsSimpleNumField}),
        a, i, b, parent(a))
end

function gen!(r::AbsSimpleNumFieldElem)
   a = parent(r)
   ccall((:nf_elem_gen, libantic), Nothing,
         (Ref{AbsSimpleNumFieldElem}, Ref{AbsSimpleNumField}), r, a)
   return r
end


################################################################################
#
#  Norm div
#
################################################################################

@doc raw"""
    norm_div(a::AbsSimpleNumFieldElem, d::ZZRingElem, nb::Int) -> QQFieldElem

Computes `divexact(norm(a), d)` provided the result has at most `nb` bits.

Typically, `a` is an element of some ideal with norm `d`.
"""
function norm_div(a::AbsSimpleNumFieldElem, d::ZZRingElem, nb::Int)
   z = QQFieldElem()
   # TODO:
   #CF the resultant code has trouble with denominators,
   #   this "solves" the problem, but it should probably be
   #   addressed in c
   @assert nb > 0
   n = degree(parent(a))
   if n > 20
     p = p_start
     pp = ZZRingElem(1)
     no = 1
     while nbits(pp) < nb
       p = next_prime(p)
       R = Native.GF(Int(p), cached = false)
       Rt, t = polynomial_ring(R, cached = false)
       np = R(divexact(resultant(Rt(parent(a).pol), Rt(a), false), R(d)))
       if isone(pp)
         no = lift(np)
         pp = ZZRingElem(p)
       else
         no = crt(no, pp, lift(np), ZZRingElem(p))
         pp *= ZZRingElem(p)
       end
     end
     no = mod_sym(no, pp)
     return no//1
   end
   de = denominator(a)
   ccall((:nf_elem_norm_div, libantic), Nothing,
         (Ref{QQFieldElem}, Ref{AbsSimpleNumFieldElem}, Ref{AbsSimpleNumField}, Ref{ZZRingElem}, UInt),
         z, (a*de), a.parent, (d*de^n), UInt(nb))
   return z
end

################################################################################
#
#  Is norm divisible by
#
################################################################################

# TODO: Use fits(Int, n) and then split into ZZModRingElem/zzModRingElem case
@doc raw"""
    is_norm_divisible(a::AbsSimpleNumFieldElem, n::ZZRingElem) -> Bool

Checks if the norm of $a$ is divisible by $n$, assuming that the norm of $a$ is
an integer.
"""
function is_norm_divisible(a::AbsSimpleNumFieldElem, n::ZZRingElem)
  K = parent(a)
  if !is_coprime(denominator(K.pol), n)
    na = norm(a)
    @assert isone(denominator(na))
    return divides(numerator(na), n)[1]
  end
  s, t = ppio(denominator(a), n)
  if !isone(s)
    m = n*s^degree(K)
  else
    m = n
  end
  if fits(Int, m)
    R1 = residue_ring(ZZ, Int(m), cached = false)[1]
    R1x = polynomial_ring(R1, "x", cached = false)[1]
    el = resultant_ideal(R1x(numerator(a)), R1x(K.pol))
    return iszero(el)
  end
  R = residue_ring(ZZ, m, cached = false)[1]
  Rx = polynomial_ring(R, "x", cached = false)[1]
  el = resultant_ideal(Rx(numerator(a)), Rx(K.pol))
  return iszero(el)
end

#In this version, n is supposed to be a prime power
function is_norm_divisible_pp(a::AbsSimpleNumFieldElem, n::ZZRingElem)
  K = parent(a)
  if !is_coprime(denominator(K.pol), n)
    na = norm(a)
    @assert isone(denominator(na))
    return divides(numerator(na), n)[1]
  end
  s, t = ppio(denominator(a), n)
  if !isone(s)
    m = n*s^degree(K)
  else
    m = n
  end
  if fits(Int, m)
    R1 = residue_ring(ZZ, Int(m), cached = false)[1]
    R1x = polynomial_ring(R1, "x", cached = false)[1]
    el = resultant_ideal_pp(R1x(numerator(a)), R1x(K.pol))
    return iszero(el)
  end
  R = residue_ring(ZZ, m, cached = false)[1]
  Rx = polynomial_ring(R, "x", cached = false)[1]
  el = resultant_ideal_pp(Rx(numerator(a)), Rx(K.pol))
  return iszero(el)
end


################################################################################
#
#  Chinese remaindering
#
################################################################################

function induce_crt(a::AbsSimpleNumFieldElem, p::ZZRingElem, b::AbsSimpleNumFieldElem, q::ZZRingElem, signed::Bool = false)
  c = parent(a)()
  pi = invmod(p, q)
  mul!(pi, pi, p)
  pq = p*q
  if signed
    pq2 = div(pq, 2)
  else
    pq2 = ZZRingElem(0)
  end
  return induce_inner_crt(a, b, pi, pq, pq2), pq
end

function inner_crt(a::ZZRingElem, b::ZZRingElem, up::ZZRingElem, pq::ZZRingElem, pq2::ZZRingElem = ZZRingElem(0))
  #1 = gcd(p, q) = up + vq
  # then u = modinv(p, q)
  # vq = 1-up. i is up here
  #crt: x = a (p), x = b(q) => x = avq + bup = a(1-up) + bup
  #                              = (b-a)up + a
  if !iszero(pq2)
    r = mod(((b-a)*up + a), pq)
    if r > pq2
      return r-pq
    else
      return r
    end
  else
    return mod(((b-a)*up + a), pq)
  end
end

function induce_inner_crt(a::AbsSimpleNumFieldElem, b::AbsSimpleNumFieldElem, pi::ZZRingElem, pq::ZZRingElem, pq2::ZZRingElem = ZZRingElem(0))
  c = parent(a)()
  ca = ZZRingElem()
  cb = ZZRingElem()
  for i=0:degree(parent(a))-1
    Nemo.num_coeff!(ca, a, i)
    Nemo.num_coeff!(cb, b, i)
    Hecke._num_setcoeff!(c, i, inner_crt(ca, cb, pi, pq, pq2))
  end
  return c
end

################################################################################
#
#  Norm
#
################################################################################

@doc raw"""
    norm(f::PolyRingElem{AbsSimpleNumFieldElem}) -> QQPolyRingElem

>The norm of $f$, that is, the product of all conjugates of $f$ taken
>coefficientwise.
"""
function norm(f::PolyRingElem{AbsSimpleNumFieldElem})
  Kx = parent(f)
  K = base_ring(f)
  f, i = deflate(f)
  if degree(f) == 1 && is_monic(f)
    N = charpoly(-constant_coefficient(f))
  elseif degree(f) > 10 || degree(K) > 10 # TODO: find a good cross-over,
                         # do this using CRT modular?
    ff = f * inv(leading_coefficient(f)) #make monic
    P = polynomial_to_power_sums(ff, degree(ff)*degree(K))
    PQ = QQFieldElem[tr(x) for x in P]
    N = power_sums_to_polynomial(PQ)*norm(leading_coefficient(f))
  else
    Qx = polynomial_ring(QQ, "x", cached = false)[1]
    Qxy = polynomial_ring(Qx, "y", cached = false)[1]

    T = change_base_ring(Qx, K.pol, parent = Qxy)
    h = nf_poly_to_xy(f, Qxy, Qx)
    N = resultant(T, h)
  end
  return inflate(N, i)
end

################################################################################
#
#  Factorization
#
################################################################################

@doc raw"""
    factor(K::number_field, f::ZZPolyRingElem) -> Fac{Generic.Poly{AbsSimpleNumFieldElem}}
    factor(K::number_field, f::QQPolyRingElem) -> Fac{Generic.Poly{AbsSimpleNumFieldElem}}

The factorisation of $f$ over $K$.
"""
function factor(K::AbsSimpleNumField, f::QQPolyRingElem)
  f1 = change_base_ring(K, f)
  return factor(f1)
end

function factor(K::AbsSimpleNumField, f::ZZPolyRingElem)
  f1 = change_base_ring(K, f)
  return factor(f1)
end

function nice(f::PolyRingElem{AbsSimpleNumFieldElem})
  if degree(f) < 10
    return "$f"
  end
  if is_monic(f)
    return "$(gen(parent(f))^degree(f)) + ... "
  else
    return "$(leading_coefficient(f))$(gen(parent(f))^degree(f)) + ... "
  end
end

@doc raw"""
    factor(f::PolyRingElem{AbsSimpleNumFieldElem}) -> Fac{Generic.Poly{AbsSimpleNumFieldElem}}

The factorisation of $f$.
"""
function factor(f::PolyRingElem{AbsSimpleNumFieldElem}; algo::Symbol=:default)
  @assert algo in [:default, :trager, :van_hoeij]
  Kx = parent(f)
  K = base_ring(f)

  iszero(f) && error("poly is zero")

  if degree(f) == 0
    r = Fac{typeof(f)}()
    r.fac = Dict{typeof(f), Int}()
    r.unit = Kx(leading_coefficient(f))
    return r
  end
  sqf = factor_squarefree(f)
  fac = Dict{typeof(f), Int}()
  for (k, v) in sqf
    if degree(k) == 1
      fac[k] = v
      continue
    end
    el = k
    if iszero(coeff(k, 0))
      el = shift_right(el, 1)
      fac[gen(Kx)] = v
    end
    @vprintln :PolyFactor 1 "Factoring $(nice(el))"
    lf = _factor(el, algo = algo)
    for g in lf
      fac[g] = v
    end
  end
  r = Fac{typeof(f)}()
  r.fac = fac
  #The unit is just the leading coefficient of f
  r.unit = Kx(leading_coefficient(f))
  return r
end

  #assumes that f is a squarefree polynomial
function _factor(f::PolyRingElem{AbsSimpleNumFieldElem}; algo::Symbol = :default)

  K = base_ring(f)
  f = f*(1//leading_coefficient(f))

  if degree(f) < degree(K) || algo == :trager
    lf = factor_trager(f)::Vector{typeof(f)}
  else
    lf = factor_new(f)::Vector{typeof(f)}
  end
return lf
end

function factor_trager(f::PolyRingElem{AbsSimpleNumFieldElem})
  k = 0
  g = f
  @vprintln :PolyFactor 1 "Using Trager's method"
  p = p_start
  F = GF(p)

  Kx = parent(f)
  K = base_ring(Kx)

  Zx = Hecke.Globals.Zx
  @vtime :PolyFactor Np = norm_mod(g, p, Zx)
  while is_constant(Np) || !is_squarefree(map_coefficients(F, Np, cached = false))
    k = k + 1
    g = compose(f, gen(Kx) - k*gen(K), inner = :second)
    @vtime :PolyFactor 2 Np = norm_mod(g, p, Zx)
  end

  @vprintln :PolyFactor 2 "need to shift by $k, now the norm"
  if any(x -> denominator(x) > 1, coefficients(g)) ||
     !is_defining_polynomial_nice(K)
     #in all(?) tested examples, the non-modular one
     #is faster (its no longer using resulant directly)
     #maybe we should also do a modula resultant / Q?
#    A = any_order(K)
#    d = mapreduce(x->denominator(x, A), lcm, coefficients(g), init = ZZRingElem(1))
#    @vtime :PolyFactor 2 N = norm_mod(g*d, Zx)
#    N = Hecke.Globals.Qx(N) * QQFieldElem(1, d)^degree(K)
    @vtime :PolyFactor 2 N = Hecke.Globals.Qx(norm(g))
  else
    @vtime :PolyFactor 2 N = norm_mod(g, Zx)
    @hassert :PolyFactor 1 N == Zx(norm(g))
  end

  while is_constant(N) || !is_squarefree(N)
    error("should not happen")
    k = k + 1
    g = compose(f, gen(Kx) - k*gen(K), inner = :second)
    @vtime :PolyFactor 2 N = norm_mod(g)
  end
  @vtime :PolyFactor 2 fac = factor(N)

  res = typeof(f)[]

  for i in keys(fac.fac)
    t = change_base_ring(K, i, parent = Kx)
    t = compose(t, gen(Kx) + k*gen(K), inner = :second)
    @vtime :PolyFactor 2 t = gcd(f, t)
    push!(res, t)
  end

  return res
end

function is_irreducible(f::PolyRingElem{AbsSimpleNumFieldElem})
  isresult_right, result = is_irreducible_easy(f)
  if isresult_right
    return result
  end
  fac = _factor(f)
  return length(fac) == 1
end

function is_irreducible_easy(f::PolyRingElem{AbsSimpleNumFieldElem})
  if degree(f) == 1
    return true, true
  end
  if iszero(coeff(f, 0))
    return true, false
  end
  if !is_squarefree(f)
    return true, false
  end

  s = Set{Int}()
  i = 1
  for p = PrimesSet(degree(f)+1, -1)
    try
      d = _degset(f, p)
      if length(s) == 0
        s = d
      else
        s = Base.intersect(s, d)
      end
      if length(s) == 1
        return true, true
      end
      i += 1
      if i > 2*degree(f)
        break
      end
    catch e
      if !isa(e, BadPrime)
        rethrow(e)
      end
    end
  end
  return false, false
end

function _ds(fa)
  @assert all(x->x == 1, values(fa.fac))
  T = Int[degree(x) for x = keys(fa.fac)]
  M = MSet(T)
  return Set(sum(s) for s = subsets(M) if length(s) > 0)
end

function _degset(f::ZZPolyRingElem, p::Int)
  F = GF(p, cached = false)
  Ft, t = polynomial_ring(F, cached = false)
  @assert is_squarefree(Ft(f))
  g = Ft(f)
  if !is_squarefree(g)
    throw(BadPrime(p))
  end
  fa = factor(g)
  return _ds(fa)
end

function (R::fpPolyRing)(f::fqPolyRepPolyRingElem)
  g = R()
  for i=0:degree(f)
    setcoeff!(g, i, coeff(coeff(f, i), 0))
  end
  return g
end

function _degset(f::PolyRingElem{AbsSimpleNumFieldElem}, p::Int, normal::Bool = false)
  K = base_ring(f)

  me = modular_init(K, p, deg_limit = 1)
  #to be competitive, we need to have Fp, not Fq of degree 1
  if isempty(me)
    return Set(1:degree(f))
  end
  fp = modular_proj(f, me)
  R = Native.GF(p, cached = false)
  Rt = polynomial_ring(R, cached = false)[1]
  if !is_squarefree(fp[1])
    throw(BadPrime(p))
  end

  s = _ds(factor(Rt(fp[1])))
  if normal
    return s
  end
  for i=2:length(fp)
    if !is_squarefree(fp[i])
      throw(BadPrime(p))
    end
    s = Base.intersect(s, _ds(factor(Rt(fp[i]))))
    if length(s) == 1
      return s
    end
  end
  return s
end

################################################################################
#
#  Roots
#
################################################################################

@doc raw"""
    roots(K::AbsSimpleNumField, f::ZZPolyRingElem) -> Vector{AbsSimpleNumFieldElem}

Computes all roots in $K$ of a polynomial $f$. It is assumed that $f$ is non-zero,
squarefree and monic.
"""
function roots(K::AbsSimpleNumField, f::ZZPolyRingElem; kw...)
  f1 = change_base_ring(K, f)
  return roots(f1; kw...)
end

@doc raw"""
    roots(K::AbsSimpleNumField, f::QQPolyRingElem) -> Vector{AbsSimpleNumFieldElem}

Computes all roots in $K$ of a polynomial $f$. It is assumed that $f$ is non-zero,
squarefree and monic.
"""
function roots(K::AbsSimpleNumField, f::QQPolyRingElem; kw...)
  f1 = change_base_ring(K, f)
  return roots(f1; kw...)
end

function elem_in_nf(a::AbsSimpleNumFieldElem)
  return a
end

@doc raw"""
    roots(f::Generic.Poly{AbsSimpleNumFieldElem}; max_roots = degree(f),
                                    ispure = false,
                                    is_squarefree = false,
                                    is_normal = false)       -> Vector{AbsSimpleNumFieldElem}

Computes the roots of a polynomial $f$.

- `max_roots` controls the maximal number of roots the function returns.
- `ispure` indicates whether $f$ is of the form $x^d + c$, where $d$ is the
  degree and $c$ the constant coefficient of $f$.
- `is_normal` indicates that the field contains no or all the roots of $f$.
- `is_squarefree` indicated if the polynomial is known to be square free already.
"""
function roots(f::Generic.Poly{AbsSimpleNumFieldElem}; max_roots::Int = degree(f),
                                         ispure::Bool = false,
                                         is_squarefree::Bool = false,
                                         is_normal::Bool = false)

  iszero(f) && error("Polynomial must be non-zero")

  if max_roots == 0
    return AbsSimpleNumFieldElem[]
  end

  k = base_ring(f)

  if max_roots <= 1 && iszero(coeff(f, 0))
    return AbsSimpleNumFieldElem[zero(k)]
  end

  if degree(f) == 0
    return AbsSimpleNumFieldElem[]
  end

  if degree(f) == 1
    return AbsSimpleNumFieldElem[-coeff(f, 0)//coeff(f, 1)]
  end

  f = divexact(f, leading_coefficient(f))
  rts = AbsSimpleNumFieldElem[]

  if iszero(constant_coefficient(f))
    push!(rts, zero(k))
    if length(rts) >= max_roots
      return rts
    end
    _, f = remove(f, gen(parent(f)))
  end

  if !is_squarefree && !Hecke.is_squarefree(f)
    g = gcd(f, derivative(f))
    r = roots(divexact(f, g))
    for x = r
      push!(rts, x)
      if length(rts) >= max_roots
        return rts
      end
    end
    return rts
  end

  d = lcm(map(denominator, coefficients(f)))
  if !isone(d)
    ff = evaluate(f, gen(parent(f))*QQFieldElem(1, d))*d^degree(f)
    @assert is_monic(ff)
    @assert all(x->isone(denominator(x)), coefficients(ff))
    rt = _roots_hensel(ff, max_roots = max_roots, ispure = ispure, is_normal = is_normal)
    return vcat(rts, AbsSimpleNumFieldElem[x//d for x = rt])
  end

  return vcat(rts, _roots_hensel(f, max_roots = max_roots, ispure = ispure, is_normal = is_normal))
end

@doc raw"""
    has_root(f::PolyRingElem{AbsSimpleNumFieldElem}) -> Bool, AbsSimpleNumFieldElem

Tests if $f$ has a root and return it.
"""
function has_root(f::PolyRingElem{AbsSimpleNumFieldElem})
  rt = roots(f, max_roots = 1)
  if length(rt) == 0
    return false, zero(base_ring(f))
  else
    return true, rt[1]
  end
end

@doc raw"""
    has_root(f::ZZPolyRingElem, K::AbsSimpleNumField) -> Bool, AbsSimpleNumFieldElem
    has_root(f::QQPolyRingElem, K::AbsSimpleNumField) -> Bool, AbsSimpleNumFieldElem

Tests if $f$ has a root in $K$, and return it.
"""
function has_root(f::ZZPolyRingElem, K::AbsSimpleNumField)
  f1 = change_base_ring(K, f)
  return has_root(f1)
end

function has_root(f::QQPolyRingElem, K::AbsSimpleNumField)
  f1 = change_base_ring(K, f)
  return has_root(f1)
end

################################################################################
#
#  Roots
#
################################################################################

@doc raw"""
    is_power(a::AbsSimpleNumFieldElem, n::Int; with_roots_unity::Bool = false) -> Bool, AbsSimpleNumFieldElem

Determines whether $a$ has an $n$-th root. If this is the case,
the root is returned.

If the field $K$ is known to contain the $n$-th roots of unity,
one can set `with_roots_unity` to `true`.
"""
function is_power(a::AbsSimpleNumFieldElem, n::Int; with_roots_unity::Bool = false, is_integral::Bool = false, trager = false)
#  @req is_defining_polynomial_nice(parent(a)) "Defining polynomial must be integral and monic"
  @assert n > 0
  if n == 1
    return true, a
  end
  if iszero(a)
    return true, a
  end

  if trager
    return is_power_trager(a, n)
  end

  K = parent(a)
  if is_integral
    d = ZZRingElem(1)
  else
    if is_maximal_order_known(K)
      OK = maximal_order(K)
      d = denominator(a, OK)
    else
      d = denominator(a)
    end
  end
  Ky, y = polynomial_ring(K, "y", cached = false)

  if n == 2 || with_roots_unity
    rt = roots(y^n - a*d^n, max_roots = 1, ispure = true, is_normal = true)
  else
    rt = roots(y^n - a*d^n, max_roots = 1, ispure = true)
  end

  if length(rt) > 0
    return true, rt[1]//d
  else
    return false, zero(a)
  end
end

function is_power_trager(a::AbsSimpleNumFieldElem, n::Int)
  # This is done using Trager factorization, but we can do some short cuts
  # The norm will be the minpoly_a(x^n), which will always be squarefree.
  K = parent(a)
  @vprintln :PolyFactor 1 "Computing the minpoly"
  @vtime :PolyFactor 1 f = minpoly(a)
  b = K(1)
  c = a*b
  if degree(f) < degree(K)
    i = 0
    while true
      @vprintln :PolyFactor 1 "Need to shift it"
      b = (gen(K)+i)
      c = a*b^n
      f = minpoly(c)
      if degree(f) == degree(K)
        break
      end
      i += 1
    end
  end
  Qx = parent(f)
  x = gen(Qx)
  N = inflate(f, n)
  @vprintln :PolyFactor 1 "Factoring the minpoly"
  @vtime :PolyFactor 1 fac = factor(N)
  Kt, t = polynomial_ring(K, "a", cached = false)
  for (p, _) in fac
    if degree(p) == degree(f)
      @vprintln :PolyFactor 1 "Computing final gcd"
      t = gcd(change_base_ring(K, p, parent = Kt), t^n - c)
      @assert degree(t) == 1
      return true, -divexact(coeff(t, 0), coeff(t, 1))//b
    end
  end

  return false, a
end

function _height(a::AbsSimpleNumFieldElem)
  h = ZZRingElem(1)
  for i in 1:degree(parent(a))
    h = max(h, height(coeff(a, i - 1)))
  end
  return h
end

is_square(a::AbsSimpleNumFieldElem) = is_power(a, 2)[1]

is_square_with_sqrt(a::NumFieldElem) = is_power(a, 2)

sqrt(a::AbsSimpleNumFieldElem) = root(a, 2)

function root(a::AbsSimpleNumFieldElem, n::Int)
  fl, rt = is_power(a, n)
  if fl
    return rt
  end

  error("$a has no $n-th root")
end

function roots(a::AbsSimpleNumFieldElem, n::Int)
  @assert n > 0
  if n == 1 || iszero(a)
    return AbsSimpleNumFieldElem[a]
  end

  d = denominator(a)
  Ky, y = polynomial_ring(parent(a), "y", cached = false)
  rt = roots(y^n - a*d^n, ispure = true)

  return AbsSimpleNumFieldElem[x//d for x = rt]
end

function root(a::AbsSimpleNumFieldOrderElem, n::Int)
  fl, rt = is_power(a.elem_in_nf, n)
  if fl
    O = parent(a)
    if denominator(rt, O) == 1
      return O(rt)
    end
  end

  error("$a has no $n-th root")
end

################################################################################
#
#  Inversion via lifting
#
################################################################################

function inv_lift_recon(a::AbsSimpleNumFieldElem)  # not competitive....reconstruction is too slow
  p = next_prime(2^60)
  K = parent(a)
  me = modular_init(K, p)
  ap = Hecke.modular_proj(a, me)
  bp = Hecke.modular_lift([inv(x) for x = ap], me)
  pp = ZZRingElem(p)

  fl, b = Hecke.rational_reconstruction(bp, pp)
  t = K()
  while !fl
#    @assert mod_sym(a*bp - 1, pp) == 0
    mul!(pp, pp, pp)
    mul!(t, a, bp)
    rem!(bp, pp)
    sub!(t, 2, t)
    mul!(bp, bp, t)
    rem!(bp, pp)
#    @assert mod_sym(a*bp - 1, pp) == 0
    fl, b = rational_reconstruction(bp, pp)
    if fl
      if b*a == 1
        return b
      end
      fl = false
    end
  end
  return b
end

function inv_lift(a::AbsSimpleNumFieldElem)  # better, but not enough
  p = next_prime(2^60)
  K = parent(a)
  me = modular_init(K, p)
  ap = modular_proj(a, me)
  bp = modular_lift([inv(x) for x = ap], me)
  pp = ZZRingElem(p)
  fl, b = Hecke.rational_reconstruction(bp, pp)
  t = K()
  n = norm(a)
  while !fl
    Hecke.mul!(t, a, bp)
    Hecke.mul!(pp, pp, pp)
    rem!(t, pp)
    Hecke.sub!(t, 2, t)
    Hecke.mul!(bp, bp, t)
    rem!(t, pp)
    mul!(t, bp, n)
    mod_sym!(t, pp)
    if t*a == n
      return t//n
    end
  end
  return b
end

################################################################################
#
#  Mod function
#
################################################################################

function __mod(a::AbsSimpleNumFieldElem, b::ZZRingElem, fl::Bool = true)#, sym::Bool = false) # Not yet
  z = parent(a)()
  ccall((:nf_elem_mod_fmpz_den, libantic), Nothing, (Ref{AbsSimpleNumFieldElem}, Ref{AbsSimpleNumFieldElem}, Ref{ZZRingElem}, Ref{AbsSimpleNumField}, Cint), z, a, b, parent(a), Cint(fl))
  return z
end

function coprime_denominator(a::AbsSimpleNumFieldElem, b::ZZRingElem)
  z = parent(a)()
  ccall((:nf_elem_coprime_den, libantic), Nothing, (Ref{AbsSimpleNumFieldElem}, Ref{AbsSimpleNumFieldElem}, Ref{ZZRingElem}, Ref{AbsSimpleNumField}), z, a, b, parent(a))
  return z
end

function mod(b::AbsSimpleNumFieldElem, p::ZZRingElem)
  K = parent(b)
  if is_defining_polynomial_nice(parent(b))
    return coprime_denominator(b, p)
  else
    m = lcm([p, denominator(K.pol), numerator(coeff(K.pol, degree(K.pol)))])
    return coprime_denominator(b, m)
  end
end

mod(x::AbsSimpleNumFieldElem, y::Integer) = mod(x, ZZRingElem(y))


function rem(a::AbsSimpleNumFieldElem, b::ZZRingElem)
  c = deepcopy(a)
  rem!(c, b)
  return c
end


################################################################################
#
#  Complex conjugate
#
################################################################################

function conjugate_quad(a::AbsSimpleNumFieldElem)
  k = parent(a)
  @assert degree(k) == 2
  #fallback: tr(a) = a + bar(a), so tr(a) - a = bar(a)...
  #in the easy case: tr(gen(k)) = -r
  #if there are dens then it gets messy and I am not sure it is worth while:
  # x + y gen(k) -> x + y bar(k) and bar(k) = tr(k) - gen(k), but
  # tr(k) = -b/a (for the polyomial ax^2 + bx + c), hence:
  # (x+y gen(k)) / d -> (ax - by - ay gen(k))/(ad)
  # and there we might have to do simplification.
  #TODO: on 2nd thought: we might have to simplify in the easy case as well?
  (isone(k.pol_den) && is_monic(k.pol))|| return tr(a) - a
  # we have
  # a = x + y gen(k), so bar(a) = x + y bar(k)
  # assume pol(k) is monic: x^2 + rx + t, then
  # bar(gen(k)) = -gen(k) - r
  # since (pq-formula) gen(k) = - r/2 \pm 1/2(sqrt(r^2-4t)
  # so bar(a) = x + y (-bar(k) - r) = (x-ry) - y gen(k)
  b = k()
  q = ZZRingElem()
  GC.@preserve a b k begin
    a_ptr = reinterpret(Ptr{ZZRingElem}, pointer_from_objref(a))
    b_ptr = reinterpret(Ptr{ZZRingElem}, pointer_from_objref(b))
    p_ptr = reinterpret(Ptr{ZZRingElem}, k.pol_coeffs)
    s = sizeof(Ptr{ZZRingElem})

    # The C type `nf_elem_t` (corresponding to `AbsSimpleNumFieldElem`) is a C union;
    # in our case (= quadratic number field) it is a `qnf_elem_t`, defined like this:
    # typedef struct /* element of a quadratic number field */
    # {
    #    fmpz num[3]; /* extra coeff for delayed reduction */
    #    fmpz_t den;
    # } qnf_elem_struct;

    # compute r*y, where `r` is the second coefficient in k.pol_coeffs (hence `p_ptr+s`)
    # and `y` is the second coefficient in `a`
    mul!(q, p_ptr+s, a_ptr+s)
    # compute x - r*y, store it as first coefficient for `b`
    sub!(b_ptr, a_ptr, q)
    # compute -y, store it as second coefficient for `b`
    neg!(b_ptr+s, a_ptr+s)
    # copy the denominator from `a` to `b`
    set!(b_ptr+3*s, a_ptr+3*s)
  end
  #TODO:
  # - write in c?
  # - use Ref and Ref(, i) instead of pointers
  # - deal with non-monic fields
  return b
end

function complex_conjugate(a::AbsSimpleNumFieldElem)
  d = degree(parent(a))
  if d == 1
    return a
  end
  if d == 2
    if discriminant(parent(a)) < 0
      return a
    end
    return conjugate_quad(a)
  end
  error("Not implemented yet: element must be in an at most quadratic field")
end

################################################################################
#
#  Integral multiplicator
#
################################################################################

_integral_multiplicator(a::AbsSimpleNumFieldElem) = denominator(minpoly(a))

_integral_multiplicator(a::QQPolyRingElem) = denominator(a)
