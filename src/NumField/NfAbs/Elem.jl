export isintegral

################################################################################
#
#  Copy
#
################################################################################

Base.copy(d::nf_elem) = deepcopy(d)

################################################################################
#
#  Basis matrix
#
################################################################################

function basis_matrix(A::Array{nf_elem, 1}, ::Type{FakeFmpqMat})
  @assert length(A) > 0
  n = length(A)
  d = degree(parent(A[1]))

  M = zero_matrix(FlintZZ, n, d)

  deno = one(FlintZZ)
  dummy = one(FlintZZ)

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

function basis_matrix(A::Array{nf_elem, 1})
  @assert length(A) > 0
  n = length(A)
  d = degree(parent(A[1]))

  M = zero_matrix(FlintQQ, n, d)

  for i in 1:n
    for j in 1:d
      M[i, j] = coeff(A[i], j - 1)
    end
  end
  return M
end

################################################################################
#
#  Characteristic polynomial
#
################################################################################

function charpoly(Qx::FmpqPolyRing, a::nf_elem)
  f = charpoly(Qx, representation_matrix(a))
  return f
end

function charpoly(a::nf_elem)
  f = charpoly(parent(parent(a).pol), a)
  return f
end

function charpoly(a::nf_elem, ::FlintRationalField)
  return charpoly(a)
end

function charpoly(Zx::FmpzPolyRing, a::nf_elem)
  f = charpoly(a)
  if !isone(denominator(f))
    throw(error("Element is not integral"))
  end
  return Zx(f)
end

function charpoly(a::nf_elem, Z::FlintIntegerRing)
  return charpoly(PolynomialRing(Z, cached = false)[1], a)
end

################################################################################
#
#  Minimal polynomial
#
################################################################################

@doc Markdown.doc"""
    minpoly(a::nf_elem) -> fmpq_poly

The minimal polynomial of $a$.
"""
function minpoly(Qx::FmpqPolyRing, a::nf_elem)
  f = minpoly(Qx, representation_matrix(a))
  return f
end

function minpoly(a::nf_elem)
  f = minpoly(parent(parent(a).pol), a)
  return f
end

function minpoly(a::nf_elem, ::FlintRationalField)
  return minpoly(a)
end

function minpoly(a::nf_elem, ZZ::FlintIntegerRing)
  return minpoly(PolynomialRing(ZZ, cached = false)[1], a)
end

function minpoly(Zx::FmpzPolyRing, a::nf_elem)
  f = minpoly(a)
  if !isone(denominator(f))
    throw(error("Element is not integral"))
  end
  return Zx(f)
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function sub!(a::nf_elem, b::nf_elem, c::nf_elem)
   ccall((:nf_elem_sub, libantic), Nothing,
         (Ref{nf_elem}, Ref{nf_elem}, Ref{nf_elem}, Ref{AnticNumberField}),
         a, b, c, a.parent)
end

function set_den!(a::nf_elem, d::fmpz)
  ccall((:nf_elem_set_den, libflint), Nothing,
        (Ref{nf_elem}, Ref{fmpz}, Ref{AnticNumberField}),
        a, d, parent(a))
end

function divexact!(z::nf_elem, x::nf_elem, y::fmpz)
  ccall((:nf_elem_scalar_div_fmpz, libantic), Nothing,
        (Ref{nf_elem}, Ref{nf_elem}, Ref{fmpz}, Ref{AnticNumberField}),
        z, x, y, parent(x))
  return z
end

function gen!(r::nf_elem)
   a = parent(r)
   ccall((:nf_elem_gen, libantic), Nothing,
         (Ref{nf_elem}, Ref{AnticNumberField}), r, a)
   return r
end

function one!(r::nf_elem)
   a = parent(r)
   ccall((:nf_elem_one, libantic), Nothing,
         (Ref{nf_elem}, Ref{AnticNumberField}), r, a)
   return r
end

function one(r::nf_elem)
   a = parent(r)
   return one(a)
end

function zero(r::nf_elem)
   return zero(parent(r))
end

################################################################################
#
#  Norm div
#
################################################################################

@doc Markdown.doc"""
    norm_div(a::nf_elem, d::fmpz, nb::Int) -> fmpq

> Computes `divexact(norm(a), d)` provided the result has at most `nb` bits.
>
> Typically, `a` is an element of some ideal with norm `d`.
"""
function norm_div(a::nf_elem, d::fmpz, nb::Int)
   z = fmpq()
   # TODO:
   #CF the resultant code has trouble with denominators,
   #   this "solves" the problem, but it should probably be
   #   adressed in c
   @assert nb > 0
   n = degree(parent(a))
   if n > 20
     p = p_start
     pp = fmpz(1)
     no = 1
     while nbits(pp) < nb
       p = next_prime(p)
       R = GF(Int(p), cached = false)
       Rt, t = PolynomialRing(R, cached = false)
       np = R(divexact(resultant(Rt(parent(a).pol), Rt(a)), R(d)))
       if isone(pp)
         no = lift(np)
         pp = fmpz(p)
       else
         no = crt(no, pp, lift(np), fmpz(p))
         pp *= fmpz(p)
       end
     end
     no = mod_sym(no, pp)
     return no//1
   end
   de = denominator(a)
   ccall((:nf_elem_norm_div, libantic), Nothing,
         (Ref{fmpq}, Ref{nf_elem}, Ref{AnticNumberField}, Ref{fmpz}, UInt),
         z, (a*de), a.parent, (d*de^n), UInt(nb))
   return z
end

################################################################################
#
#  Is norm divisible by
#
################################################################################

# TODO: Use fits(Int, n) and then split into fmpz_mod/nmod case
@doc Markdown.doc"""
    isnorm_divisible(a::nf_elem, n::fmpz) -> Bool
Checks if the norm of $a$ is divisible by $n$, assuming that the norm of $a$ is
an integer.
"""
function isnorm_divisible(a::nf_elem, n::fmpz)
  K = parent(a)
  if !iscoprime(denominator(K.pol), n)
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
    R1 = ResidueRing(FlintZZ, Int(m), cached = false)
    R1x = PolynomialRing(R1, "x", cached = false)[1]
    el = resultant_ideal(R1x(numerator(a)), R1x(K.pol))
    return iszero(el)
  end
  R = ResidueRing(FlintZZ, m, cached = false)
  Rx = PolynomialRing(R, "x", cached = false)[1]
  el = resultant_ideal(Rx(numerator(a)), Rx(K.pol))
  return iszero(el)
end

#In this version, n is supposed to be a prime power
function isnorm_divisible_pp(a::nf_elem, n::fmpz)
  K = parent(a)
  if !iscoprime(denominator(K.pol), n)
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
    R1 = ResidueRing(FlintZZ, Int(m), cached = false)
    R1x = PolynomialRing(R1, "x", cached = false)[1]
    el = resultant_ideal_pp(R1x(numerator(a)), R1x(K.pol))
    return iszero(el)
  end
  R = ResidueRing(FlintZZ, m, cached = false)
  Rx = PolynomialRing(R, "x", cached = false)[1]
  el = resultant_ideal_pp(Rx(numerator(a)), Rx(K.pol))
  return iszero(el)
end

################################################################################
#
#  Numerator
#
################################################################################

@doc Markdown.doc"""
    numerator(a::nf_elem) -> nf_elem
For an element $a\in K = Q[t]/f$ write $a$ as $b/d$ with
$b\in Z[t]$, $\deg(a) = \deg(b)$ and $d>0$ minimal in $Z$.
This function returns $b$.
"""
function numerator(a::nf_elem)
   _one = one(FlintZZ)
   z = deepcopy(a)
   ccall((:nf_elem_set_den, libantic), Nothing,
         (Ref{nf_elem}, Ref{fmpz}, Ref{AnticNumberField}),
         z, _one, a.parent)
   return z
end

################################################################################
#
#  Chinese remaindering
#
################################################################################

function induce_crt(a::nf_elem, p::fmpz, b::nf_elem, q::fmpz, signed::Bool = false)
  c = parent(a)()
  pi = invmod(p, q)
  mul!(pi, pi, p)
  pq = p*q
  if signed
    pq2 = div(pq, 2)
  else
    pq2 = fmpz(0)
  end
  return induce_inner_crt(a, b, pi, pq, pq2), pq
end

function inner_crt(a::fmpz, b::fmpz, up::fmpz, pq::fmpz, pq2::fmpz = fmpz(0))
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

function induce_inner_crt(a::nf_elem, b::nf_elem, pi::fmpz, pq::fmpz, pq2::fmpz = fmpz(0))
  c = parent(a)()
  ca = fmpz()
  cb = fmpz()
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

@doc Markdown.doc"""
    norm(f::PolyElem{nf_elem}) -> fmpq_poly

>The norm of $f$, that is, the product of all conjugates of $f$ taken
>coefficientwise.
"""
function norm(f::PolyElem{nf_elem})
  Kx = parent(f)
  K = base_ring(f)
  f, i = deflate(f)
  if degree(f) == 1 && ismonic(f)
    N = charpoly(-constant_coefficient(f))
  elseif degree(f) > 10 # TODO: find a good cross-over,
                         # do this using CRT modular?
    P = polynomial_to_power_sums(f, degree(f)*degree(K))
    PQ = fmpq[tr(x) for x in P]
    N = power_sums_to_polynomial(PQ)
  else
    Qx = PolynomialRing(FlintQQ, "x", cached = false)[1]
    Qxy = PolynomialRing(Qx, "y", cached = false)[1]

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

@doc Markdown.doc"""
    factor(f::fmpz_poly, K::NumberField) -> Fac{Generic.Poly{nf_elem}}
    factor(f::fmpq_poly, K::NumberField) -> Fac{Generic.Poly{nf_elem}}

The factorisation of $f$ over $K$.
"""
function factor(f::fmpq_poly, K::AnticNumberField)
  f1 = change_base_ring(K, f)
  return factor(f1)
end

function factor(f::fmpz_poly, K::AnticNumberField)
  f1 = change_base_ring(K, f)
  return factor(f1)
end

function nice(f::PolyElem{nf_elem})
  if degree(f) < 10
    return "$f"
  end
  if ismonic(f)
    return "$(gen(parent(f))^degree(f)) + ... "
  else
    return "$(lead(f))$(gen(parent(f))^degree(f)) + ... "
  end
end

@doc Markdown.doc"""
    factor(f::PolyElem{nf_elem}) -> Fac{Generic.Poly{nf_elem}}

The factorisation of $f$.
"""
function factor(f::PolyElem{nf_elem})
  Kx = parent(f)
  K = base_ring(f)

  iszero(f) && error("poly is zero")

  if degree(f) == 0
    r = Fac{typeof(f)}()
    r.fac = Dict{typeof(f), Int}()
    r.unit = Kx(lead(f))
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
    @vprint :PolyFactor 1 "Factoring $(nice(el))\n"
    lf = _factor(el)
    for g in lf
      fac[g] = v
    end
  end
  r = Fac{typeof(f)}()
  r.fac = fac
  #The unit is just the leading coefficient of f
  r.unit = Kx(lead(f))
  return r
end

  #assumes that f is a squarefree polynomial
function _factor(f::PolyElem{nf_elem})

  K = base_ring(f)
  f = f*(1//lead(f))

  if degree(f) < degree(K)
    lf = factor_trager(f)::Vector{typeof(f)}
  else
    lf = factor_new(f)::Vector{typeof(f)}
  end
return lf
end

function factor_trager(f::PolyElem{nf_elem})
  k = 0
  g = f
  @vprint :PolyFactor 1 "Using Trager's method\n"
  p = p_start
  F = GF(p)

  Kx = parent(f)
  K = base_ring(Kx)

  Zx = Hecke.Globals.Zx
  @vtime :PolyFactor Np = norm_mod(g, p, Zx)
  while isconstant(Np) || !issquarefree(map_coeffs(F, Np))
    k = k + 1
    g = compose(f, gen(Kx) - k*gen(K))
    @vtime :PolyFactor 2 Np = norm_mod(g, p, Zx)
  end

  @vprint :PolyFactor 2 "need to shift by $k, now the norm"
  if any(x -> denominator(x) > 1, coefficients(g))
    @vtime :PolyFactor 2 N = Hecke.Globals.Qx(norm(g))
  else
    @vtime :PolyFactor 2 N = norm_mod(g, Zx)
    @hassert :PolyFactor 1 N == Zx(norm(g))
  end
  
  while isconstant(N) || !issquarefree(N)
    error("should not happen")
    k = k + 1
    g = compose(f, gen(Kx) - k*gen(K))
    @vtime :PolyFactor 2 N = norm_mod(g)
  end
  @vtime :PolyFactor 2 fac = factor(N)

  res = typeof(f)[]

  for i in keys(fac.fac)
    t = change_base_ring(K, i, parent = Kx)
    t = compose(t, gen(Kx) + k*gen(K))
    @vtime :PolyFactor 2 t = gcd(f, t)
    push!(res, t)
  end

  return res
end

function isirreducible(f::PolyElem{nf_elem})
  if degree(f) == 1
    return true
  end
  if !issquarefree(f)
    return false
  end
  if iszero(coeff(f, 0))
    return false
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
        return true
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
  fac = _factor(f)
  return length(fac) == 1
end

function _ds(fa)
  @assert all(x->x == 1, values(fa.fac))
  T = Int[degree(x) for x = keys(fa.fac)]
  M = MSet(T)
  return Set(sum(s) for s = subsets(M) if length(s) > 0)
end

function _degset(f::fmpz_poly, p::Int)
  F = GF(p, cached = false)
  Ft, t = PolynomialRing(F, cached = false)
  @assert issquarefree(Ft(f))
  g = Ft(f)
  if !issquarefree(g)
    throw(BadPrime(p))
  end
  fa = factor(g)
  return _ds(fa)
end

function (R::GFPPolyRing)(f::fq_nmod_poly)
  g = R()
  for i=0:degree(f)
    setcoeff!(g, i, coeff(coeff(f, i), 0))
  end
  return g
end

function _degset(f::PolyElem{nf_elem}, p::Int, normal::Bool = false)
  K = base_ring(f)

  me = modular_init(K, p, deg_limit = 1)
  #to be competitive, we need to have Fp, not Fq of degree 1
  if isempty(me)
    return Set(1:degree(f))
  end
  fp = modular_proj(f, me)
  R = GF(p, cached = false)
  Rt = PolynomialRing(R, cached = false)[1]
  if !issquarefree(fp[1])
    throw(BadPrime(p))
  end

  s = _ds(factor(Rt(fp[1])))
  if normal
    return s
  end
  for i=2:length(fp)
    if !issquarefree(fp[i])
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

@doc Markdown.doc"""
    roots(f::fmpz_poly, K::AnticNumberField) -> Array{nf_elem, 1}

Computes all roots in $K$ of a polynomial $f$. It is assumed that $f$ is non-zero,
squarefree and monic.
"""
function roots(f::fmpz_poly, K::AnticNumberField; kw...)
  f1 = change_base_ring(K, f)
  return roots(f1; kw...)
end

@doc Markdown.doc"""
    roots(f::fmpq_poly, K::AnticNumberField) -> Array{nf_elem, 1}

Computes all roots in $K$ of a polynomial $f$. It is assumed that $f$ is non-zero,
squarefree and monic.
"""
function roots(f::fmpq_poly, K::AnticNumberField; kw...)
  f1 = change_base_ring(K, f)
  return roots(f1; kw...)
end

function elem_in_nf(a::nf_elem)
  return a
end

@doc Markdown.doc"""
    roots(f::Generic.Poly{nf_elem}; max_roots = degree(f),
                                    ispure = false,
                                    isnormal = false)       -> Array{nf_elem, 1}

Computes the roots of a polynomial $f$. It is assumed that $f$ is non-zero,
squarefree and monic.

- `max_roots` controls the maximal number of roots the function returns.
- `ispure` indicates whether $f$ is of the form $x^d + c$, where $d$ is the
  degree and $c$ the constant coefficient of $f$.
- `isnormal` indicates that the field contains no or all the roots of $f$.
"""
function roots(f::Generic.Poly{nf_elem}; max_roots::Int = degree(f),
                                         ispure::Bool = false,
                                         isnormal::Bool = false)

  iszero(f) && error("Polynomial must be non-zero")

  if max_roots == 0
    return nf_elem[]
  end

  if max_roots <= 1 && iszero(coeff(f, 0))
    return nf_elem[zero(base_ring(f))]
  end

  if degree(f) == 0
    return nf_elem[]
  end

  if degree(f) == 1
    return nf_elem[-coeff(f, 0)//coeff(f, 1)]
  end

  return _roots_hensel(f, max_roots = max_roots, ispure = ispure, isnormal = isnormal)
end

@doc Markdown.doc"""
    hasroot(f::PolyElem{nf_elem}) -> Bool, nf_elem
Tests if $f$ has a root and return it.
"""
function hasroot(f::PolyElem{nf_elem})
  rt = roots(f, max_roots = 1)
  if length(rt) == 0
    return false, zero(base_ring(f))
  else
    return true, rt[1]
  end
end

@doc Markdown.doc"""
    hasroot(f::fmpz_poly, K::AnticNumberField) -> Bool, nf_elem
    hasroot(f::fmpq_poly, K::AnticNumberField) -> Bool, nf_elem

Tests if $f$ has a root in $K$, and return it.
"""
function hasroot(f::fmpz_poly, K::AnticNumberField)
  f1 = change_base_ring(K, f)
  return hasroot(f1)
end

function hasroot(f::fmpq_poly, K::AnticNumberField)
  f1 = change_base_ring(K, f)
  return hasroot(f1)
end

################################################################################
#
#  Roots
#
################################################################################

@doc Markdown.doc"""
    ispower(a::nf_elem, n::Int; with_roots_unity::Bool = false) -> Bool, nf_elem

Determines whether $a$ has an $n$-th root. If this is the case,
the root is returned.
>
If the field $K$ is known to contain the $n$-th roots of unity,
one can set `with_roots_unity` to `true`.
"""
function ispower(a::nf_elem, n::Int; with_roots_unity::Bool = false, isintegral::Bool = false, trager = false)
  @assert n > 0
  if n == 1
    return true, a
  end
  if iszero(a)
    return true, a
  end

  if trager
    return ispower_trager(a, n)
  end

  K = parent(a)
  if isintegral
    d = fmpz(1)
  else
    if ismaximal_order_known(K)
      OK = maximal_order(K)
      d = denominator(a, OK)
    else
      d = denominator(a)
    end
  end
  Ky, y = PolynomialRing(K, "y", cached = false)

  if n == 2 || with_roots_unity
    rt = roots(y^n - a*d^n, max_roots = 1, ispure = true, isnormal = true)
  else
    rt = roots(y^n - a*d^n, max_roots = 1, ispure = true)
  end

  if length(rt) > 0
    return true, rt[1]//d
  else
    return false, zero(a)
  end
end

function ispower_trager(a::nf_elem, n::Int)
  # This is done using Trager factorization, but we can do some short cuts
  # The norm will be the minpoly_a(x^n), which will always be squarefree.
  K = parent(a)
  @vprint :PolyFactor 1 "Computing the minpoly\n"
  @vtime :PolyFactor 1 f = minpoly(a)
  b = K(1)
  c = a*b
  if degree(f) < degree(K)
    i = 0
    while true
      @vprint :PolyFactor 1 "Need to shift it\n"
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
  @vprint :PolyFactor 1 "Factoring the minpoly\n"
  @vtime :PolyFactor 1 fac = factor(N)
  Kt, t = PolynomialRing(K, "a", cached = false)
  for (p, _) in fac
    if degree(p) == degree(f)
      @vprint :PolyFactor 1 "Computing final gcd\n"
      t = gcd(change_base_ring(K, p, parent = Kt), t^n - c)
      @assert degree(t) == 1
      return true, -divexact(coeff(t, 0), coeff(t, 1))//b
    end
  end

  return false, a
end

function _height(a::nf_elem)
  h = fmpz(1)
  for i in 1:degree(parent(a))
    h = max(h, height(coeff(a, i - 1)))
  end
  return h
end

@doc Markdown.doc"""
    issquare(a::nf_elem) -> Bool, nf_elem
Tests if $a$ is a square and return the root if possible.
"""
issquare(a::nf_elem) = ispower(a, 2)

issquare_with_root(a::NumFieldElem) = issquare(a)

@doc Markdown.doc"""
    sqrt(a::nf_elem) -> nf_elem
The square-root of $a$ or an error if this is not possible.
 """
sqrt(a::nf_elem) = root(a, 2)

@doc Markdown.doc"""
    root(a::nf_elem, n::Int) -> nf_elem

Computes the $n$-th root of $a$. Throws an error if this is not possible.
"""
function root(a::nf_elem, n::Int)
  fl, rt = ispower(a, n)
  if fl
    return rt
  end

  error("$a has no $n-th root")
end

@doc Markdown.doc"""
    roots(a::nf_elem, n::Int) -> Array{nf_elem, 1}
Compute all $n$-th roots of $a$, possibly none.
"""
function roots(a::nf_elem, n::Int)
  @assert n > 0
  if n == 1 || iszero(a)
    return nf_elem[a]
  end

  d = denominator(a)
  Ky, y = PolynomialRing(parent(a), "y", cached = false)
  rt = roots(y^n - a*d^n, ispure = true)

  return nf_elem[x//d for x = rt]
end

function root(a::NfOrdElem, n::Int)
  fl, rt = ispower(a.elem_in_nf, n)
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

function inv_lift_recon(a::nf_elem)  # not competitive....reconstruction is too slow
  p = next_prime(2^60)
  K = parent(a)
  me = modular_init(K, p)
  ap = Hecke.modular_proj(a, me)
  bp = Hecke.modular_lift([inv(x) for x = ap], me)
  pp = fmpz(p)

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

function inv_lift(a::nf_elem)  # better, but not enough
  p = next_prime(2^60)
  K = parent(a)
  me = modular_init(K, p)
  ap = modular_proj(a, me)
  bp = modular_lift([inv(x) for x = ap], me)
  pp = fmpz(p)
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

function __mod(a::nf_elem, b::fmpz, fl::Bool = true)#, sym::Bool = false) # Not yet
  z = parent(a)()
  ccall((:nf_elem_mod_fmpz_den, libantic), Nothing, (Ref{nf_elem}, Ref{nf_elem}, Ref{fmpz}, Ref{AnticNumberField}, Cint), z, a, b, parent(a), Cint(fl))
  return z
end

function coprime_denominator(a::nf_elem, b::fmpz)
  z = parent(a)()
  ccall((:nf_elem_coprime_den, libantic), Nothing, (Ref{nf_elem}, Ref{nf_elem}, Ref{fmpz}, Ref{AnticNumberField}), z, a, b, parent(a))
  return z
end

function mod_sym!(a::nf_elem, b::fmpz)
  ccall((:nf_elem_smod_fmpz, libantic), Nothing,
        (Ref{nf_elem}, Ref{nf_elem}, Ref{fmpz}, Ref{AnticNumberField}),
        a, a, b, parent(a))
  return a
end

function mod(b::nf_elem, p::fmpz)
  K = parent(b)
  if isdefining_polynomial_nice(parent(b))
    return coprime_denominator(b, p)
  else
    m = lcm([p, denominator(K.pol), numerator(coeff(K.pol, degree(K.pol)))])
    return coprime_denominator(b, m)
  end
end

mod(x::nf_elem, y::Integer) = mod(x, fmpz(y))

#Assuming that the denominator of a is one, reduces all the coefficients modulo p
# non-symmetric (positive) residue system
function mod!(a::nf_elem, b::fmpz)
  ccall((:nf_elem_mod_fmpz, libantic), Nothing,
        (Ref{nf_elem}, Ref{nf_elem}, Ref{fmpz}, Ref{AnticNumberField}),
        a, a, b, parent(a))
  return a
end

function rem(a::nf_elem, b::fmpz)
  c = deepcopy(a)
  rem!(c, b)
  return c
end

function mod_sym(a::nf_elem, b::fmpz, b2::fmpz)
  return mod_sym(a, b)
  return z
end

function mod_sym(a::nf_elem, b::fmpz)
  c = deepcopy(a)
  mod_sym!(c, b)
  return c
end

################################################################################
#
#  Conversion to nmod_poly and fmpz_mod_poly
#
################################################################################

function nf_elem_to_nmod_poly!(r::nmod_poly, a::nf_elem, useden::Bool = true)
  ccall((:nf_elem_get_nmod_poly_den, libantic), Nothing,
        (Ref{nmod_poly}, Ref{nf_elem}, Ref{AnticNumberField}, Cint),
        r, a, a.parent, Cint(useden))
  return nothing
end

function nf_elem_to_gfp_poly!(r::gfp_poly, a::nf_elem, useden::Bool = true)
  ccall((:nf_elem_get_nmod_poly_den, libantic), Nothing,
        (Ref{gfp_poly}, Ref{nf_elem}, Ref{AnticNumberField}, Cint),
        r, a, a.parent, Cint(useden))
  return nothing
end

function (R::Nemo.NmodPolyRing)(a::nf_elem)
  r = R()
  nf_elem_to_nmod_poly!(r, a)
  return r
end

function (R::Nemo.GFPPolyRing)(a::nf_elem)
  r = R()
  nf_elem_to_gfp_poly!(r, a)
  return r
end

function nf_elem_to_fmpz_mod_poly!(r::fmpz_mod_poly, a::nf_elem, useden::Bool = true)
  ccall((:nf_elem_get_fmpz_mod_poly_den, libantic), Nothing,
        (Ref{fmpz_mod_poly}, Ref{nf_elem}, Ref{AnticNumberField}, Cint),
        r, a, a.parent, Cint(useden))
  return nothing
end

function nf_elem_to_gfp_fmpz_poly!(r::gfp_fmpz_poly, a::nf_elem, useden::Bool = true)
  ccall((:nf_elem_get_fmpz_mod_poly_den, libantic), Nothing,
        (Ref{gfp_fmpz_poly}, Ref{nf_elem}, Ref{AnticNumberField}, Cint),
        r, a, a.parent, Cint(useden))
  return nothing
end

function (R::Nemo.FmpzModPolyRing)(a::nf_elem)
  r = R()
  nf_elem_to_fmpz_mod_poly!(r, a)
  return r
end

################################################################################
#
#  Complex conjugate
#
################################################################################

function conjugate_quad(a::nf_elem)
  k = parent(a)
  @assert degree(k) == 2
  # we have
  # a = x + y gen(k), so bar(a) = x + y bar(k)
  # assume pol(k) is monic: x^2 + rx + t, then
  # bar(gen(k)) = -gen(k) - r
  # since (pq-formula) gen(k) = - r/2 \pm 1/2(sqrt(r^2-4t)
  # so bar(a) = x + y (-bar(k) - r) = (x-ry) - y gen(k)
  b = k()
  q = fmpz()
  @assert isone(k.pol_den)
  GC.@preserve b begin
    a_ptr = reinterpret(Ptr{Int}, pointer_from_objref(a))
    p_ptr = reinterpret(Ptr{Int}, k.pol_coeffs)
    s = sizeof(Ptr{fmpz})

    ccall((:fmpz_mul, libflint), Cvoid, (Ref{fmpz}, Ptr{Int}, Ptr{Int}), q, p_ptr+s, a_ptr +s)
    ccall((:fmpz_sub, libflint), Cvoid, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), reinterpret(Ptr{Int}, pointer_from_objref(b)), a_ptr, q)
    ccall((:fmpz_neg, libflint), Cvoid, (Ptr{fmpz}, Ptr{fmpz}), reinterpret(Ptr{Int}, pointer_from_objref(b))+1*s, a_ptr + s)
    ccall((:fmpz_set, libflint), Cvoid, (Ptr{fmpz}, Ptr{fmpz}), reinterpret(Ptr{Int}, pointer_from_objref(b))+3*s, a_ptr+3*s)
  end
  #TODO:
  # - write in c?
  # - use Ref and Ref(, i) instead of pointers
  # - deal with non-monic fields
  return b
end

function complex_conjugate(a::nf_elem)
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
