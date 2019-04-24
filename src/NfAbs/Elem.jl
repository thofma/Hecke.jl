################################################################################
#
#  Base case for dot products
#
################################################################################

dot(x::fmpz, y::nf_elem) = x*y

dot(x::nf_elem, y::fmpz) = x*y

function dot(a::Array{nf_elem, 1}, b::Array{fmpz, 1})
  d = zero(parent(a[1]))
  t = zero(d)
  for i=1:length(a)
    mul!(t, a[i], b[i])
    add!(d, d, t)
  end
  return d
end

################################################################################
#
#  Copy
#
################################################################################

Base.copy(d::nf_elem) = deepcopy(d)

################################################################################
#
#  Is rational?
#
################################################################################

function israt(a::nf_elem)
  if degree(parent(a))==1
    return true
  end
  @assert degree(parent(a))>2 ## fails for 2 due to efficiency
  return a.elem_length<2
end

################################################################################
#
#  Is integral
#
################################################################################

isintegral(a::fmpq) = isone(denominator(a))

function isintegral(a::Union{ nf_elem, NfAbsNSElem, NfRelElem, NfRel_nsElem })
  f = minpoly(a)
  for i = 0:(degree(f) - 1)
    if !isintegral(coeff(f, i))
      return false
    end
  end
  return true
end

################################################################################
#
#  Random elements from arrays of nf_elem
#
################################################################################

@doc Markdown.doc"""
    rand(b::Array{nf_elem,1}, r::UnitRange)

A random linear combination of elements in `b` with coefficients in `r`.
"""
function rand(b::Array{nf_elem,1}, r::UnitRange)
  length(b) == 0 && error("Array must not be empty")
  s = zero(parent(b[1]))
  rand!(s, b, r)
  return s
end

@doc Markdown.doc"""
    rand(b::Array{nf_elem,1}, r::UnitRange, terms::Int) -> nf_elem

A random linear combination (with repetitions) of \code{terms} elements of `b`
with coefficients in `r`.
"""
function rand(b::Array{nf_elem,1}, r::UnitRange, terms::Int)
  length(b) == 0 && error("Array must not be empty")
  s = zero(parent(b[1]))
  rand!(s, b, r, terms)
  return s
end

function rand!(c::nf_elem, b::Array{nf_elem,1}, r::UnitRange, terms::Int)
  length(b) == 0 && error("Array must not be empty")
  (terms<=0 || terms > length(b)) && error("Number of terms should be at least 1 and cannot exceed the length of the array")

  t = zero(parent(b[1]))

  terms = min(terms, length(b))
  mul!(c, rand(b), rand(r))
  for i = 2:terms
    mul!(t, rand(b), rand(r))
    add!(c, t, c)
  end

  return c
end

function rand!(c::nf_elem, b::Array{nf_elem,1}, r::UnitRange)
  length(b) == 0 && error("Array must not be empty")

  mul!(c, b[1], rand(r))
  t = zero(b[1].parent)

  for i = 2:length(b)
    mul!(t, b[i], rand(r))
    add!(c, t, c)
  end

  return c
end

################################################################################
#
#  Basis matrix
#
################################################################################

function basis_mat(A::Array{T, 1}) where {T <: Union{nf_elem, NfAbsNSElem}}
  @assert length(A) > 0
  n = length(A)
  d = degree(parent(A[1]))

  if T === NfAbsNSElem
    MM = zero_matrix(FlintQQ, n, d)
    for i in 1:n
      elem_to_mat_row!(MM, i, A[i])
    end
    return FakeFmpqMat(MM)
  end

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

################################################################################
#
#  Characteristic polynomial
#
################################################################################

@doc Markdown.doc"""
    charpoly(a::nf_elem) -> fmpq_poly

The characteristic polynomial of a.
"""
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
    error("element is not integral")
  end
  return Zx(denocharator(f)*f)
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

The minimal polynomial of a.
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
    error("element is not integral")
  end
  return Zx(denominator(f)*f)
end

################################################################################
#
#  Powering with fmpz
#
################################################################################

function ^(x::nf_elem, y::fmpz)
  # TODO: try to coerce y to UInt
  res = parent(x)()
  if y < 0
    res = inv(x)^(-y)
  elseif y == 0
    res = parent(x)(1)
  elseif y == 1
    res = deepcopy(x)
  elseif mod(y, 2) == 0
    z = x^(div(y, 2))
    res = z*z
  else
    res = x^(y-1) * x
  end
  return res
end



################################################################################
#
#  Unsafe operations
#
################################################################################

function sub!(a::nf_elem, b::nf_elem, c::nf_elem)
   ccall((:nf_elem_sub, :libantic), Nothing,
         (Ref{nf_elem}, Ref{nf_elem}, Ref{nf_elem}, Ref{AnticNumberField}),
         a, b, c, a.parent)
end

function set_den!(a::nf_elem, d::fmpz)
  ccall((:nf_elem_set_den, :libflint), Nothing,
        (Ref{nf_elem}, Ref{fmpz}, Ref{AnticNumberField}),
        a, d, parent(a))
end

function divexact!(z::nf_elem, x::nf_elem, y::fmpz)
  ccall((:nf_elem_scalar_div_fmpz, :libantic), Nothing,
        (Ref{nf_elem}, Ref{nf_elem}, Ref{fmpz}, Ref{AnticNumberField}),
        z, x, y, parent(x))
  return z
end

function gen!(r::nf_elem)
   a = parent(r)
   ccall((:nf_elem_gen, :libantic), Nothing,
         (Ref{nf_elem}, Ref{AnticNumberField}), r, a)
   return r
end

function one!(r::nf_elem)
   a = parent(r)
   ccall((:nf_elem_one, :libantic), Nothing,
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
#  Ad hoc operations
#
################################################################################

################################################################################
#
#  Norm div
#
################################################################################

@doc Markdown.doc"""
    norm_div(a::nf_elem, d::fmpz, nb::Int) -> fmpq

Computes divexact(norm(a), d) provided the result has at most `nb` bits.
Typically, $a$ is in some ideal and $d$ is the norm of the ideal.
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
   ccall((:nf_elem_norm_div, :libantic), Nothing,
         (Ref{fmpq}, Ref{nf_elem}, Ref{AnticNumberField}, Ref{fmpz}, UInt),
         z, (a*de), a.parent, (d*de^n), UInt(nb))
   return z
end

################################################################################
#
#  Is norm divisible by
#
################################################################################


@doc Markdown.doc"""
    isnorm_divisible(a::nf_elem, n::fmpz) -> Bool
Checks if the norm of $a$ is divisible by $n$, assuming that the norm of $a$ is
an integer.
"""
function isnorm_divisible(a::nf_elem, n::fmpz)
  
  K = parent(a)
  s, t = ppio(denominator(a), n)
  if s == 1
    R = ResidueRing(FlintZZ, n, cached = false)
    Rx, x = PolynomialRing(R, "x", cached = false)
    el = resultant_ideal(Rx(numerator(a)), Rx(K.pol))
  else
    m = n*s^degree(K)
    R = ResidueRing(FlintZZ, m, cached = false)
    Rx, x = PolynomialRing(R, "x", cached = false)
    el = resultant_ideal(Rx(numerator(a)), Rx(K.pol))
  end 
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
   ccall((:nf_elem_set_den, :libantic), Nothing,
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
  if degree(f) > 10 # TODO: find a good cross-over
    P = polynomial_to_power_sums(f, degree(f)*degree(K))
    PQ = fmpq[tr(x) for x in P]
    return power_sums_to_polynomial(PQ)
  end

  Qx = PolynomialRing(FlintQQ, "x", cached = false)[1]
  Qxy = PolynomialRing(Qx, "y", cached = false)[1]

  T = change_ring(K.pol, Qxy)
  h = nf_poly_to_xy(f, Qxy, Qx)
  return resultant(T, h)
end

function norm(f::PolyElem{T}) where T <: NfRelElem
  Kx = parent(f)
  K = base_ring(f)

  P = polynomial_to_power_sums(f, degree(f)*degree(K))
  PQ = [tr(x) for x = P]
  return power_sums_to_polynomial(PQ)
end

################################################################################
#
#  Factorization
#
################################################################################

@doc Markdown.doc"""
  factor(f::fmpz_poly, K::NumberField) -> Fac{Generic.Poly{nf_elem}}
  factor(f::fmpq_poly, K::NumberField) -> Fac{Generic.Poly{nf_elem}}

The factorisation of f over K (using Trager's method).
"""
function factor(f::fmpq_poly, K::AnticNumberField)
  f1 = change_base_ring(f, K)
  return factor(f1)
end

function factor(f::fmpz_poly, K::AnticNumberField)
  f1 = change_base_ring(f, K)
  return factor(f1)
end

@doc Markdown.doc"""
  factor(f::PolyElem{nf_elem}) -> Fac{Generic.Poly{nf_elem}}

The factorisation of f (using Trager's method).
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

  f_orig = deepcopy(f)
  @vprint :PolyFactor 1 "Factoring $f\n"
  @vtime :PolyFactor 2 g = gcd(f, derivative(f))  
  if degree(g) > 0
    f = div(f, g)
  end

  
  if degree(f) == 1
    multip = div(degree(f_orig), degree(f))
    r = Fac{typeof(f)}()
    r.fac = Dict{typeof(f), Int}(f*(1//lead(f)) => multip)
    r.unit = one(Kx) * lead(f_orig)
    return r
  end

  f = f*(1//lead(f))

  k = 0
  g = f
  @vtime :PolyFactor 2 N = norm(g)

  while isconstant(N) || !issquarefree(N)
    k = k + 1
    g = compose(f, gen(Kx) - k*gen(K))
    @vtime :PolyFactor 2 N = norm(g)
  end
  @vtime :PolyFactor 2 fac = factor(N)
  
  res = Dict{PolyElem{nf_elem}, Int64}()

  for i in keys(fac.fac)
    t = change_ring(i, Kx)
    t = compose(t, gen(Kx) + k*gen(K))
    @vtime :PolyFactor 2 t = gcd(f, t)
    res[t] = 1
  end

  r = Fac{typeof(f)}()
  r.fac = res
  r.unit = Kx(1)

  if f != f_orig
    global p_start
    p = p_start
    @vtime :PolyFactor 2 while true
      p = next_prime(p)
      me = modular_init(K, p, max_split=1)
      fp = modular_proj(f, me)[1]
      if issquarefree(fp)
        fp = deepcopy(modular_proj(f_orig, me)[1])
        for k in keys(res)
          gp = modular_proj(k, me)[1]
          res[k] = valuation(fp, gp)
        end
        r.fac = res
        # adjust the unit of the factorization
        r.unit = one(Kx) * lead(f_orig)//prod((lead(p) for (p, e) in r))
        return r
      end
    end
  end
  r.unit = one(Kx)* lead(f_orig)//prod((lead(p) for (p, e) in r))
  return r
end

function isirreducible(f::PolyElem{nf_elem})
  if !issquarefree(f)
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
  fac = factor(f)
  return length(fac.fac) == 1 && first(values(fac.fac)) == 1
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

Computes all roots in $K$ of a polynomial $f$. It is assumed that $f$ is is non-zero,
squarefree and monic.
"""
function roots(f::fmpz_poly, K::AnticNumberField; kw...)
  f1 = change_base_ring(f, K)
  return roots(f1; kw...)
end

@doc Markdown.doc"""
    roots(f::fmpq_poly, K::AnticNumberField) -> Array{nf_elem, 1}

Computes all roots in $K$ of a polynomial $f$. It is assumed that $f$ is is non-zero,
squarefree and monic.
"""
function roots(f::fmpq_poly, K::AnticNumberField; kw...)
  f1 = change_base_ring(f, K)
  return roots(f1; kw...)
end

function elem_in_nf(a::nf_elem)
  return a
end

@doc Markdown.doc"""
    roots(f::Generic.Poly{nf_elem}; max_roots = degree(f),
                                    ispure = false,
                                    isnormal = false)       -> Array{nf_elem, 1}

Computes the roots of a polynomial $f$. It is assumed that $f$ is is non-zero,
squarefree and monic.

- `max_roots` controls the maximal number of roots the functions returns.
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
  f1 = change_base_ring(f, K)
  return hasroot(f1)
end

function hasroot(f::fmpq_poly, K::AnticNumberField)
  f1 = change_base_ring(f, K)
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
function ispower(a::nf_elem, n::Int; with_roots_unity::Bool = false)
  @assert n > 0
  if n == 1
    return true, a
  end
  if iszero(a)
    return true, a
  end

  d = denominator(a)

  Ky, y = PolynomialRing(parent(a), "y", cached = false)

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

@doc Markdown.doc"""
    issquare(a::nf_elem) -> Bool, nf_elem
Tests if $a$ is a square and return the root if possible.
"""
Nemo.issquare(a::nf_elem) = ispower(a, 2)

@doc Markdown.doc"""
    sqrt(a::nf_elem) -> nf_elem
The square-root of $a$ or an error if this is not possible.
 """
Nemo.sqrt(a::nf_elem) = root(a, 2)

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
#  Modular reduction
#
################################################################################

import Hecke.mod_sym!, Hecke.rem!, Hecke.mod!, Hecke.mod, Hecke.rem

function mod_sym!(a::nf_elem, b::fmpz)
  mod_sym!(a, b, div(b, 2))
end

function mod_sym!(a::nf_elem, b::fmpz, b2::fmpz)
  z = fmpz()
  for i=0:a.elem_length-1
    Nemo.num_coeff!(z, a, i)
    rem!(z, z, b)
    if z >= b2
      sub!(z, z, b)
    end
    _num_setcoeff!(a, i, z)
  end
end

function mod!(z::fmpz, x::fmpz, y::fmpz)
  ccall((:fmpz_mod, :libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), z, x, y)
  return z
end

function mod!(a::nf_elem, b::fmpz)
  z = fmpz()
  d = degree(parent(a))
  if d == 1
    Nemo.num_coeff!(z, a, 0)
    mod!(z, z, b)
    _num_setcoeff!(a, 0, z)
  elseif d == 2
    Nemo.num_coeff!(z, a, 0)
    mod!(z, z, b)
    _num_setcoeff!(a, 0, z)
    Nemo.num_coeff!(z, a, 1)
    mod!(z, z, b)
    _num_setcoeff!(a, 1, z)
  else
    for i=0:a.elem_length-1
      Nemo.num_coeff!(z, a, i)
      mod!(z, z, b)
      _num_setcoeff!(a, i, z)
    end
  end
end

function mod(a::nf_elem, b::fmpz)
  c = deepcopy(a)
  mod!(c, b)
  return c
end

function rem!(a::nf_elem, b::fmpz)
  z = fmpz()
  for i=0:a.elem_length-1
    Nemo.num_coeff!(z, a, i)
    rem!(z, z, b)
    _num_setcoeff!(a, i, z)
  end
end

function rem(a::nf_elem, b::fmpz)
  c = deepcopy(a)
  rem!(c, b)
  return c
end

function mod_sym(a::nf_elem, b::fmpz)
  return mod_sym(a, b, div(b, 2))
end

function mod_sym(a::nf_elem, b::fmpz, b2::fmpz)
  c = deepcopy(a)
  mod_sym!(c, b, b2)
  return c
end

################################################################################
#
#  Conversion to nmod_poly and fmpz_mod_poly
#
################################################################################

function nf_elem_to_nmod_poly!(r::nmod_poly, a::nf_elem, useden::Bool = true)
  ccall((:nf_elem_get_nmod_poly_den, :libantic), Nothing,
        (Ref{nmod_poly}, Ref{nf_elem}, Ref{AnticNumberField}, Cint),
        r, a, a.parent, Cint(useden))
  return nothing
end

function nf_elem_to_gfp_poly!(r::gfp_poly, a::nf_elem, useden::Bool = true)
  ccall((:nf_elem_get_nmod_poly_den, :libantic), Nothing,
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
  ccall((:nf_elem_get_fmpz_mod_poly_den, :libantic), Nothing,
        (Ref{fmpz_mod_poly}, Ref{nf_elem}, Ref{AnticNumberField}, Cint),
        r, a, a.parent, Cint(useden))
  return nothing
end

function (R::Nemo.FmpzModPolyRing)(a::nf_elem)
  r = R()
  nf_elem_to_fmpz_mod_poly!(r, a)
  return r
end

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

    ccall((:fmpz_mul, :libflint), Cvoid, (Ref{fmpz}, Ptr{Int}, Ptr{Int}), q, p_ptr+s, a_ptr +s)
    ccall((:fmpz_sub, :libflint), Cvoid, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), reinterpret(Ptr{Int}, pointer_from_objref(b)), a_ptr, q)
    ccall((:fmpz_neg, :libflint), Cvoid, (Ptr{fmpz}, Ptr{fmpz}), reinterpret(Ptr{Int}, pointer_from_objref(b))+1*s, a_ptr + s)
    ccall((:fmpz_set, :libflint), Cvoid, (Ptr{fmpz}, Ptr{fmpz}), reinterpret(Ptr{Int}, pointer_from_objref(b))+3*s, a_ptr+3*s)
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
