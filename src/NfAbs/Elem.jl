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
#  Random elements from arrays of nf_elem
#
################################################################################

Markdown.doc"""
***
    rand(b::Array{nf_elem,1}, r::UnitRange)

A random linear combination of elements in `b` with coefficients in `r`.
"""
function rand(b::Array{nf_elem,1}, r::UnitRange)
  length(b) == 0 && error("Array must not be empty")
  s = zero(parent(b[1]))
  rand!(s, b, r)
  return s
end

Markdown.doc"""
***
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

Markdown.doc"""
***
    charpoly(a::nf_elem) -> fmpq_poly

The characteristic polynomial of a.
"""
function charpoly(a::nf_elem, Qx::FmpqPolyRing = parent(parent(a).pol))
  f = charpoly(Qx, representation_matrix(a))
  return f
end

################################################################################
#
#  Minimal polynomial
#
################################################################################

Markdown.doc"""
***
  minpoly(a::nf_elem) -> fmpq_poly

> The minimal polynomial of a.
"""
function minpoly(a::nf_elem, Qx::FmpqPolyRing = parent(parent(a).pol))
  f = minpoly(Qx, representation_matrix(a))
  return f
end

################################################################################
#
#  Powering with fmpz
#
################################################################################

function ^(x::nf_elem, y::fmpz)
  # TODO: try to coerce y to UInt
  if y < 0
    return inv(x)^(-y)
  elseif y == 0
    return parent(x)(1)
  elseif y == 1
    return deepcopy(x)
  elseif mod(y, 2) == 0
    z = x^(div(y, 2))
    return z*z
  elseif mod(y, 2) == 1
    return x^(y-1) * x
  end
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

Markdown.doc"""
***
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
       R = ResidueRing(FlintZZ, Int(p))
       Rt, t = PolynomialRing(R)
       np = divexact(resultant(Rt(parent(a).pol), Rt(a)), R(d))
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
#  Numerator
#
################################################################################

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

Markdown.doc"""
    norm(f::PolyElem{nf_elem}) -> fmpq_poly

The norm of $f$, that is, the product of all conjugates of $f$ taken
coefficientwise.
"""
function norm(f::PolyElem{nf_elem})
  Kx = parent(f)
  K = base_ring(f)
  if degree(f) > 10 # TODO: find a good cross-over
    P = polynomial_to_power_sums(f, degree(f)*degree(K))
    PQ = [tr(x) for x=P]
    return power_sums_to_polynomial(PQ)
  end

  Qy = parent(K.pol)
  y = gen(Qy)
  Qyx, x = PolynomialRing(Qy, "x", cached = false)

  Qx = PolynomialRing(FlintQQ, "x")[1]
  Qxy = PolynomialRing(Qx, "y", cached = false)[1]

  T = evaluate(K.pol, gen(Qxy))
  h = nf_poly_to_xy(f, gen(Qxy), gen(Qx))
  return resultant(T, h)
end

function norm(f::PolyElem{T}) where T <: NfRelElem
  Kx = parent(f)
  K = base_ring(f)

  P = polynomial_to_power_sums(f, degree(f)*degree(K))
  PQ = [tr(x) for x=P]
  return power_sums_to_polynomial(PQ)
end

################################################################################
#
#  Factorization
#
################################################################################

Markdown.doc"""
  factor(f::fmpz_poly, K::NumberField) -> Fac{Generic.Poly{nf_elem}}
  factor(f::fmpq_poly, K::NumberField) -> Fac{Generic.Poly{nf_elem}}

> The factorisation of f over K (using Trager's method).
"""
function factor(f::fmpq_poly, K::AnticNumberField)
  Ky, y = PolynomialRing(K, cached = false)
  return factor(evaluate(f, y))
end

function factor(f::fmpz_poly, K::AnticNumberField)
  Ky, y = PolynomialRing(K, cached = false)
  Qz, z = PolynomialRing(FlintQQ)
  return factor(evaluate(Qz(f), y))
end

Markdown.doc"""
  factor(f::PolyElem{nf_elem}) -> Fac{Generic.Poly{nf_elem}}

> The factorisation of f (using Trager's method).
"""
function factor(f::PolyElem{nf_elem})
  Kx = parent(f)
  K = base_ring(f)
  f == 0 && error("poly is zero")
  f_orig = deepcopy(f)
  @vprint :PolyFactor 1 "Factoring $f\n"
  @vtime :PolyFactor 2 g = gcd(f, derivative(f'))
  if degree(g) > 0
    f = div(f, g)
  end

  f = f*(1//lead(f))

  k = 0
  g = f
  N = 0

  while true
    @vtime :PolyFactor 2 N = norm(g)

    if !isconstant(N) && issquarefree(N)
      break
    end

    k = k + 1

    g = compose(f, gen(Kx) - k*gen(K))
  end

  @vtime :PolyFactor 2 fac = factor(N)

  res = Dict{PolyElem{nf_elem}, Int64}()

  for i in keys(fac.fac)
    t = zero(Kx)
    for j in 0:degree(i)
      t = t + K(coeff(i, j))*gen(Kx)^j
    end
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

  s = MSet(Int[])
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
  M = MSet(degree(x) for x = keys(fa.fac))
  return Set(sum(s) for s = subsets(M) if length(s) > 0)
end

function _degset(f::fmpz_poly, p::Int)
  F = ResidueRing(FlintZZ, p)
  Ft, t = PolynomialRing(F, cached = false)
  @assert issquarefree(Ft(f))
  g = Ft(f)
  if !issquarefree(g)
    throw(BadPrime(p))
  end
  fa = factor(g)
  return _ds(fa)
end

function (R::NmodPolyRing)(f::fq_nmod_poly)
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
  R = ResidueRing(FlintZZ, p, cached = false)
  Rt = PolynomialRing(R, cached = false)[1]
  if !issquarefree(fp[1])
    throw(BadPrime(p))
  end
  
  s = _ds(factor(Rt(fp[1])))
  if normal 
    return s
  end
  for i=2:length(fp)
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

Markdown.doc"""
***
    roots(f::fmpz_poly, K::AnticNumberField) -> Array{nf_elem, 1}
    roots(f::fmpq_poly, K::AnticNumberField) -> Array{nf_elem, 1}

> Computes all roots in $K$ of a polynomial $f$. It is assumed that $f$ is is non-zero,
> squarefree and monic.
"""
function roots(f::fmpz_poly, K::AnticNumberField, max_roots::Int = degree(f))
  Ky, y = PolynomialRing(K, cached = false)
  return roots(evaluate(f, y), max_roots)
end

function roots(f::fmpq_poly, K::AnticNumberField, max_roots::Int = degree(f))
  Ky, y = PolynomialRing(K, cached = false)
  return roots(evaluate(f, y), max_roots)
end

function elem_in_nf(a::nf_elem)
  return a
end

Markdown.doc"""
***
    roots(f::Generic.Poly{nf_elem}) -> Array{nf_elem, 1}

> Computes all roots of a polynomial $f$. It is assumed that $f$ is is non-zero,
> squarefree and monic.
"""
function roots(f::Generic.Poly{nf_elem}, max_roots::Int = degree(f); do_lll::Bool = false, do_max_ord::Bool = true)
  @assert issquarefree(f)

  #TODO: implement for equation order....
  #TODO: use max_roots

  if degree(f) == 1
    return [-trailing_coefficient(f)//lead(f)]
  end

  get_d = x -> denominator(x)
  if do_max_ord
    O = maximal_order(base_ring(f))
    if do_lll
      O = lll(O)
    end
    get_d = x-> denominator(x, O)
  end

  d = degree(f)

  deno = get_d(coeff(f, d))
  for i in (d-1):-1:0
    ai = coeff(f, i)
    if !iszero(ai)
      deno = lcm(deno, get_d(ai))
    end
  end

  g = deno*f

  if do_max_ord
    Ox, x = PolynomialRing(O, "x", cached = false)
    goverO = Ox([ O(coeff(g, i)) for i in 0:d])
  else
    goverO = g
  end  

  if !isone(lead(goverO))
    deg = degree(f)
    a = lead(goverO)
    b = one(O)
    for i in deg-1:-1:0
      setcoeff!(goverO, i, b*coeff(goverO, i))
      b = b*a
    end
    setcoeff!(goverO, deg, one(O))
    r = _roots_hensel(goverO, max_roots)
    return [ divexact(elem_in_nf(y), elem_in_nf(a)) for y in r ]
  end

  A = _roots_hensel(goverO, max_roots)

  return [ elem_in_nf(y) for y in A ]
end

Markdown.doc"""
    hasroot(f::PolyElem{nf_elem}) -> Bool, nf_elem
> Tests if $f$ has a root and return it.    
"""
function hasroot(f::PolyElem{nf_elem})
  rt = roots(f, 1)
  if length(rt) == 0
    return false, gen(base_ring(f))
  else
    return true, rt[1]
  end
end

Markdown.doc"""
    hasroot(f::fmpz_poly, K::AnticNumberField) -> Bool, nf_elem
    hasroot(f::fmpq_poly, K::AnticNumberField) -> Bool, nf_elem
> Tests if $f$ has a root in $K$, and return it.
"""
function hasroot(f::fmpz_poly, K::AnticNumberField)
  Ky, y = PolynomialRing(K, cached = false)
  return hasroot(evaluate(f, y))
end

function hasroot(f::fmpq_poly, K::AnticNumberField)
  Ky, y = PolynomialRing(K, cached = false)
  return hasroot(evaluate(f, y))
end

################################################################################
#
#  Roots
#
################################################################################

Markdown.doc"""
***
    ispower(a::nf_elem, n::Int) -> Bool, nf_elem

> Determines whether $a$ has an $n$-th root. If this is the case,
> the root is returned.
"""
function ispower(a::nf_elem, n::Int)
  #println("Compute $(n)th root of $a")

  @assert n>0
  if n==1
    return true, a
  end
  if iszero(a)
    return true, a
  end

  d = denominator(a)
  rt = _roots_hensel(a*d^n, n, 1)

  if length(rt)>0
    return true, rt[1]//d
  else
    return false, zero(a)
  end
end

Markdown.doc"""
    issquare(a::nf_elem) -> Bool, nf_elem
> Tests if $a$ is a square and return the root if possible.
"""
Nemo.issquare(a::nf_elem) = ispower(a, 2)

Markdown.doc"""
    sqrt(a::nf_elem) -> nf_elem
> The square-root of $a$ or an error if this is not possible.
 """
Nemo.sqrt(a::nf_elem) = root(a, 2)

Markdown.doc"""
***
    root(a::nf_elem, n::Int) -> nf_elem

> Computes the $n$-th root of $a$. Throws an error if this is not possible.
"""
function root(a::nf_elem, n::Int)
  fl, rt = ispower(a, n)
  if fl
    return rt
  end

  error("$a has no $n-th root")
end

Markdown.doc"""
    roots(a::nf_elem, n::Int) -> Array{nf_elem, 1}
> Compute all $n$-th roots of $a$, possibly none.
"""
function roots(a::nf_elem, n::Int)
  #println("Compute $(n)th root of $a")

  @assert n>0
  if n==1
    return [a]
  end
  if iszero(a)
    return [a]
  end

  d = denominator(a)
  rt = _roots_hensel(a*d^n, n)

  return [x//d for x = rt]
end

function root(a::NfOrdElem, n::Int)
  fl, rt = ispower(a.elem_in_nf, n)
  if fl
    O = parent(a)
    if denominator(a, O) == 1
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

function (R::Nemo.NmodPolyRing)(a::nf_elem)
  r = R()
  nf_elem_to_nmod_poly!(r, a)
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

################################################################################
#
#  Alternative norm computation
#
################################################################################

#TODO: This seems to be abandoned

mutable struct NormCtx
  me::Array{modular_env, 1}
  nb::Int
  K::AnticNumberField
  ce::crt_env{fmpz}
  ln::Array{fmpz, 1}

  function NormCtx(K::AnticNumberField, nb::Int, deg_one::Bool = false)
    p = p_start
    me = Array{modular_env,1}()

    r = new()
    r.K = K
    r.nb = nb

    lp = fmpz[]

    while nb > 0
      local m
      while true
        p = next_prime(p)
        m = modular_init(K, p)
        if deg_one && length(m.rp) < degree(K)
          continue
        end
        break
      end
      push!(lp, fmpz(p))
      push!(me, m)
      nb = nb - nbits(p)
    end
    r.me = me
    r.ce = crt_env(lp)
    r.ln = Array{fmpz, 1}()
    for i = me
      push!(r.ln, fmpz(0))
    end
    return r
  end
end

function show(io::IO, a::NormCtx)
  println(io, "NormCtx for $(a.K) for $(a.nb) bits, using $(length(a.me)) primes")
end

function norm(a::nf_elem, N::NormCtx, div::fmpz = fmpz(1))
  ln = N.ln
  i = 1
  for m = N.me
    np = UInt(invmod(div, m.p))
    ap = modular_proj(a, m)
    for j=1:length(ap)
      # problem: norm costs memory (in fmpz formally, then new fq_nmod is created)
      np = mulmod(np, coeff(norm(ap[j]), 0), m.rp[1].mod_n, m.rp[1].mod_ninv)
    end
    N.ln[i] = np # problem: np is UInt, ln is not...
    i += 1
  end
  return crt_signed(N.ln, N.ce)
end


