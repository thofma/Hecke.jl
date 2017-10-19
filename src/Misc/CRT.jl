import Hecke.rem!, Nemo.crt, Nemo.zero, Nemo.iszero, Nemo.isone, Nemo.sub!
export crt_env, crt, crt_inv, modular_init, crt_signed

isone(a::Int) = (a==1)

function zero(a::PolyElem)
  return zero(parent(a))
end

@inline function rem!(a::fmpz, b::fmpz, c::fmpz)
  ccall((:fmpz_mod, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}, Ptr{fmpz}), &a, &b, &c)
end

@inline function sub!(a::fmpz, b::fmpz, c::fmpz)
  ccall((:fmpz_sub, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}, Ptr{fmpz}), &a, &b, &c)
end

function rem!(a::fmpz_mod_poly, b::fmpz_mod_poly, c::fmpz_mod_poly)
  ccall((:fmpz_mod_poly_rem, :libflint), Void, (Ptr{fmpz_mod_poly}, Ptr{fmpz_mod_poly}, Ptr{fmpz_mod_poly}), &a, &b, &c)
end

mutable struct crt_env{T}
  pr::Array{T, 1}
  id::Array{T, 1}
  tmp::Array{T, 1}
  t1::T
  t2::T
  n::Int
  M::T #for T=fmpz, holds prod/2

  function crt_env{T}(p::Array{T, 1}) where {T}
    pr = deepcopy(p)
    id = Array{T, 1}()
    i = 1
    while 2*i <= length(pr)
      a = pr[2*i-1]
      b = pr[2*i]
      if false
        g, u, v = gcdx(a, b)
        @assert isone(g)
        push!(id, v*b , u*a )
      else
        # we have 1 = g = u*a + v*b, so v*b = 1-u*a - which saves one mult.
        u = invmod(a, b)
#        @assert  (a*u) % b == 1
        u *= a
        push!(id, 1-u, u)
      end
      push!(pr, a*b)
      i += 1
    end
    r = new{T}()
    r.pr = pr
    r.id = id

    r.tmp = Array{T, 1}()
    n = length(p)
    for i=1:div(n+1, 2)
      push!(r.tmp, zero(p[1]))
    end
    r.t1 = zero(p[1])
    r.t2 = zero(p[1])

    r.n = n
    return r
  end
end

doc"""
***
   crt_env(p::Array{T, 1}) -> crt_env{T}

> Given coprime moduli in some euclidean ring (FlintZZ, nmod_poly, 
>  fmpz_mod_poly), prepare data for fast application of the chinese
>  remander theorem for those moduli.
"""
function crt_env(p::Array{T, 1}) where T
  return crt_env{T}(p)
end

function show(io::IO, c::crt_env{T}) where T
  print(io, "CRT data for moduli ", c.pr[1:c.n])
end

doc"""
***
   crt{T}(b::Array{T, 1}, a::crt_env{T}) -> T

> Given values in b and the environment prepared by crt_env, return the 
> unique (modulo the product) solution to $x \equiv b_i \bmod p_i$.
"""  
function crt(b::Array{T, 1}, a::crt_env{T}) where T
  res = zero(b[1])
  return crt!(res, b, a)
end

function crt!(res::T, b::Array{T, 1}, a::crt_env{T}) where T
  @assert a.n == length(b)
  bn = div(a.n, 2)
  if isodd(a.n)
    @inbounds zero!(a.tmp[1])
    @inbounds add!(a.tmp[1], a.tmp[1], b[end])
    off = 1
  else
    off = 0
  end

  for i=1:bn
    @inbounds mul!(a.t1, b[2*i-1], a.id[2*i-1])
    @inbounds mul!(a.t2, b[2*i], a.id[2*i])
    @inbounds add!(a.tmp[i+off], a.t1, a.t2)
    @inbounds rem!(a.tmp[i+off], a.tmp[i+off], a.pr[a.n+i])
  end

  if isodd(a.n)
    bn += 1
  end

  id_off = a.n - off
  pr_off = a.n + bn - off
#  println(a.tmp, " id_off=$id_off, pr_off=$pr_off, off=$off, bn=$bn")
  while bn>1
    if isodd(bn)
      off = 1
    else
      off = 0
    end
    bn = div(bn, 2)
    for i=1:bn
      if true  # that means we need only one co-factor!!!
        @inbounds sub!(a.t1, a.tmp[2*i-1], a.tmp[2*i])
        @inbounds mul!(a.t1, a.t1, a.id[id_off + 2*i-1])
        @inbounds add!(a.tmp[i+off], a.t1, a.tmp[2*i])
      else
        @inbounds mul!(a.t1, a.tmp[2*i-1], a.id[id_off + 2*i-1])
        @inbounds mul!(a.t2, a.tmp[2*i], a.id[id_off + 2*i])
        @inbounds add!(a.tmp[i + off], a.t1, a.t2)
      end  
      @inbounds rem!(a.tmp[i + off], a.tmp[i + off], a.pr[pr_off+i])
    end
    if off == 1
      @inbounds a.tmp[1], a.tmp[2*bn+1] = a.tmp[2*bn+1], a.tmp[1] 
    end
    id_off += 2*bn
    pr_off += bn
    bn += off
#    println(a.tmp, " id_off=$id_off, pr_off=$pr_off, off=$off, bn=$bn")
  end
  zero!(res)
  @inbounds add!(res, res, a.tmp[1])
  return res
end

function crt_signed!(res::fmpz, b::Array{fmpz, 1}, a::crt_env{fmpz})
  crt!(res, b, a)
  if !isdefined(a, :M)
    a.M = div(prod(a.pr[1:a.n]), 2)
  end
  if res>a.M
    sub!(res, res, a.pr[end])
  end
end

function crt_signed(b::Array{fmpz, 1}, a::crt_env{fmpz})
  res = fmpz()
  crt_signed!(res, b, a)
  return res
end

#in .pr we have the products of pairs, ... in the wrong order
# so we traverse this list backwards, while building the remainders...
#.. and then we do it again, efficiently to avoid resorting and re-allocation
#=
function crt_inv{T}(a::T, c::crt_env{T})
  r = Array{T, 1}()
  push!(r, a)
  i = length(c.pr)-1
  j = 1
  while i>1 
    push!(r, r[j] % c.pr[i], r[j] %c.pr[i-1])
    i -= 2
    j += 1
  end
  return reverse(r, length(r)-c.n+1:length(r))
end
=#

function crt_inv_iterative!(res::Array{T,1}, a::T, c::crt_env{T}) where T
  for i=1:c.n
    if isassigned(res, i)
      rem!(res[i], a, c.pr[i])
    else
      res[i] = a % c.pr[i]
    end
  end
  return res
end

function crt_inv_tree!(res::Array{T,1}, a::T, c::crt_env{T}) where T
  for i=1:c.n
    if !isassigned(res, i)
      res[i] = zero(a)
    end
  end

  i = length(c.pr)-1
  if i == 0
    rem!(res[1], a, c.pr[1])
    return res
  end  
  r = i
  w = r + c.n - 1

  @inbounds zero!(res[r % c.n + 1])
  @inbounds add!(res[r % c.n + 1], res[r % c.n + 1], a)

  while i>1 
    @inbounds rem!(res[w % c.n + 1], res[r % c.n + 1], c.pr[i])
    @inbounds rem!(res[(w+c.n - 1) % c.n + 1], res[r % c.n + 1], c.pr[i - 1])
    w += 2*(c.n-1)
    i -= 2
    r += 1*(c.n-1)
  end

  return res
end

doc"""
***
   crt_inv(a::T, crt_env{T}) -> Array{T, 1}

> Given a \code{crt_env} and an element a, return
> the modular data $a \bmod pr_i$ for all $i$.
> This is essentially the inverse to the \code{crt} function.  
"""
function crt_inv(a::T, c::crt_env{T}) where T
  res = Array{T}(c.n)
  if c.n < 50
    return crt_inv_iterative!(res, a, c)
  else
    return crt_inv_tree!(res, a, c)
  end
end
    
function crt_inv!(res::Array{T, 1}, a::T, c::crt_env{T}) where T
  if c.n < 50
    return crt_inv_iterative!(res, a, c)
  else
    return crt_inv_tree!(res, a, c)
  end
end
    
#explains the idea, but is prone to overflow.
# idea: the tree CRT ..
# given moduli p1 .. pn, we first do (p1, p2), (p2, p3), ...
# then ((p1, p2), (p3, p4)), ...
# until done.
# In every step we need the cofactors, the inverse of pi mod pj
# thus we build a parallel array id for the cofactors
# in id[2i-1], id[2i] are the cofactors for pr[2i-1], pr[2i]
# To recombine, we basically loop through the cofactors:
# use id[1], id[2] to combine b[1], b[2] AND append to b
# The product pr[1]*pr[2] was appended to pr, thus we can walk through the 
# growing list till the end
# For the optimized version, we have tmp-array to hold the CRT results
# plus t1, t2 for temporaty products.
function crt(b::Array{Int, 1}, a::crt_env{Int})
  i = a.n+1
  j = 1
  while j <= length(b)
    push!(b, (b[j-1]*a.id[j-1] + b[j]*a.id[j]) % a.pr[i])
    j += 2
    i += 1
  end
  return b[end]
end

function crt_test(a::crt_env{fmpz}, b::Int)
  z = [fmpz(0) for x=1:a.n]
  for i=1:b
    b = rand(0:a.pr[end]-1)
    for j=1:a.n
      rem!(z[j], b, a.pr[j])
    end
    if b != crt(z, a)
      println("problem: $b and $z")
    end
    @assert b == crt(z, a)
  end
end


doc"""
***
  crt(r1::PolyElem, m1::PolyElem, r2::PolyElem, m2::PolyElem) -> PolyElem

> Find $r$ such that $r \equiv r_1 \pmod m_1$ and $r \equiv r_2 \pmod m_2$
"""
function crt(r1::PolyElem{T}, m1::PolyElem{T}, r2::PolyElem{T}, m2::PolyElem{T}) where T
  g, u, v = gcdx(m1, m2)
  m = m1*m2
  return (r1*v*m2 + r2*u*m1) % m
end

doc"""
***
  crt_iterative(r::Array{T, 1}, m::Array{T,1}) -> T

> Find $r$ such that $r \equiv r_i \pmod m_i$ for all $i$.
> A plain iteration is performed.
"""
function crt_iterative(r::Array{T, 1}, m::Array{T, 1}) where T
  p = crt(r[1], m[1], r[2], m[2])
  d = m[1] * m[2]
  for i = 3:length(m)
    p = crt(p, d, r[i], m[i])
    d *= m[i]
  end
  return p
end

doc"""
***
  crt_tree(r::Array{T, 1}, m::Array{T,1}) -> T

> Find $r$ such that $r \equiv r_i \pmod m_i$ for all $i$.
> A tree based strategy is used that is asymptotically fast.
"""
function crt_tree(r::Array{T, 1}, m::Array{T, 1}) where T
  if isodd(length(m))
    M = [m[end]]
    V = [r[end]]
  else
    M = Array{T, 1}()
    V = Array{T, 1}()
  end

  for i=1:div(length(m), 2)
    push!(V, crt(r[2*i-1], m[2*i-1], r[2*i], m[2*i]))
    push!(M, m[2*i-1]*m[2*i])
  end
  i = 1
  while 2*i <= length(V)
    push!(V, crt(V[2*i-1], M[2*i-1], V[2*i], M[2*i]))
    push!(M, M[2*i-1] * M[2*i])
    i += 1
  end
#  println("M = $M\nV = $V")
  return V[end]
end

doc"""
***
  crt(r::Array{T, 1}, m::Array{T,1}) -> T

> Find $r$ such that $r \equiv r_i \pmod m_i$ for all $i$.
"""
function crt(r::Array{T, 1}, m::Array{T, 1}) where T 
  length(r) == length(m) || error("Arrays need to be of same size")
  if length(r) < 15
    return crt_iterative(r, m)
  else
    return crt_tree(r, m)
  end
end

function crt_test_time_all(np::Int, n::Int)
  p = next_prime(fmpz(2)^60)
  m = [p]
  x = fmpz(1)
  for i=1:np-1
    push!(m, next_prime(m[end]))
  end
  v = [rand(0:x-1) for x = m]
  println("crt_env...")
  @time ce = crt_env(m)
  @time for i=1:n 
    x = crt(v, ce)
  end
  
  println("iterative...")
  @time for i=1:n
    x = crt_iterative(v, m)
  end

  println("tree...")
  @time for i=1:n
    x = crt_tree(v, m)
  end

  println("inv_tree")
  @time for i=1:n
    crt_inv_tree!(m, x, ce)
  end
  
  println("inv_iterative")
  @time for i=1:n
    crt_inv_iterative!(m, x, ce)
  end
end  

doc"""
    induce_crt(a::fmpz_poly, p::fmpz, b::fmpz_poly, q::fmpz, signed::Bool = false) -> fmpz_poly
> Given integral polynomials $a$ and $b$ as well as coprime integer moduli
> $p$ and $q$, find $f = a \bmod p$ and $f=b \bmod q$.
> If signed is set, the symmetric representative is used, the positive one
> otherwise.
"""
function induce_crt(a::fmpz_poly, p::fmpz, b::fmpz_poly, q::fmpz, signed::Bool = false)
  c = parent(a)()
  pi = invmod(p, q)
  mul!(pi, pi, p)
  pq = p*q
  if signed
    pq2 = div(pq, 2)
  else
    pq2 = fmpz(0)
  end
  for i=0:max(degree(a), degree(b))
    setcoeff!(c, i, Hecke.inner_crt(coeff(a, i), coeff(b, i), pi, pq, pq2))
  end
  return c, pq
end

doc"""
    induce_crt(L::Array, c::crt_env{fmpz}) -> fmpz_poly
> Given fmpz_poly polynomials $L[i]$ and a {{{crt_env}}}, apply the
> {{{crt}}} function to each coefficient retsulting in a polynomial $f = L[i] \bmod p[i]$.
"""
function induce_crt(L::Array, c::crt_env{fmpz})
  Zx, x = FlintZZ["x"]
  res = Zx()
  m = maximum(degree(x) for x = L)

  for i=0:m
    setcoeff!(res, i, crt([lift(coeff(x, i)) for x =L], c))
  end
  return res
end

doc"""
***
  _num_setcoeff!(a::nf_elem, n::Int, c::fmpz)
  _num_setcoeff!(a::nf_elem, n::Int, c::UInt)

> Sets the $n$-th coefficient in $a$ to $c$. No checks performed, use
> only if you know what you're doing.
"""
function _num_setcoeff!(a::nf_elem, n::Int, c::fmpz)
  K = a.parent
  @assert n < degree(K) && n >=0
  ra = pointer_from_objref(a)
  if degree(K) == 1
    ccall((:fmpz_set, :libflint), Void, (Ptr{Void}, Ptr{fmpz}), ra, &c)
    ccall((:fmpq_canonicalise, :libflint), Void, (Ptr{nf_elem}, ), &a)
  elseif degree(K) == 2
     ccall((:fmpz_set, :libflint), Void, (Ptr{Void}, Ptr{fmpz}), ra+n*sizeof(Int), &c)
  else
    ccall((:fmpq_poly_set_coeff_fmpz, :libflint), Void, (Ptr{nf_elem}, Int, Ptr{fmpz}), &a, n, &c)
   # includes canonicalisation and treatment of den.
  end
end

function _num_setcoeff!(a::nf_elem, n::Int, c::UInt)
  K = a.parent
  @assert n < degree(K) && n >=0

  ra = pointer_from_objref(a)
   
  if degree(K) == 1
    ccall((:fmpz_set_ui, :libflint), Void, (Ptr{Void}, UInt), ra, c)
    ccall((:fmpq_canonicalise, :libflint), Void, (Ptr{nf_elem}, ), &a)
  elseif degree(K) == 2
    ccall((:fmpz_set_ui, :libflint), Void, (Ptr{Void}, UInt), ra+n*sizeof(Int), c)
  else
    ccall((:fmpq_poly_set_coeff_ui, :libflint), Void, (Ptr{nf_elem}, Int, UInt), &a, n, c)
   # includes canonicalisation and treatment of den.
  end
end

mutable struct modular_env
  p::fmpz
  up::UInt
  upinv::UInt

  fld::Array{FqNmodFiniteField, 1}
  fldx::Array{FqNmodPolyRing, 1}
  ce::crt_env{nmod_poly}
  rp::Array{nmod_poly, 1}
  res::Array{fq_nmod, 1}
  Fpx::NmodPolyRing
  K::AnticNumberField
  Rp::Array{fq_nmod_poly, 1}
  Kx::Generic.PolyRing{nf_elem}

  function modular_env()
    return new()
  end
end

function show(io::IO, me::modular_env)
  println("modular environment for p=$(me.p), using $(me.ce.n) ideals")
end

doc"""
***
  modular_init(K::AnticNumberField, p::fmpz) -> modular_env
  modular_init(K::AnticNumberField, p::Integer) -> modular_env

> Given a number field $K$ and an ``easy'' prime $p$ (ie. fits into an 
> \code{Int} and is coprime to the polynomial discriminant), compute
> the residue class fields of the associated primes ideals above $p$.
> Returns data that can be used by \code{modular_proj} and \code{modular_lift}.
"""
function modular_init(K::AnticNumberField, p::fmpz; deg_limit::Int=0, max_split::Int = 0)
  @assert isprime(p)
  UInt(p) # to enforce p being small

  me = modular_env()
  me.Fpx = PolynomialRing(ResidueRing(FlintZZ, UInt(p), cached = false), "_x", cached=false)[1]
  fp = me.Fpx(K.pol)
  lp = factor(fp)
  if Set(values(lp.fac)) != Set([1])
    throw(BadPrime(p))
  end
  pols = collect(keys(lp.fac))
  if deg_limit > 0
    pols = pols[find(x -> degree(x) <= deg_limit, pols)]
  end

  if max_split > 0
    pols = pols[1:min(length(pols), max_split)]
  end
  me.ce = crt_env(pols)
  me.fld = [FqNmodFiniteField(x, :$) for x = pols]  #think about F_p!!!
                                   # and chacheing
  me.rp = Array{nmod_poly}(length(pols))
  me.res = Array{fq_nmod}(me.ce.n)

  me.p = p
  me.K = K
  me.up = UInt(p)
  me.upinv = ccall((:n_preinvert_limb, :libflint), UInt, (UInt, ), me.up)
  return me
end

function modular_init(K::AnticNumberField, p::Integer; deg_limit::Int=0, max_split::Int = 0)
  return modular_init(K, fmpz(p), deg_limit = deg_limit, max_split = max_split)
end

doc"""
***
  modular_proj(a::nf_elem, me::modular_env) -> Array{fq_nmod, 1}

> Given an algebraic number $a$ and data \code{me} as computed by
> \code{modular_init}, project $a$ onto the residue class fields.
"""
function modular_proj(a::nf_elem, me::modular_env)
  ap = me.Fpx(a)
  crt_inv!(me.rp, ap, me.ce)
  for i=1:me.ce.n
    F = me.fld[i]
    if isassigned(me.res, i)
      u = me.res[i]
    else
      u = F()
    end
    ccall((:fq_nmod_set, :libflint), Void,
                (Ptr{fq_nmod}, Ptr{nmod_poly}, Ptr{FqNmodFiniteField}),
                &u, &me.rp[i], &F)
    me.res[i] = u
  end
  return me.res
end

doc"""
***
  modular_lift(a::Array{fq_nmod}, me::modular_env) -> nf_elem

> Given an array of elements as computed by \code{modular_proj},
> compute a global pre-image using some efficient CRT.
"""
function modular_lift(a::Array{fq_nmod, 1}, me::modular_env)
  for i=1:me.ce.n
    ccall((:nmod_poly_set, :libflint), Void, (Ptr{nmod_poly}, Ptr{fq_nmod}), &me.rp[i], &a[i])
  end
  ap = crt(me.rp, me.ce)
  r = me.K()
  for i=0:ap.length-1
    u = ccall((:nmod_poly_get_coeff_ui, :libflint), UInt, (Ptr{nmod_poly}, Int), &ap, i)
    _num_setcoeff!(r, i, u)
  end
  return r
end

doc"""
***
  modular_proj(a::Generic.Poly{nf_elem}, me::modular_env) -> Array

> Apply the \code{modular_proj} function to each coeficient of $a$.
> Computes an array of polynomials over the respective residue class fields.
"""
function modular_proj(a::Generic.Poly{nf_elem}, me::modular_env)

  if !isdefined(me, :fldx)
    me.fldx = [PolynomialRing(x, "_x")[1] for x = me.fld]
    me.Rp = Array{fq_nmod_poly}(me.ce.n)
    for i =1:me.ce.n
      me.Rp[i] = me.fldx[i](0)
    end
    me.Kx = parent(a)
  end  

  for j=1:me.ce.n
    zero!(me.Rp[j])
  end
  for i=0:length(a)-1
    crt_inv!(me.rp, me.Fpx(coeff(a, i)), me.ce)
    for j=1:me.ce.n
      u = coeff(me.Rp[j], i)
      ccall((:fq_nmod_set, :libflint), Void,
                   (Ptr{fq_nmod}, Ptr{nmod_poly}, Ptr{FqNmodFiniteField}),
                   &u, &me.rp[j], &me.fld[j])
      setcoeff!(me.Rp[j], i, u)
    end
  end  
  return me.Rp
end

doc"""
***
  modular_lift(a::Array{fq_nmod_poly}, me::modular_env) -> Generic.Poly{nf_elem}

> Apply the \code{modular_lift} function to each coeficient of $a$.
> Computes a polynomial over the number field.
"""
function modular_lift(a::Array{fq_nmod_poly, 1}, me::modular_env)
  res = me.Kx()
  d = maximum([x.length for x = a])
  for i=0:d-1
    for j=1:me.ce.n
      ccall((:nmod_poly_set, :libflint), Void, (Ptr{nmod_poly}, Ptr{fq_nmod}), &me.rp[j], &coeff(a[j], i))
    end
    ap = crt(me.rp, me.ce)
    r = coeff(res, i)
    for j=0:ap.length-1
      u = ccall((:nmod_poly_get_coeff_ui, :libflint), UInt, (Ptr{nmod_poly}, Int), &ap, j)
      _num_setcoeff!(r, j, u)
    end
    setcoeff!(res, i, r)
  end  
  return res
end

doc"""
***
  modular_proj(a::Generic.Mat{nf_elem}, me::modular_env) -> Array{Matrix}
  modular_proj(a::Generic.Mat{NfOrdElem}, me::modular_env) -> Array{Matrix}

> Apply the \code{modular_proj} function to each entry of $a$.
> Computes an array of matrices over the respective residue class fields.
"""
function modular_proj(a::Generic.Mat{nf_elem}, me::modular_env)
  Mp = []
  for i=1:me.ce.n
    push!(Mp, zero_matrix(me.fld[i], rows(a), cols(a)))
  end
  for i=1:rows(a)
    for j=1:cols(a)
      im =modular_proj(a[i,j], me)
      for k=1:me.ce.n
        setindex!(Mp[k], im[k], i, j)
      end
    end
  end  
  return Mp
end  

function modular_proj(a::Generic.Mat{NfOrdElem}, me::modular_env)
  Mp = []
  for i=1:me.ce.n
    push!(Mp, zero_matrix(me.fld[i], rows(a), cols(a)))
  end
  for i=1:rows(a)
    for j=1:cols(a)
      im =modular_proj(me.K(a[i,j]), me)
      for k=1:me.ce.n
        setindex!(Mp[k], im[k], i, j)
      end
    end
  end  
  return Mp
end


