import Nemo.crt, Nemo.zero, Nemo.iszero, Nemo.isone, Nemo.sub!

mutable struct crt_env{T}
  pr::Vector{T}
  id::Vector{T}
  tmp::Vector{T}
  t1::T
  t2::T
  n::Int
  M::T #for T=ZZRingElem, holds prod/2

  function crt_env{T}(p::Vector{T}) where {T}
    pr = deepcopy(p)
    id = Vector{T}()
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

    r.tmp = Vector{T}()
    n = length(p)
    for i=1:div(n+1, 2)
      push!(r.tmp, zero(parent(p[1])))
    end
    r.t1 = zero(parent(p[1]))
    r.t2 = zero(parent(p[1]))

    r.n = n
    return r
  end
end

@doc raw"""
    crt_env(p::Vector{T}) -> crt_env{T}

Given coprime moduli in some euclidean ring (FlintZZ, zzModRingElem\_poly,
ZZRingElem\_mod\_poly), prepare data for fast application of the chinese
remainder theorem for those moduli.
"""
function crt_env(p::Vector{T}) where T
  return crt_env{T}(p)
end

function show(io::IO, c::crt_env{T}) where T
  print(io, "CRT data for moduli ", c.pr[1:c.n])
end

@doc raw"""
    crt{T}(b::Vector{T}, a::crt_env{T}) -> T

Given values in $b$ and the environment prepared by `crt\_env`, return the
unique (modulo the product) solution to $x \equiv b_i \bmod p_i$.
"""
function crt(b::Vector{T}, a::crt_env{T}) where T
  res = zero(parent(b[1]))
  return crt!(res, b, a)
end

function crt!(res::T, b::Vector{T}, a::crt_env{T}) where T
  @assert a.n == length(b)
  bn = div(a.n, 2)
  if isodd(a.n)
    @inbounds zero!(a.tmp[1])
    @inbounds a.tmp[1] = add!(a.tmp[1], a.tmp[1], b[end])
    off = 1
  else
    off = 0
  end

  for i=1:bn
    @inbounds a.t1 = mul!(a.t1, b[2*i-1], a.id[2*i-1])
    @inbounds a.t2 = mul!(a.t2, b[2*i], a.id[2*i])
    @inbounds a.tmp[i+off] = add!(a.tmp[i+off], a.t1, a.t2)
    @inbounds a.tmp[i+off] = rem!(a.tmp[i+off], a.tmp[i+off], a.pr[a.n+i])
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
        @inbounds a.t1 = sub!(a.t1, a.tmp[2*i-1], a.tmp[2*i])
        @inbounds a.t1 = mul!(a.t1, a.t1, a.id[id_off + 2*i-1])
        @inbounds a.tmp[i+off] = add!(a.tmp[i+off], a.t1, a.tmp[2*i])
      else
        @inbounds mul!(a.t1, a.tmp[2*i-1], a.id[id_off + 2*i-1])
        @inbounds mul!(a.t2, a.tmp[2*i], a.id[id_off + 2*i])
        @inbounds add!(a.tmp[i + off], a.t1, a.t2)
      end
      @inbounds a.tmp[i + off] = rem!(a.tmp[i + off], a.tmp[i + off], a.pr[pr_off+i])
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
  @inbounds res = add!(res, res, a.tmp[1])
  return res
end

function crt_signed!(res::ZZRingElem, b::Vector{ZZRingElem}, a::crt_env{ZZRingElem})
  crt!(res, b, a)
  if !isdefined(a, :M)
    a.M = div(prod(a.pr[1:a.n]), 2)
  end
  if res>a.M
    sub!(res, res, a.pr[end])
  end
end

function crt_signed(b::Vector{ZZRingElem}, a::crt_env{ZZRingElem})
  res = ZZRingElem()
  crt_signed!(res, b, a)
  return res
end

#in .pr we have the products of pairs, ... in the wrong order
# so we traverse this list backwards, while building the remainders...
#.. and then we do it again, efficiently to avoid resorting and re-allocation
#=
function crt_inv{T}(a::T, c::crt_env{T})
  r = Vector{T}()
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

function crt_inv_iterative!(res::Vector{T}, a::T, c::crt_env{T}) where T
  for i=1:c.n
    if isassigned(res, i)
      rem!(res[i], a, c.pr[i])
    else
      res[i] = a % c.pr[i]
    end
  end
  return res
end

function crt_inv_tree!(res::Vector{T}, a::T, c::crt_env{T}) where T
  for i=1:c.n
    if !isassigned(res, i)
      res[i] = zero(parent(a))
    end
  end

  i = length(c.pr)-1
  if i == 0
    res[1] = rem!(res[1], a, c.pr[1])
    return res
  end
  r = i
  w = r + c.n - 1

  @inbounds zero!(res[r % c.n + 1])
  @inbounds res[r % c.n + 1] = add!(res[r % c.n + 1], res[r % c.n + 1], a)

  while i>1
    @inbounds res[w % c.n + 1] = rem!(res[w % c.n + 1], res[r % c.n + 1], c.pr[i])
    @inbounds res[(w+c.n - 1) % c.n + 1] = rem!(res[(w+c.n - 1) % c.n + 1], res[r % c.n + 1], c.pr[i - 1])
    w += 2*(c.n-1)
    i -= 2
    r += 1*(c.n-1)
  end

  return res
end

@doc raw"""
    crt_inv(a::T, crt_env{T}) -> Vector{T}

Given a $\code{crt_env}$ and an element $a$, return
the modular data $a \bmod pr_i$ for all $i$.
This is essentially the inverse to the $\code{crt}$ function.
"""
function crt_inv(a::T, c::crt_env{T}) where T
  res = Array{T}(undef, c.n)
  if c.n < 50
    return crt_inv_iterative!(res, a, c)
  else
    return crt_inv_tree!(res, a, c)
  end
end

function crt_inv!(res::Vector{T}, a::T, c::crt_env{T}) where T
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
function crt(b::Vector{Int}, a::crt_env{Int})
  i = a.n+1
  j = 1
  while j <= length(b)
    push!(b, (b[j-1]*a.id[j-1] + b[j]*a.id[j]) % a.pr[i])
    j += 2
    i += 1
  end
  return b[end]
end

function crt_test(a::crt_env{ZZRingElem}, b::Int)
  z = [ZZRingElem(0) for x=1:a.n]
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


@doc raw"""
    crt(r1::PolyRingElem, m1::PolyRingElem, r2::PolyRingElem, m2::PolyRingElem) -> PolyRingElem

Find $r$ such that $r \equiv r_1 \pmod m_1$ and $r \equiv r_2 \pmod m_2$
"""
function crt(r1::PolyRingElem{T}, m1::PolyRingElem{T}, r2::PolyRingElem{T}, m2::PolyRingElem{T}) where T
  g, u, v = gcdx(m1, m2)
  m = m1*m2
  return (r1*v*m2 + r2*u*m1) % m
end

@doc raw"""
    crt_iterative(r::Vector{T}, m::Vector{T}) -> T

Find $r$ such that $r \equiv r_i \pmod m_i$ for all $i$.
A plain iteration is performed.
"""
function crt_iterative(r::Vector{T}, m::Vector{T}) where T
  if length(r) == 1
    return r[1]
  end
  p = crt(r[1], m[1], r[2], m[2])
  d = m[1] * m[2]
  for i = 3:length(m)
    p = crt(p, d, r[i], m[i])
    d *= m[i]
  end
  return p
end

@doc raw"""
    crt_tree(r::Vector{T}, m::Vector{T}) -> T

Find $r$ such that $r \equiv r_i \pmod m_i$ for all $i$.
A tree based strategy is used that is asymptotically fast.
"""
function crt_tree(r::Vector{T}, m::Vector{T}) where T
  if isodd(length(m))
    M = [m[end]]
    V = [r[end]]
  else
    M = Vector{T}()
    V = Vector{T}()
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

@doc raw"""
    crt(r::Vector{T}, m::Vector{T}) -> T

Find $r$ such that $r \equiv r_i \pmod m_i$ for all $i$.
"""
function crt(r::Vector{T}, m::Vector{T}) where T
  length(r) == length(m) || error("Arrays need to be of same size")
  if length(r) == 1
    return r[1] % m[1]
  end
  if length(r) < 15
    return crt_iterative(r, m)
  else
    return crt_tree(r, m)
  end
end

function crt_test_time_all(Kx::PolyRing{<:FinFieldElem}, np::Int, n::Int)
  m = elem_type(Kx)[]
  x = gen(Kx)
  K = base_ring(Kx)
  @assert np^2 < order(K)
  while true
    t = x-rand(K)
    if t in m
      continue
    else
      push!(m, t)
      if length(m) >= np
        break
      end
    end
  end

  v = [Kx(rand(K)) for x = m]
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


function crt_test_time_all(np::Int, n::Int)
  p = next_prime(ZZRingElem(2)^60)
  m = [p]
  x = ZZRingElem(1)
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

@doc raw"""
    induce_crt(a::ZZPolyRingElem, p::ZZRingElem, b::ZZPolyRingElem, q::ZZRingElem, signed::Bool = false) -> ZZPolyRingElem

Given integral polynomials $a$ and $b$ as well as coprime integer moduli
$p$ and $q$, find $f = a \bmod p$ and $f=b \bmod q$.
If `signed` is set, the symmetric representative is used, the positive one
otherwise.
"""
function induce_crt(a::ZZPolyRingElem, p::ZZRingElem, b::ZZPolyRingElem, q::ZZRingElem, signed::Bool = false)
  c = parent(a)()
  pi = invmod(p, q)
  mul!(pi, pi, p)
  pq = p*q
  if signed
    pq2 = div(pq, 2)
  else
    pq2 = ZZRingElem(0)
  end
  for i=0:max(degree(a), degree(b))
    setcoeff!(c, i, Hecke.inner_crt(coeff(a, i), coeff(b, i), pi, pq, pq2))
  end
  return c, pq
end

@doc raw"""
    induce_crt(L::Vector{PolyRingElem}, c::crt_env{ZZRingElem}) -> ZZPolyRingElem

Given ZZRingElem\_poly polynomials $L[i]$ and a `crt\_env`, apply the
`crt` function to each coefficient resulting in a polynomial $f = L[i] \bmod p[i]$.
"""
function induce_crt(L::Vector{T}, c::crt_env{ZZRingElem}) where {T <: PolyRingElem}
  Zx, x = FlintZZ["x"]
  res = Zx()
  m = maximum(degree(x) for x = L)

  for i=0:m
    setcoeff!(res, i, crt([lift(coeff(x, i)) for x =L], c))
  end
  return res
end

#@doc raw"""
#    _num_setcoeff!(a::AbsSimpleNumFieldElem, n::Int, c::ZZRingElem)
#    _num_setcoeff!(a::AbsSimpleNumFieldElem, n::Int, c::Integer)
#
#Sets the $n$-th coefficient in $a$ to $c$. No checks performed, use
#only if you know what you're doing.
#"""
function _num_setcoeff!(a::AbsSimpleNumFieldElem, n::Int, c::ZZRingElem)
  K = parent(a)
  ra = pointer_from_objref(a)
  if degree(K) == 1
    @assert n == 0
    ccall((:fmpz_set, libflint), Nothing, (Ref{Nothing}, Ref{ZZRingElem}), ra, c)
    ccall((:fmpq_canonicalise, libflint), Nothing, (Ref{AbsSimpleNumFieldElem}, ), a)
  elseif degree(K) == 2
     @assert n >= 0  && n <= 3
     ccall((:fmpz_set, libflint), Nothing, (Ref{Nothing}, Ref{ZZRingElem}), ra+n*sizeof(Int), c)
  else
    @assert n < degree(K) && n >=0
    ccall((:fmpq_poly_set_coeff_fmpz, libflint), Nothing, (Ref{AbsSimpleNumFieldElem}, Int, Ref{ZZRingElem}), a, n, c)
   # includes canonicalisation and treatment of den.
  end
end

function _num_setcoeff!(a::AbsSimpleNumFieldElem, n::Int, c::UInt)
  K = a.parent
  @assert n < degree(K) && n >=0

  ra = pointer_from_objref(a)

  if degree(K) == 1
    ccall((:fmpz_set_ui, libflint), Nothing, (Ref{Nothing}, UInt), ra, c)
    ccall((:fmpq_canonicalise, libflint), Nothing, (Ref{AbsSimpleNumFieldElem}, ), a)
  elseif degree(K) == 2
    ccall((:fmpz_set_ui, libflint), Nothing, (Ref{Nothing}, UInt), ra+n*sizeof(Int), c)
  else
    ccall((:fmpq_poly_set_coeff_ui, libflint), Nothing, (Ref{AbsSimpleNumFieldElem}, Int, UInt), a, n, c)
   # includes canonicalisation and treatment of den.
  end
end

function _num_setcoeff!(a::AbsSimpleNumFieldElem, n::Int, c::Integer)
  _num_setcoeff!(a, n, ZZRingElem(c))
end

@doc raw"""
    induce_crt(L::Vector{MatElem}, c::crt_env{ZZRingElem}) -> ZZMatrix

Given matrices $L[i]$ and a `crt\_env`, apply the
`crt` function to each coefficient resulting in a matrix $M = L[i] \bmod p[i]$.
"""
function induce_crt(L::Vector{T}, c::crt_env{ZZRingElem}, signed::Bool = false) where {T <: MatElem}
  res = zero_matrix(FlintZZ, nrows(L[1]), ncols(L[1]))

  if signed
    cr = crt_signed
  else
    cr = crt
  end

  for i=1:nrows(L[1])
    for j=1:ncols(L[1])
      res[i,j] = cr([lift(x[i,j]) for x =L], c)
    end
  end
  return res
end


mutable struct modular_env
  p::ZZRingElem
  up::UInt
  upinv::UInt

  fld::Vector{fqPolyRepField}
  fldx::Vector{fqPolyRepPolyRing}
  ce::crt_env{zzModPolyRingElem}
  rp::Vector{zzModPolyRingElem}
  res::Vector{fqPolyRepFieldElem}
  Fpx::zzModPolyRing
  K::AbsSimpleNumField
  Rp::Vector{fqPolyRepPolyRingElem}
  Kx::Generic.PolyRing{AbsSimpleNumFieldElem}
  Kxy::Generic.MPolyRing{AbsSimpleNumFieldElem}
  Kpxy::zzModMPolyRing

  function modular_env()
    return new()
  end
end

Base.isempty(me::modular_env) = !isdefined(me, :ce)

function show(io::IO, me::modular_env)
  if isempty(me)
    println("modular environment for p=$(me.p), using $(0) ideals")
  else
    println("modular environment for p=$(me.p), using $(me.ce.n) ideals")
  end
end

@doc raw"""
    modular_init(K::AbsSimpleNumField, p::ZZRingElem) -> modular_env
    modular_init(K::AbsSimpleNumField, p::Integer) -> modular_env

Given a number field $K$ and an ``easy'' prime $p$ (i.e. fits into an
\code{Int} and is coprime to the polynomial discriminant), compute
the residue class fields of the associated prime ideals above $p$.
Returns data that can be used by \code{modular_proj} and \code{modular_lift}.
"""
function modular_init(K::AbsSimpleNumField, p::ZZRingElem; deg_limit::Int=0, max_split::Int = 0)
  @hassert :AbsNumFieldOrder 1 is_prime(p)
  me = modular_env()
  me.Fpx = polynomial_ring(residue_ring(FlintZZ, Int(p), cached = false)[1], "_x", cached=false)[1]
  fp = me.Fpx(K.pol)
  lp = factor(fp)
  if Set(values(lp.fac)) != Set([1])
    throw(BadPrime(p))
  end
  pols = collect(keys(lp.fac))
  if deg_limit > 0
    pols = pols[findall(x -> degree(x) <= deg_limit, pols)]
  end

  if max_split > 0
    pols = pols[1:min(length(pols), max_split)]
  end
  if length(pols) == 0
    return me
  end
  me.ce = crt_env(pols)
  me.fld = [fqPolyRepField(x, :$, false) for x = pols]  #think about F_p!!!
                                   # and chacheing
  me.rp = Vector{zzModPolyRingElem}(undef, length(pols))
  me.res = Vector{fqPolyRepFieldElem}(undef, me.ce.n)

  me.p = p
  me.K = K
  me.up = UInt(p)
  me.upinv = ccall((:n_preinvert_limb, libflint), UInt, (UInt, ), me.up)
  return me
end

function modular_init(K::AbsSimpleNumField, p::Integer; deg_limit::Int=0, max_split::Int = 0)
  return modular_init(K, ZZRingElem(p), deg_limit = deg_limit, max_split = max_split)
end

@doc raw"""
    modular_proj(a::AbsSimpleNumFieldElem, me::modular_env) -> Vector{fqPolyRepFieldElem}

Given an algebraic number $a$ and data \code{me} as computed by
\code{modular_init}, project $a$ onto the residue class fields.
"""
function modular_proj(a::AbsSimpleNumFieldElem, me::modular_env)
  ap = me.Fpx(a)
  crt_inv!(me.rp, ap, me.ce)
  for i=1:me.ce.n
    F = me.fld[i]
    if isassigned(me.res, i)
      u = me.res[i]
    else
      u = F()
    end
    ccall((:fq_nmod_set, libflint), Nothing,
                (Ref{fqPolyRepFieldElem}, Ref{zzModPolyRingElem}, Ref{fqPolyRepField}),
                u, me.rp[i], F)
    me.res[i] = u
  end
  return me.res
end

@doc raw"""
    modular_proj(a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, me::modular_env) -> Vector{fqPolyRepFieldElem}

Given an algebraic number $a$ in factored form and data \code{me} as computed by
\code{modular_init}, project $a$ onto the residue class fields.
"""
function modular_proj(A::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, me::modular_env)
  if length(A.fac) > 100 #arbitrary
    return modular_proj_vec(A, me)
  end

  for i=1:me.ce.n
    me.res[i] = one(me.fld[i])
  end
  for (a, v) = A.fac
    ap = me.Fpx(a)
    crt_inv!(me.rp, ap, me.ce)
    for i=1:me.ce.n
      F = me.fld[i]
      u = F()
      ccall((:fq_nmod_set, libflint), Nothing,
                  (Ref{fqPolyRepFieldElem}, Ref{zzModPolyRingElem}, Ref{fqPolyRepField}),
                  u, me.rp[i], F)
      eee = mod(v, size(F)-1)
      if abs(eee-size(F)+1) < div(eee, 2)
        eee = eee+1-size(F)
      end
      #@show v, eee, size(F)-1
      u = u^eee
      me.res[i] *= u
    end
  end
  return me.res
end
function _apply_frob(a::fqPolyRepFieldElem, F)
  b = parent(a)()
  apply!(b, a, F)
  return b
end

function modular_proj_vec(A::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, me::modular_env)
  for i=1:me.ce.n
    me.res[i] = one(me.fld[i])
  end
  p = Int(me.p)
  data = [Vector{Tuple{fqPolyRepFieldElem, ZZRingElem, Int}}() for i=1:me.ce.n]
  Frob = map(FrobeniusCtx, me.fld)
  dig = [zeros(Int, degree(x)) for x = me.fld]
  for (a, v) = A.fac
    ap = me.Fpx(a)
    crt_inv!(me.rp, ap, me.ce)
    for i=1:me.ce.n
      F = me.fld[i]
      u = F()
      ccall((:fq_nmod_set, libflint), Nothing,
                  (Ref{fqPolyRepFieldElem}, Ref{zzModPolyRingElem}, Ref{fqPolyRepField}),
                  u, me.rp[i], F)
      eee = mod(v, size(F)-1)

      if abs(eee-size(F)+1) < div(eee, 2)
        eee = eee+1-size(F)
      end
      if eee < 0
        u = inv(u)
        eee = -eee
      end
      if false
        d = digits!(dig[i], eee, base = p)
        for s = d
          if !iszero(s)
            if s<0
              push!(data[i], (inv(u), -s, nbits(-s)))
            else
              push!(data[i], (u, s, nbits(s)))
            end
          end
          u = _apply_frob(u, Frob[i])
        end
      else
        push!(data[i], (u, eee, nbits(eee)))
      end
    end
  end

  res = fqPolyRepFieldElem[]
  res = map(inner_eval, data)

  return res
end

@inline function mul_raw!(a::fqPolyRepFieldElem, b::fqPolyRepFieldElem, c::fqPolyRepFieldElem, K::fqPolyRepField)
  ccall((:fq_nmod_mul, libflint), Nothing, (Ref{fqPolyRepFieldElem}, Ref{fqPolyRepFieldElem}, Ref{fqPolyRepFieldElem}, Ref{fqPolyRepField}), a, b, c, K)
end

@inbounds function inner_eval(z::Vector{Tuple{fqPolyRepFieldElem, Int, Int}})
  sort!(z, lt = (a,b) -> isless(b[2], a[2]))
  t = z[1][3] #should be largest...
  it = 1<<(t-1)
  u = one(z[1][1])
  K = parent(u)
#    @show map(i->nbits(i[2]), z)
  while t > 0
    i = 1
    v = one(z[1][1])
    while z[i][3] >= t
#        @show i, is[i][1]
      if (z[i][2] & it) != 0
        mul_raw!(v, v, z[i][1], K)
      end
      i += 1
      if i > length(z)
        break
      end
    end
    mul_raw!(u, u, u, K)
    mul_raw!(u, u, v, K)
    t -= 1
    it = it >> 1
  end
  return u
end

@inbounds function inner_eval(z::Vector{Tuple{fqPolyRepFieldElem, ZZRingElem, Int}})
  sort!(z, lt = (a,b) -> isless(b[2], a[2]))
  t = z[1][3] #should be largest...
  it = [bits(i[2]) for i=z]
  is = map(iterate, it)
  u = one(z[1][1])
  K = parent(u)
#    @show map(i->nbits(i[2]), z)
  while t > 0
    i = 1
    v = one(z[1][1])
    while z[i][3] >= t
#        @show i, is[i][1]
      if is[i][1]
        mul_raw!(v, v, z[i][1], K)
      end

      if t > 1
        st = iterate(it[i], is[i][2])
        if st === nothing
          @show it[i], is[i], t
          error("should never happen")
        else
          is[i] = st
        end
      end
      i += 1
      if i > length(z)
        break
      end
    end
    mul_raw!(u, u, u, K)
    mul_raw!(u, u, v, K)
    t -= 1
  end
  return u
end



@doc raw"""
    modular_lift(a::Array{fqPolyRepFieldElem}, me::modular_env) -> AbsSimpleNumFieldElem

Given an array of elements as computed by \code{modular_proj},
compute a global pre-image using some efficient CRT.
"""
function modular_lift(a::Vector{fqPolyRepFieldElem}, me::modular_env)
  for i=1:me.ce.n
    ccall((:nmod_poly_set, libflint), Nothing, (Ref{zzModPolyRingElem}, Ref{fqPolyRepFieldElem}), me.rp[i], a[i])
  end
  ap = crt(me.rp, me.ce)
  r = me.K()
  for i=0:ap.length-1
    u = ccall((:nmod_poly_get_coeff_ui, libflint), UInt, (Ref{zzModPolyRingElem}, Int), ap, i)
    _num_setcoeff!(r, i, u)
  end
  return r
end

@doc raw"""
    modular_proj(a::Generic.Poly{AbsSimpleNumFieldElem}, me::modular_env) -> Array

Apply the \code{modular_proj} function to each coefficient of $a$.
Computes an array of polynomials over the respective residue class fields.
"""
function modular_proj(a::Generic.Poly{AbsSimpleNumFieldElem}, me::modular_env)

  if !isdefined(me, :fldx)
    me.fldx = [polynomial_ring(x, "_x", cached=false)[1] for x = me.fld]
    me.Rp = Array{fqPolyRepPolyRingElem}(undef, me.ce.n)
    for i =1:me.ce.n
      me.Rp[i] = me.fldx[i](0)
    end
    me.Kx = parent(a)
  end

  for j=1:me.ce.n
    zero!(me.Rp[j])
  end
  r = me.Fpx()
  for i=0:length(a)-1
    c = coeff(a, i)
    if iszero(mod(denominator(c), me.p))
      throw(BadPrime(me.p))
    end
    Nemo.nf_elem_to_nmod_poly!(r, c, true)
    crt_inv!(me.rp, r, me.ce)
    for j=1:me.ce.n
      u = coeff(me.Rp[j], i)
      ccall((:fq_nmod_set, libflint), Nothing,
                   (Ref{fqPolyRepFieldElem}, Ref{zzModPolyRingElem}, Ref{fqPolyRepField}),
                   u, me.rp[j], me.fld[j])
      setcoeff!(me.Rp[j], i, u)
    end
  end
  return me.Rp
end

@doc raw"""
    modular_lift(a::Array{fqPolyRepPolyRingElem}, me::modular_env) -> Generic.Poly{AbsSimpleNumFieldElem}

Apply the \code{modular_lift} function to each coefficient of $a$.
Computes a polynomial over the number field.
"""
function modular_lift(a::Vector{fqPolyRepPolyRingElem}, me::modular_env)
  res = me.Kx()
  d = maximum([x.length for x = a])
  for i=0:d-1
    for j=1:me.ce.n
      ccall((:nmod_poly_set, libflint), Nothing, (Ref{zzModPolyRingElem}, Ref{fqPolyRepFieldElem}), me.rp[j], coeff(a[j], i))
    end
    ap = crt(me.rp, me.ce)
    r = coeff(res, i)
    for j=0:ap.length-1
      u = ccall((:nmod_poly_get_coeff_ui, libflint), UInt, (Ref{zzModPolyRingElem}, Int), ap, j)
      _num_setcoeff!(r, j, u)
    end
    setcoeff!(res, i, r)
  end
  return res
end

@doc raw"""
    modular_proj(a::Generic.Mat{AbsSimpleNumFieldElem}, me::modular_env) -> Array{Matrix}
    modular_proj(a::Generic.Mat{AbsSimpleNumFieldOrderElem}, me::modular_env) -> Array{Matrix}

Apply the \code{modular_proj} function to each entry of $a$.
Computes an array of matrices over the respective residue class fields.
"""
function modular_proj(a::Generic.Mat{AbsSimpleNumFieldElem}, me::modular_env)
  Mp = fqPolyRepMatrix[]
  for i=1:me.ce.n
    push!(Mp, zero_matrix(me.fld[i], nrows(a), ncols(a)))
  end
  for i=1:nrows(a)
    for j=1:ncols(a)
      im =modular_proj(a[i,j], me)
      for k=1:me.ce.n
        setindex!(Mp[k], deepcopy(im[k]), i, j)
      end
    end
  end
  return Mp
end

function modular_proj(a::Generic.Mat{AbsSimpleNumFieldOrderElem}, me::modular_env)
  Mp = []
  for i=1:me.ce.n
    push!(Mp, zero_matrix(me.fld[i], nrows(a), ncols(a)))
  end
  for i=1:nrows(a)
    for j=1:ncols(a)
      im =modular_proj(me.K(a[i,j]), me)
      for k=1:me.ce.n
        setindex!(Mp[k], deepcopy(im[k]), i, j)
      end
    end
  end
  return Mp
end
