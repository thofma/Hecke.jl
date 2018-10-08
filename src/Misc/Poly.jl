
export rational_reconstruction, farey_lift, div, valence, leading_coefficient,
       trailing_coefficient, constant_coefficient, factor_mod_pk,
       factor_mod_pk_init, hensel_lift, resultant_sircana, rres, rresx,
       coefficients

function PolynomialRing(R::Ring; cached::Bool = false)
  return PolynomialRing(R, "_x", cached = cached)
end

function PolynomialRing(R::FlintRationalField, a::Symbol; cached::Bool = true)
  Qx = FmpqPolyRing(R, a, cached)
  return Qx, gen(Qx)
end

function PolynomialRing(R::FlintIntegerRing, a::Symbol; cached::Bool = true)
  Zx = FmpzPolyRing(a, cached)
  return Zx, gen(Zx)
end

function FlintFiniteField(p::Integer)
  @assert isprime(p)
  return GF(p, cached=false)
end

function FlintFiniteField(p::fmpz)
  @assert isprime(p)
  return GF(p, cached=false)
end

function fmpz(a::Generic.Res{Nemo.fmpz})
  return a.data
end

function fmpz(a::Nemo.nmod)
  return fmpz(a.data)
end

function lift(::FlintIntegerRing, a::Generic.Res{Nemo.fmpz})
  return a.data
end

function (::FlintIntegerRing)(a::Generic.Res{Nemo.fmpz})
  return a.data
end

function lift(::FlintIntegerRing, a::Nemo.nmod)
  return fmpz(a.data)
end

function (::FlintIntegerRing)(a::Nemo.nmod)
  return fmpz(a.data)
end

function div(f::PolyElem, g::PolyElem)
  q,r = divrem(f,g)
  return q
end

function ismonic(a::PolyElem)
  return isone(lead(a))
end

@doc Markdown.doc"""
***
  valence(f::PolyElem) -> RingElem

>  The last non-zero coefficient of f
"""
function valence(f::PolyElem)
  for i=0:degree(f)
    c = coeff(f, i)
    if !iszero(c)
      return c
    end
  end
  return c
end

@doc Markdown.doc"""
***
  leading_coefficient(f::PolyElem) -> RingElem

>  The last leading coefficient of f.
"""
leading_coefficient(f::PolyElem) = lead(f)

@doc Markdown.doc"""
***
  trailing_coefficient(f::PolyElem) -> RingElem
  constant_coefficient(f::PolyElem) -> RingElem

>  The constant coefficient of f.
"""
function trailing_coefficient(f::PolyElem)
  if iszero(f)
    return base_ring(f)(0)
  end
  return coeff(f, 0)
end

@doc Markdown.doc"""
    induce_rational_reconstruction(a::fmpz_poly, M::fmpz) -> fmpq_poly
> Apply {{{rational_reconstruction}}} to each coefficient of $a$, resulting
> in either a fail (return (false, s.th.)) or (true, g) for some rational
> polynomial $g$ s.th. $g \equiv a \bmod M$.
"""
function induce_rational_reconstruction(a::fmpz_poly, M::fmpz) 
  b = PolynomialRing(FlintQQ, parent(a).S)[1]()
  for i=0:degree(a)
    fl, x,y = rational_reconstruction(coeff(a, i), M)
    if fl
      setcoeff!(b, i, x//y)
    else
      return false, b
    end
  end
  return true, b
end


constant_coefficient = trailing_coefficient

function resultant(f::fmpz_poly, g::fmpz_poly, d::fmpz, nb::Int)
  z = fmpz()
  ccall((:fmpz_poly_resultant_modular_div, :libflint), Nothing, 
     (Ref{fmpz}, Ref{fmpz_poly}, Ref{fmpz_poly}, Ref{fmpz}, Int), 
     z, f, g, d, nb)
  return z
end

##############################################################
#
# Hensel
#
##############################################################
#cannot use Ref here, has to be Ptr as the underlying stuff is
#not Julia allocated (but flint)
mutable struct fmpz_poly_raw  ## fmpz_poly without parent like in c
  coeffs::Ptr{Nothing}
  alloc::Int
  length::Int

  function fmpz_poly_raw()
    error("should not get called")
    z = new()
    ccall((:fmpz_poly_init, :libflint), Nothing, (Ref{fmpz_poly},), z)
    finalizer(_fmpz_poly_raw_clear_fn, z)
    return z
  end
end

function _fmpz_poly_raw_clear_fn(a::fmpz_poly)
  ccall((:fmpz_poly_clear, :libflint), Nothing, (Ref{fmpz_poly},), a)
end


mutable struct fmpz_poly_factor
  c::Int   # really an fmpz  - but there is no fmpz_raw to be flint compatible
  poly::Ptr{fmpz_poly_raw}
  exp::Ptr{Int} 
  _num::Int
  _alloc::Int
    
  function fmpz_poly_factor()
    z = new()
    ccall((:fmpz_poly_factor_init, :libflint), Nothing,
            (Ref{fmpz_poly_factor}, ), z)
    finalizer(_fmpz_poly_factor_clear_fn, z)
    return z
  end
end

function _fmpz_poly_factor_clear_fn(a::fmpz_poly_factor)
  ccall((:fmpz_poly_factor_clear, :libflint), Nothing,
          (Ref{fmpz_poly_factor}, ), a)
end
 
function factor_to_dict(a::fmpz_poly_factor)
  res = Dict{fmpz_poly,Int}()
  Zx,x = PolynomialRing(FlintZZ, "x")
  for i in 1:a._num
    f = Zx()
    ccall((:fmpz_poly_set, :libflint), Nothing, (Ref{fmpz_poly}, Ref{fmpz_poly_raw}), f, a.poly+(i-1)*sizeof(fmpz_poly_raw))
    res[f] = unsafe_load(a.exp, i)
  end  
  return res
end

function show(io::IO, a::fmpz_poly_factor)
  ccall((:fmpz_poly_factor_print, :libflint), Nothing, (Ref{fmpz_poly_factor}, ), a)
end

mutable struct HenselCtx
  f::fmpz_poly
  p::UInt

  LF :: fmpz_poly_factor
  link::Ptr{Int}
  v::Ptr{fmpz_poly_raw}
  w::Ptr{fmpz_poly_raw}
  N::UInt
  prev::UInt
  r::Int  #for the cleanup
  lf:: Nemo.nmod_poly_factor

  function HenselCtx(f::fmpz_poly, p::fmpz)
    a = new()
    a.f = f
    a.p = UInt(p)
    Zx,x = PolynomialRing(FlintZZ, "x", cached=false)
    Rx,x = PolynomialRing(GF(UInt(p), cached=false), "x", cached=false)
    a.lf = Nemo.nmod_poly_factor(UInt(p))
    ccall((:nmod_poly_factor, :libflint), UInt,
          (Ref{Nemo.nmod_poly_factor}, Ref{gfp_poly}), (a.lf), Rx(f))
    r = a.lf.num
    a.r = r  
    a.LF = fmpz_poly_factor()
    @assert r > 1  #flint restriction
    a.v = ccall((:flint_malloc, :libflint), Ptr{fmpz_poly_raw}, (Int, ), (2*r-2)*sizeof(fmpz_poly_raw))
    a.w = ccall((:flint_malloc, :libflint), Ptr{fmpz_poly_raw}, (Int, ), (2*r-2)*sizeof(fmpz_poly_raw))
    for i=1:(2*r-2)
      ccall((:fmpz_poly_init, :libflint), Nothing, (Ptr{fmpz_poly_raw}, ), a.v+(i-1)*sizeof(fmpz_poly_raw))
      ccall((:fmpz_poly_init, :libflint), Nothing, (Ptr{fmpz_poly_raw}, ), a.w+(i-1)*sizeof(fmpz_poly_raw))
    end
    a.link = ccall((:flint_calloc, :libflint), Ptr{Int}, (Int, Int), 2*r-2, sizeof(Int))
    a.N = 0
    a.prev = 0
    finalizer(HenselCtx_free, a)
    return a
  end

  function free_fmpz_poly_array(p::Ref{fmpz_poly_raw}, r::Int)
    for i=1:(2*r-2)
      ccall((:fmpz_poly_clear, :libflint), Nothing, (Ref{fmpz_poly_raw}, ), p+(i-1)*sizeof(fmpz_poly_raw))
    end
    ccall((:flint_free, :libflint), Nothing, (Ref{fmpz_poly_raw}, ), p)
  end
  function free_int_array(a::Ref{Int})
    ccall((:flint_free, :libflint), Nothing, (Ref{Int}, ), a)
  end
  function HenselCtx_free(a::HenselCtx)
    free_fmpz_poly_array(a.v, a.r)
    free_fmpz_poly_array(a.w, a.r)
    free_int_array(a.link)
  end
end

function show(io::IO, a::HenselCtx)
  println("factorisation of $(a.f) modulo $(a.p)^$(a.N)")
  if a.N > 0
    d = factor_to_dict(a.LF)
    println("currently: $d")
  end
end

function start_lift(a::HenselCtx, N::Int)
  a.prev = ccall((:_fmpz_poly_hensel_start_lift, :libflint), UInt, 
       (Ref{fmpz_poly_factor}, Ref{Int}, Ref{fmpz_poly_raw}, Ref{fmpz_poly_raw}, Ref{fmpz_poly}, Ref{Nemo.nmod_poly_factor}, Int),
       a.LF, a.link, a.v, a.w, a.f, a.lf, N)
  a.N = N
end

function continue_lift(a::HenselCtx, N::Int)
  a.prev = ccall((:_fmpz_poly_hensel_continue_lift, :libflint), Int, 
       (Ref{fmpz_poly_factor}, Ref{Int}, Ref{fmpz_poly_raw}, Ref{fmpz_poly_raw}, Ref{fmpz_poly}, UInt, UInt, Int, Ref{fmpz}),
       a.LF, a.link, a.v, a.w, a.f, a.prev, a.N, N, fmpz(a.p))
  a.N = N
end

@doc Markdown.doc"""
***
  factor_mod_pk(f::fmpz_poly, p::Int, k::Int) -> Dict{fmpz_poly, Int}

>  For f that is square-free modulo p, return the factorisation modulo p^k.
"""
function factor_mod_pk(f::fmpz_poly, p::Int, k::Int)
  H = HenselCtx(f, fmpz(p))
  start_lift(H, k)
  return factor_to_dict(H.LF)
end

@doc Markdown.doc"""
***
  factor_mod_pk_init(f::fmpz_poly, p::Int) -> HenselCtx

>  For f that is square-free modulo p, return a structure that allows to compute
>  the factorisaion modulo p^k for any k
"""
function factor_mod_pk_init(f::fmpz_poly, p::Int)
  H = HenselCtx(f, fmpz(p))
  return H
end

@doc Markdown.doc"""
***
  factor_mod_pk(H::HenselCtx, k::Int) -> RingElem

>  Using the result of factor_mod_pk_init, return a factorisation modulo p^k
"""
function factor_mod_pk(H::HenselCtx, k::Int)
  @assert k>= H.N
  if H.N == 0
    start_lift(H, k)
  else
    continue_lift(H, k)
  end
  return factor_to_dict(H.LF)
end

#I think, experimentally, that p = Q^i, p1 = Q^j and j<= i is the condition to make it tick.
function hensel_lift!(G::fmpz_poly, H::fmpz_poly, A::fmpz_poly, B::fmpz_poly, f::fmpz_poly, g::fmpz_poly, h::fmpz_poly, a::fmpz_poly, b::fmpz_poly, p::fmpz, p1::fmpz)
  ccall((:fmpz_poly_hensel_lift, :libflint), Nothing, (Ref{fmpz_poly}, Ref{fmpz_poly},  Ref{fmpz_poly},  Ref{fmpz_poly},  Ref{fmpz_poly},  Ref{fmpz_poly},  Ref{fmpz_poly}, Ref{fmpz_poly}, Ref{fmpz_poly}, Ref{fmpz}, Ref{fmpz}), G, H, A, B, f, g, h, a, b, p, p1)
end

@doc Markdown.doc"""
***
  hensel_lift(f::fmpz_poly, g::fmpz_poly, h::fmpz_poly, p::fmpz, k::Int) -> (fmpz_poly, fmpz_poly)

>  Given f = gh modulo p for g, h coprime modulo p, compute G, H s.th. f = GH mod p^k and
>  G = g mod p, H = h mod p.
"""
function hensel_lift(f::fmpz_poly, g::fmpz_poly, h::fmpz_poly, p::fmpz, k::Int)
  Rx, x = PolynomialRing(GF(p, cached=false), cached=false)
  fl, a, b = gcdx(Rx(g), Rx(h))
  @assert isone(fl)
  @assert k>= 2
  ## if one of the cofactors is zero, this crashes.
  ## this can only happen if one of the factors is one. In this case, the other
  ## is essentially f and f would be a legal answer. Probably reduced mod p^k
  ## with all non-negative coefficients
  ## for now:
  @assert !iszero(a) && !iszero(b)
  a = lift(parent(g), a)
  b = lift(parent(g), b)
  G = parent(g)()
  H = parent(g)()
  A = parent(g)()
  B = parent(g)()
  g = deepcopy(g)
  h = deepcopy(h)

  # the idea is to have a good chain of approximations, ie.
  # to reach p^10, one should do p, p^2, p^3, p^5, p^10
  # rather than p, p^2, p^4, p^8, p^10
  # the chain has the same length, but smaller entries.
  l = [k]
  while k>1
    k = div(k+1, 2)
    push!(l, k)
  end
  ll = []
  for i=length(l)-1:-1:1
    push!(ll, l[i] - l[i+1])
  end
  P = p
  for i in ll
    p1 = p^i
    hensel_lift!(G, H, A, B, f, g, h, a, b, P, p1)
    G, g = g, G
    H, h = h, H
    A, a = a, A
    B, b = b, B
    P *= p1
  end
  return g, h
end  

@doc Markdown.doc"""
***
  hensel_lift(f::fmpz_poly, g::fmpz_poly, p::fmpz, k::Int) -> (fmpz_poly, fmpz_poly)

>  Given f and g such that g is a divisor of f mod p and g and f/g are coprime, compute a hensel lift of g modulo p^k.
"""
function hensel_lift(f::fmpz_poly, g::fmpz_poly, p::fmpz, k::Int)
  Rx, x = PolynomialRing(GF(p, cached=false), cached=false)
  h = lift(parent(f), div(Rx(f), Rx(g)))
  return hensel_lift(f, g, h, p, k)[1]
end  
  

function fmpq_poly_to_nmod_poly_raw!(r::nmod_poly, a::fmpq_poly)
  ccall((:_fmpz_vec_get_nmod_poly, :libhecke), Nothing, (Ref{nmod_poly}, Ref{Int}, Int), r, a.coeffs, a.length)
  p = r.mod_n
  den = ccall((:fmpz_fdiv_ui, :libflint), UInt, (Ref{Int}, UInt), a.den, p)
  if den != UInt(1)
    den = ccall((:n_invmod, :libflint), UInt, (UInt, UInt), den, p)
    mul!(r, r, den)
  end
end

function fmpq_poly_to_gfp_poly_raw!(r::gfp_poly, a::fmpq_poly)
  ccall((:_fmpz_vec_get_nmod_poly, :libhecke), Nothing, (Ref{gfp_poly}, Ref{Int}, Int), r, a.coeffs, a.length)
  p = r.mod_n
  den = ccall((:fmpz_fdiv_ui, :libflint), UInt, (Ref{Int}, UInt), a.den, p)
  if den != UInt(1)
    den = ccall((:n_invmod, :libflint), UInt, (UInt, UInt), den, p)
    mul!(r, r, den)
  end
end

function fmpq_poly_to_fmpz_mod_poly_raw!(r::fmpz_mod_poly, a::fmpq_poly, t1::fmpz_poly = fmpz_poly(), t2::fmpz = fmpz())
  ccall((:fmpq_poly_get_numerator, :libflint), Nothing, (Ref{fmpz_poly}, Ref{fmpq_poly}), t1, a)
  ccall((:fmpz_mod_poly_set_fmpz_poly, :libflint), Nothing, (Ref{fmpz_mod_poly}, Ref{fmpz_poly}), r, t1)
  ccall((:fmpq_poly_get_denominator, :libflint), Nothing, (Ref{fmpz}, Ref{fmpq_poly}), t2, a)
  if !isone(t2)
    res = ccall((:fmpz_invmod, :libflint), Cint, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), t2, t2, base_ring(r).modulus)
    @assert res != 0
    ccall((:fmpz_mod_poly_scalar_mul_fmpz, :libflint), Nothing, (Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}, Ref{fmpz}), r, r, t2)
  end
end

function fmpq_poly_to_gfp_fmpz_poly_raw!(r::gfp_fmpz_poly, a::fmpq_poly, t1::fmpz_poly = fmpz_poly(), t2::fmpz = fmpz())
  ccall((:fmpq_poly_get_numerator, :libflint), Nothing, (Ref{fmpz_poly}, Ref{fmpq_poly}), t1, a)
  ccall((:fmpz_mod_poly_set_fmpz_poly, :libflint), Nothing, (Ref{gfp_fmpz_poly}, Ref{fmpz_poly}), r, t1)
  ccall((:fmpq_poly_get_denominator, :libflint), Nothing, (Ref{fmpz}, Ref{fmpq_poly}), t2, a)
  if !isone(t2)
    res = ccall((:fmpz_invmod, :libflint), Cint, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), t2, t2, base_ring(r).modulus)
    @assert res != 0
    ccall((:fmpz_mod_poly_scalar_mul_fmpz, :libflint), Nothing, (Ref{gfp_fmpz_poly}, Ref{gfp_fmpz_poly}, Ref{fmpz}), r, r, t2)
  end
end

function fmpq_poly_to_nmod_poly(Rx::Nemo.NmodPolyRing, f::fmpq_poly)
  g = Rx()
  fmpq_poly_to_nmod_poly_raw!(g, f)
  return g
end

function fmpq_poly_to_gfp_poly(Rx::Nemo.GFPPolyRing, f::fmpq_poly)
  g = Rx()
  fmpq_poly_to_gfp_poly_raw!(g, f)
  return g
end

function fmpz_poly_to_nmod_poly_raw!(r::nmod_poly, a::fmpz_poly)
  ccall((:fmpz_poly_get_nmod_poly, :libflint), Nothing,
                  (Ref{nmod_poly}, Ref{fmpz_poly}), r, a)

end

function fmpz_poly_to_gfp_poly_raw!(r::gfp_poly, a::fmpz_poly)
  ccall((:fmpz_poly_get_nmod_poly, :libflint), Nothing,
                  (Ref{gfp_poly}, Ref{fmpz_poly}), r, a)

end

function fmpz_poly_to_nmod_poly(Rx::Nemo.NmodPolyRing, f::fmpz_poly)
  g = Rx()
  fmpz_poly_to_nmod_poly_raw!(g, f)
  return g
end

function fmpq_poly_to_fmpz_mod_poly(Rx::Nemo.FmpzModPolyRing, f::fmpq_poly)
  g = Rx()
  fmpq_poly_to_fmpz_mod_poly_raw!(g, f)
  return g
end

function fmpq_poly_to_gfp_fmpz_poly(Rx::Nemo.GFPFmpzPolyRing, f::fmpq_poly)
  g = Rx()
  fmpq_poly_to_gfp_fmpz_poly_raw!(g, f)
  return g
end

function fmpz_poly_to_fmpz_mod_poly_raw!(r::fmpz_mod_poly, a::fmpz_poly)
  ccall((:fmpz_poly_get_fmpz_mod_poly, :libflint), Nothing,
                  (Ref{fmpz_mod_poly}, Ref{fmpz_poly}), r, a)

end

function fmpz_poly_to_fmpz_mod_poly(Rx::Nemo.FmpzModPolyRing, f::fmpz_poly)
  g = Rx()
  fmpz_poly_to_fmpz_mod_poly_raw!(g, f)
  return g
end


@doc Markdown.doc"""
    deflate(f::PolyElem, n::Int64) -> PolyElem
> Given a polynomial $f$ in $x^n$, write it as a polynomial in $x$, ie. divide
> all exponents by $n$.
"""
function deflate(x::PolyElem, n::Int64)
  y = parent(x)()
  for i=0:div(degree(x), n)
    setcoeff!(y, i, coeff(x, n*i))
  end
  return y
end

@doc Markdown.doc"""
    inflate(f::PolyElem, n::Int64) -> PolyElem
> Given a polynomial $f$ in $x$, return $f(x^n)$, ie. multiply 
> all exponents by $n$.
"""
function inflate(x::PolyElem, n::Int64)
  y = parent(x)()
  for i=0:degree(x)
    setcoeff!(y, n*i, coeff(x, i))
  end
  return y
end

@doc Markdown.doc"""
    deflate(x::PolyElem) -> PolyElem
> Deflate the polynomial $f$ maximally, ie. find the largest $n$ s.th.
> $f$ can be deflated by $n$, ie. $f$ is actually a polynomial in $x^n$.
"""
function deflate(x::PolyElem)
  g = 0
  for i=0:degree(x)
    if coeff(x, i) != 0
      g = gcd(g, i)
      if g==1
        return x, 1
      end
    end
  end
  return deflate(x, g), g
end

function _hensel(f::PolyElem{T}, g::PolyElem{T}, h::PolyElem{T}, s::PolyElem{T}, t::PolyElem{T}) where T <: RingElem #from von zur Gathen: h needs to be monic
  @assert ismonic(h)
#  @assert isnilpotent(content(f-g*h))  #this guarantees useful lifting
#  @assert isnilpotent(content(g*s+h*t-1))
  e = f-g*h 
  q, r = divrem(s*e, h)
#  @assert s*e == q*h+r
  g = g+t*e+q*g
  h = h+r
  @assert ismonic(h)
  b = s*g+t*h-1
  c, d = divrem(s*b, h)
#  @assert s*b == c*h+d
  s = s-d
  t = t-t*b-c*g

  return g, h, s, t
end

#factors f as unit * monic 
#seems to not like 3*x^2+3*x+1 mod 108! mod 27 it is fine.
# requires some coefficient of f to be a unit
function fun_factor(f::PolyElem{<:RingElem})
  local g0
  local h0
  if isunit(lead(f))
    l= lead(f)
    return parent(f)(l), f*inv(l)
  end
  if isunit(f)
    return f, parent(f)(1)
  end
  t = gen(parent(f))
  g0 = parent(f)(0)
  for i=degree(f):-1:0
    if isunit(coeff(f, i))
      h0 = f - g0
      break
    else
      setcoeff!(g0, i, deepcopy(coeff(f, i)))
    end
  end

  #co-factors:
  g0 = parent(f)(0)
  setcoeff!(g0, degree(f) - degree(h0), lead(f))
  setcoeff!(g0, 0, lead(h0))
  s = parent(f)(inv(lead(h0)))
  h0 *= lead(s)
  t = parent(f)(0)
  g, h, s, t = _hensel(f, g0, h0, s, t)
  i = 1
  while g!= g0 || h != h0
#      @show content(g*s-t*h-1)
    i += 1
    g0 = g
    h0 = h
    g, h, s, t = _hensel(f, g0, h0, s, t)
    if i>20 #in general: loop forever... one could check that the
      # contents of f-gh and s*g+t*h - 1 is nilpotent.
      # this SHOULD ensure convergence
      @show f
      @show parent(f)
      @show g, h, s, t
      @show content(f-g*h)
      @show content(g*s-t*h-1)
      error("too long")
    end
  end

  return g0, h0
end

@doc Markdown.doc"""
    Base.rand(Rt::PolyRing{T}, n::Int) where T <: ResElem{S} where S <: Union{fmpz, Integer} -> PolElem{T}
> Find a random polynomial of degree(n)
"""
function Base.rand(Rt::PolyRing{T}, n::Int) where T <: ResElem{S} where S <: Union{fmpz, Integer}
  f = Rt()
  R = base_ring(Rt)
  for i=0:n
    setcoeff!(f, i, rand(R))
  end
  return f
end

@doc Markdown.doc"""
    gcd_sircana(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer} -> T
> The 'gcd' of $f$ anf $g$ using a quadratic-time algorithm.
"""
function gcd_sircana(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer}
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  Rt = parent(f)
  R = base_ring(Rt)
  m = fmpz(modulus(R))
  e, p = ispower(m)
  easy = isprime(p)
  @assert easy #for now...

  while !iszero(g)
    @show cg = content(g)
    if !isunit(cg)
      for i=0:degree(g)
        setcoeff!(g, i, divexact(coeff(g, i), cg))
      end
    end
    if !isunit(lead(g))
      u, g = fun_factor(g)
    end
    @show f, g = g, (f%g)
  end
  c = canonical_unit(lead(f))
  f = divexact(f, c)
  return f
end


@doc Markdown.doc"""
    resultant_sircana(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer} -> T
> The resultant of $f$ anf $g$ using a quadratic-time algorithm.
"""
function resultant_sircana(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer}
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  Rt = parent(f)
  R = base_ring(Rt)
  m = fmpz(modulus(R))
  e, p = ispower(m)
  easy = isprime(p)

  Zx = PolynomialRing(FlintZZ)[1]

  res = R(1)

  while true
    if degree(f) < 1 && degree(g) < 1
      if iszero(f) || iszero(g)
        res *= R(0)
      else
        res *= R(1)
      end
      return res
    end

    if degree(f) < 1
      res *= lead(f)^degree(g)
      return res
    end

    if degree(g) < 1
      res *= lead(g)^degree(f)
      return res
    end

    c, f = primsplit(f)
    if !isone(c)
      res *= c^degree(g)
    end

    c, g = primsplit(g)
    if !isone(c)
      res *= c^degree(f)
    end

    if degree(f) < degree(g)
      res *= (-1)^(degree(f)*degree(g))
      f, g = g, f
    end

    #want f % g which works iff lead(g) | lead(f)

    if isunit(lead(g)) #accelerate a bit...possibly.
      q, r = divrem(f, g)
      res *= lead(g)^(degree(f) - degree(r))
      res *= R(-1)^(degree(g)*(degree(f) - degree(r)))
      f = r
      continue
    end

    if gcd(lift(lead(f)), m)  % gcd(lift(lead(g)), m) == 0
      q = divexact(lead(f), lead(g))
      ff = f - q*g*gen(Rt)^(degree(f) - degree(g))
      @assert degree(f) > degree(ff)
      res *= lead(g)^(degree(f) - degree(ff))
      res *= R(-1)^(degree(g)*(degree(f) - degree(ff)))
      f = ff
      continue
    end
    break
  end

  #factoring case, need to split the ring as well.
  #merde : we need a coprime factorisation: take
  # 6t^2+2t+3 mod 36....
  if easy
    cp = [m]
  else
    cp = [gcd(lift(coeff(g, i)), m) for i=0:degree(g)]
    push!(cp, m)
    cp = [x for x = cp if !iszero(x)]
    cp = coprime_base(cp)
    cp = [x for x = cp if !isunit(x)] #error: [1, 1, 3, 27] -> [1,3]
  end
  resp = fmpz[]
  pg = fmpz[]
  for p = cp
    lg = p^valuation(m, p)
    push!(pg, lg)

    if lg != m
      R1 = ResidueRing(FlintZZ, S(lg), cached=false)
      R1t = PolynomialRing(R1, cached=false)[1]
      #g is bad in R1, so factor it
      gR1 = R1t(lift(Zx, g))
      fR1 = R1t(lift(Zx, f))
    else
      gR1 = g
      fR1 = f
      R1 = R
      R1t = Rt
    end

    if degree(fR1) < degree(f) &&
       degree(gR1) < degree(g)
       res1 = R1(0)
    elseif degree(fR1) < degree(f)
        res1 = R1(-1)^(degree(g) * (degree(f) - degree(fR1))) *
               lead(gR1)^(degree(f) - degree(fR1))
    elseif degree(gR1) < degree(g)
        res1 = lead(fR1)^(degree(g) - degree(gR1))
    else
        res1 = R1(1)
    end

    if !isunit(lead(gR1))
      g1, g2 = fun_factor(gR1)
    
      #careful: lead(g) = 0 mod lg is possible, so the degree drops!
      #from Wiki:
      # phi: R -> S
      # phi(res(f, g)) = res(phi(f), phi(g)) if the degrees are the same
      #                = 0                   if both degrees drop (zero column in 
      #                                         sylvester matrix)
      #                = (-1)^(delta(f)*deg(g))*
      #                  phi(l(g))^delta(f)  if only degree(f) drops
      #                = phi(l(f))^delta(g)  if only degree(g) drops
      #
      # we use res(f, gh) = res(f, g)res(f, h) which seems to be true in general                  
      #next: res(fR1, gR1) = res(phi(f), g1)
      #g1 is = 1 mod p
      #however, reverse(fR1) can have a smaller degree then fR1 (eg. x^2 -> 1)
      # res(f, g) = t(g)^delta(f) * (-1)^(deg(g)*delta(f)) * res(rev(f), rev(g))
      # there is a (-1)^deg(f)*deg(g) from Wiki for the reverse on top.

      res1 *= resultant_sircana(reverse(fR1), reverse(g1))
      v = valuation(fR1, gen(parent(fR1))) 
           #should be delta(f) = degree(rev(f)) - degree(f)
      res1 *= constant_coefficient(g1)^v*R1(-1)^(v*degree(g1))
      res1 *= R1(-1)^(degree(g1)*degree(fR1))

      res1 *= resultant_sircana(fR1, g2)
      push!(resp, lift(res1))
    else
      #gR1 has a invertible leading coeff
      res1 *= resultant_sircana(fR1, gR1)
      push!(resp, lift(res1))
    end
  end
  res *= length(cp)==1 ? R(resp[1]) : R(crt(resp, pg))
  return res
end


#key idea (Carlo): if g = ab and a is a unit mod p, then it is actually a unit 
# in Z/p^kZ, hence the ideal (f, g) = (f, b) where b is now monic.
#Thus rres(f,g ) = rres(f, b).... and the division can continue
@doc Markdown.doc"""
    rres(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer} -> T
> The reduced resultant of $f$ and $g$ using a quadratic-time algorithm.
> That is a generator for the $(f, g) \cap Z$
"""
function rres(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer}
  Nemo.check_parent(f, g)
  return rres_sircana(f, g)
end

@doc Markdown.doc"""
    rres(f::fmpz_poly, g::fmpz_poly) -> fmpz
> The reduced resultant of $f$ and $g$,
> that is a generator for the ideal $(f, g) \cap Z$
"""
function rres(f::fmpz_poly, g::fmpz_poly)
  return rres_bez(f,g)
end

function rres_sircana(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer}
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  Rt = parent(f)
  R = base_ring(Rt)
  m = fmpz(modulus(R))
  e, p = ispower(m)
  easy = isprime(p)

  Zx = PolynomialRing(FlintZZ)[1]

  while true
    if degree(f) < 1 && degree(g) < 1
      if iszero(f) || iszero(g)
        res = R(0)
      else
        res = R(gcd(lift(lead(f)), lift(lead(g))))
      end
      return res
    end

    if degree(f) < degree(g)
      f, g = g, f
    end

    if degree(g) < 1
      if !isunit(lead(f))
        #need the constant coeff * the annihilator of the others...
        a = coeff(f, 1)
        for i = 2:degree(f)
          a = gcd(a, coeff(f, i))
          if isone(a)
            break
          end
        end
        a = annihilator(a)
        if iszero(a)
          return lead(g)
        else
          return gcd(lead(g), a*constant_coefficient(f))
        end
      else
        return gcd(R(0), constant_coefficient(g))
      end
    end

    if !isunit(lead(g))
      c, g = primsplit(g)
      if easy
        cp = [m]
      else
        cp = [gcd(lift(coeff(g, i)), m) for i=0:degree(g)]
        push!(cp, m)
        cp = [x for x = cp if !iszero(x)]
        cp = coprime_base(cp)
        cp = [x for x = cp if !isunit(x)] #error: [1, 1, 3, 27] -> [1,3]
      end
      resp = fmpz[]
      pg = fmpz[]
      for p = cp
        lg = p^valuation(m, p)
        push!(pg, lg)

        if lg != m
          R1 = ResidueRing(FlintZZ, S(lg), cached=false)
          R1t = PolynomialRing(R1, cached=false)[1]
          #g is bad in R1, so factor it
          gR1 = R1t(lift(Zx, g))
          fR1 = R1t(lift(Zx, f))
        else
          gR1 = g
          fR1 = f
          R1 = R
          R1t = Rt
        end
        if isunit(lead(gR1))
          g2 = gR1
        else
          g1, g2 = fun_factor(gR1)
        end
        push!(resp, lift(lift(c)*rres_sircana(fR1, g2)))
      end
      res = length(cp)==1 ? R(resp[1]) : R(crt(resp, pg))
      return gcd(R(0), res)
    end

    q, f = divrem(f, g)
  end
end

@doc Markdown.doc"""
    rresx(f::PolyElem{ResElem{fmpz}}, g::PolyElem{ResElem{fmpz}}) -> r, u, v
> The reduced resultant $r$ and polynomials $u$ and $v$ s.th.
> $r = uf+vg$ and $\langle r\rangle = \langle f, g\rangle\cap \mathbb Z$.
"""
function rresx(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer}
  Nemo.check_parent(f, g)
  return rresx_sircana(f, g)
end

function rresx_sircana(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer}
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  @assert isunit(lead(f)) || isunit(lead(g)) #can be weakened to invertable lead
  res::T, u::PolyElem{T}, v::PolyElem{T} = _rresx_sircana(f, g)::Tuple{T, PolyElem{T}, PolyElem{T}}
  if !iszero(res)
    cu = canonical_unit(res)
    cu = inv(cu)
    res *= cu
    u *= cu
    v *= cu
  end
  if isunit(lead(g))
    q::PolyElem{T}, r::PolyElem{T} = divrem(u, g)
    return res, r, v+q*f
  else
    q, r = divrem(v, f)
    return res, u+q*g, r
  end
end

function _rresx_sircana(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer}
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)

  Rt = parent(f)
  R = base_ring(Rt)
  Zx = FlintZZ["x"][1]
  m::fmpz = fmpz(modulus(R))
  e, p::fmpz = ispower(m)
  easy = isprime(p)

  u::PolyElem{T}, v::PolyElem{T} = Rt(0), Rt(1)
  U::PolyElem{T}, V::PolyElem{T} = Rt(1), Rt(0)
#  res::T, uu::T, vv::T

#  u, v = Rt(0), Rt(1)  #g = u f_in + v g_in
#  U, V = Rt(1), Rt(0)  #f = U f_in + V g_in


  Zx = PolynomialRing(FlintZZ)[1]

  while true
    if degree(f) < 1 && degree(g) < 1
      if iszero(f) || iszero(g)
        res = R(0)
        u = Rt(0)
        v = Rt(0)
      else
        res, uu, vv = gcdx(lead(f), lead(g)) 
        #res = uu*f + vv*g = uu*(U f_in + V g_in) + vv*(u f_in + v g_in)
        #    = uu*U + vv*u  uu*V + vv*v
        u, v = (uu*U + vv*u), (uu*V + vv*v)
      end
      return res, u, v
    end

    if degree(f) < degree(g)
      f, g = g, f
      U, u = u, U
      V, v = v, V
    end

    if degree(g) < 1
      if !isunit(lead(f))
        #need the constant coeff * the annihilator of the others...
        a = coeff(f, 1)
        for i = 2:degree(f)
          a = gcd(a, coeff(f, i))
          if isone(a)
            break
          end
        end
        a = annihilator(a)
        if iszero(a)
          return lead(g), u, v
        else
          res, uu, vv = gcdx(a*constant_coefficient(f), lead(g))
          u, v = (uu*a*U + vv*u), (uu*a*V + vv*v)

          return res, u, v
        end
      else
        return constant_coefficient(g), u, v
      end
    end

    if !isunit(lead(g))
      c, g = primsplit(g)
      if easy
        cp = [m]
      else
        cp = [gcd(lift(coeff(g, i)), m) for i=0:degree(g)]
        push!(cp, m)
        cp = [x for x = cp if !iszero(x)]
        cp = coprime_base(cp)
        cp = [x for x = cp if !isunit(x)] #error: [1, 1, 3, 27] -> [1,3]
      end
      resp = fmpz[]
      resB = []
      pg = fmpz[]
      for p = cp
        lg = p^valuation(m, p)
        push!(pg, lg)

        #gR1::PolyElem{T}, fR1::PolyElem{T}
        #c::T
        #g1::PolyElem{T}, g2::PolyElem{T}
        if lg != m
          R1 = ResidueRing(FlintZZ, S(lg), cached=false)
          R1t = PolynomialRing(R1, cached=false)[1]
          #g is bad in R1, so factor it
          gR1 = R1t(lift(Zx, g))
          fR1 = R1t(lift(Zx, f))
        else
          gR1 = g
          fR1 = f
          R1 = R
          R1t = Rt
        end
        if iszero(R1(lift(c)))
          push!(resp, fmpz(0))
          push!(resB, (R1t(0), R1t(1))) #relation need to be primitive
        else
          if isunit(lead(gR1))
            g2 = gR1
            g1 = R1t(1)
          else
            g1, g2 = fun_factor(gR1)
          end
          @assert isunit(g1)
          rr, uu, vv = rresx_sircana(fR1, g2)
          push!(resp, lift(lift(c)*rr))
          push!(resB, (uu*lift(c), inv(g1)*vv))
        end
      end
      if length(cp) == 1
        res, u_, v_ = R(resp[1]), Rt(resB[1][1]), Rt(resB[1][2])
      else
        ce = crt_env(pg)
        res = R(crt(resp, ce))
        u_ = Rt(induce_crt([x[1] for x = resB], ce))
        v_ = Rt(induce_crt([x[2] for x = resB], ce))
      end
      # f = U*f_in + V*g_in
      # g = u*f_in + v*g_in
      # r = u_ * f + v_ * g 

      (u_*U + v_*u), (u_*V + v_*v)
      return res, (u_*U + v_*u), (u_*V + v_*v)
    end

    q, f = divrem(f, g)
    #f -> f-qg, so U*f_in + V * g_in -> ...
    U = U - q*u
    V = V - q*v
  end
end

function my_divrem(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer}
  g1, g2 = fun_factor(g)
  if degree(g2) < 1 # g2 is monic, so it's 1
    return parent(f)(0), g2
  end
  u = invmod(g1, g2)
  q, r = divrem(f, g2)
  q, r = divrem(r*u, g2)
  return g1*r, g2
end  

#polynomial remainder sequence - almost
function prs_sircana(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer}
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  Rt = parent(f)
  R = base_ring(Rt)
  m = fmpz(modulus(R))
  e, p = ispower(m)
  easy = isprime(p)
  @assert easy

  Zx = PolynomialRing(FlintZZ)[1]

  rs = []

  while degree(g) >0
    g *= inv(canonical_unit(lead(g)))
    c, gg = primsplit(g)
    @show f, (g, mu) = gg, my_divrem(f, gg)
    push!(rs, (c, gg, mu))
  end
  return rs, g
end



function Nemo.gcd(a::ResElem{T}, b::ResElem{T}) where T <: Union{Integer, fmpz}
  m = modulus(a)
  return parent(a)(gcd(gcd(a.data, m), b.data))
end

function Nemo.gcdx(a::ResElem{T}, b::ResElem{T}) where T <: Union{Integer, fmpz}
  m = modulus(a)
  R = parent(a)
  g, u, v = gcdx(fmpz(a.data), fmpz(b.data))
  G, U, V = gcdx(g, fmpz(m))
  return R(G), R(U)*R(u), R(U)*R(v)
end

@doc Markdown.doc"""
    annihilator(a::ResElem{fmpz}) -> r
    annihilator(a::ResElem{Integer}) -> r
> The annihilator of $a$, ie. a generator for the annihilator ideal
> $\{x | xa = 0\} = \langle r\rangle$
"""
function annihilator(a::ResElem{T}) where T <: Union{Integer, fmpz}
  R = parent(a)
  m = modulus(R)
  return R(divexact(m, gcd(m, a.data)))
end

@doc Markdown.doc"""
    isunit(f::Union{fmpz_mod_poly,nmod_poly}) -> Bool
> Tests if $f$ is a unit in the polynomial ring, ie. if 
> $f = u + n$ where $u$ is a unit in the coeff. ring
> and $n$ is nilpotent.
"""
function Nemo.isunit(f::Union{fmpz_mod_poly,nmod_poly}) 
  if !isunit(constant_coefficient(f))
    return false
  end
  for i=1:degree(f)
    if !isnilpotent(coeff(f, i))
      return false
    end
  end
  return true
end

@doc Markdown.doc"""
    isnilpotent(a::ResElem{fmpz}) -> Bool
    isnilpotent(a::ResElem{Integer}) -> Bool
> Tests iff $a$ is nilpotent.
"""
function isnilpotent(a::ResElem{T}) where T <: Union{Integer, fmpz}
  #a is nilpontent if it is divisible by all primes divising the modulus
  # the largest exponent a prime can divide is nbits(m)
  l = nbits(modulus(a))
  return iszero(a^l)
end

function iszerodivisor(f::Union{fmpz_mod_poly,nmod_poly})
  c = content(f)
  return isnilpotent(c)
end

function Nemo.inv(f::Union{fmpz_mod_poly,nmod_poly}) 
  if !isunit(f)
    error("impossible inverse")
  end
  g = parent(f)(inv(trailing_coefficient(f)))
  #lifting: to invert a, start with an inverse b mod m, then
  # then b -> b*(2-ab) is an inverse mod m^2
  # starting with this g, and using the fact that all coeffs are nilpotent
  # we have an invers modulo s.th. nilpotent. Hence it works
  c = f*g
  while !isone(c)
    g = g*(2-c)
    c = f*g
  end
  return g
end

function Nemo.invmod(f::T, M::T) where T <: Union{fmpz_mod_poly}
  if !isunit(f)
    error("impossible inverse")
  end
  if !isunit(lead(M))
    error("modulus must be monic")
  end
  g = parent(f)(inv(trailing_coefficient(f)))
  #lifting: to invert a, start with an inverse b mod m, then
  # then b -> b*(2-ab) is an inverse mod m^2
  # starting with this g, and using the fact that all coeffs are nilpotent
  # we have an invers modulo s.th. nilpotent. Hence it works
  c = f*g
  q, c = divrem(c, M)
  while !isone(c)
    g = g*(2-c)
    q, g = divrem(g, M)
    c = f*g
    q, c = divrem(c, M)
  end
  return g
end


#for testing: the obvious(?) naive method(s)
function rres_hnf(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer}
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  R = base_ring(f)
  Zx = FlintZZ["x"][1]
  s = Nemo.Generic.sylvester_matrix(lift(Zx, f), lift(Zx, g))
  h = hnf(s)
  return gcd(R(0), R(h[rows(h), cols(h)]))
end

function rres_bez(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer}
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  R = base_ring(f)
  Zx = FlintZZ["x"][1]
  Qx = FlintQQ["x"][1]
  g, q, w = gcdx(Qx(lift(Zx, f)), Qx(lift(Zx, g)))
  return gcd(R(0), R(lcm(denominator(q), denominator(w))))
end

function rres_hnf(f::fmpz_poly, g::fmpz_poly)
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  s = Nemo.Generic.sylvester_matrix(f, g)
  h = hnf(s)
  return abs(h[rows(h), cols(h)])
end

function rres_bez(f::fmpz_poly, g::fmpz_poly)
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  Qx = FlintQQ["x"][1]
  g, q, w = gcdx(Qx(f), Qx(g))
  return lcm(denominator(q), denominator(w))
end

@doc Markdown.doc"""
    rresx(f::fmpz_poly, g::fmpz_poly) -> r, u, v
> The reduced resultant, ie. a generator for the intersection
> of the ideal generated by $f$ and $g$ with the integers.
> As well as polynomials $u$ and $v$ s.th. $r = uf+vg$, 
> $\deg u < \deg g$ and $\deg v < \deg f$.
"""
function rresx(f::fmpz_poly, g::fmpz_poly)
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  Qx = FlintQQ["x"][1]
  g, q, w = gcdx(Qx(f), Qx(g))
  l = lcm(denominator(q), denominator(w))
  Zx = parent(f)
  return l, Zx(l*q), Zx(l*w)
end

@doc Markdown.doc"""
    xxgcd(a::ResElem{fmpz}, b::ResElem{fmpz}) -> g, e, f, u, v
    xxgcd(a::ResElem{Integer}, b::ResElem{Integer}) -> g, e, f, u, v
> Coputes $g = \gcd(a, b)$, the Bezout coefficients, $e$, $f$ s.th.
> $g = ea+fb$ and $u$, $v$ s.th. $ev-fu = 1$, $gu = a$ and $gv = b$
"""
function xxgcd(a::ResElem{S}, b::ResElem{S}) where S <: Union{fmpz, Integer}
  g, e, f = gcdx(a, b)
  if iszero(g)
    return g, e, f, f, e
  else
    return g, e, f, divexact(a, g), divexact(b, g)
  end
end

@doc Markdown.doc"""
    primsplit!(f::PolyElem{ResElem{fmpz}}) -> c, f
    primsplit!(f::PolyElem{ResElem{Integer}}) -> c, f
> Computes the contents $c$ and the primitive part of $f$ destructively.   
"""
function primsplit!(f::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer}

  d = degree(f)
  if d == 0
    if iszero(f)
      return base_ring(parent(f))(1), f
    end
    c = canonical_unit(coeff(f, 0))
    setcoeff!(f, 0, 1)
    return inv(c)*coeff(f, 0), f
  end

  g = coeff(f, 0)
  setcoeff!(f, 0, 1)
  for i=1:d
    h, _, _, u, v = xxgcd(g, coeff(f, i))
    setcoeff!(f, i, v)
    if  g != h
      for j=0:i-1
        setcoeff!(f, j, u*coeff(f, j))
      end
    end
    g = h
    if isone(g)
      return g, f
    end
  end
  return g, f
end

@doc Markdown.doc"""
    primsplit(f::PolyElem{ResElem{fmpz}}}) -> c, f
    primsplit(f::PolyElem{ResElem{Integer}}}) -> c, f
> Computes the contents $c$ and the primitive part of $f$.
"""
function primsplit(f::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer}
  g = deepcopy(f)
  return primsplit!(g)
end

struct PolyCoeffs{T <: PolyElem} 
  f::T
end  

function coefficients(f::PolyElem)
  return PolyCoeffs(f)
end

# TODO: Fix this iterator

#function Base.start(a::PolyCoeffs)
#  return 0
#end
#
#function Base.next(a::PolyCoeffs, b::Int)
#  return coeff(a.f, b), b+1
#end
#
#function Base.done(a::PolyCoeffs, b::Int)
#  return b > degree(a.f)
#end
#
#function Base.length(a::PolyCoeffs)
#  return length(a.f)
#end

function Base.lastindex(a::PolyCoeffs)
  return degree(a.f)
end

function Base.getindex(a::PolyCoeffs, i::Int)
  return coeff(a.f, i)
end


@doc Markdown.doc"""
    resultant_valuation(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer} -> T
> A generator for the ideal of the resultant of $f$ anf $g$ using a quadratic-time algorithm.
> One of the two polynomials must be monic.
"""
function resultant_ideal(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer}
  #The algorithm is the same as the resultant. We assume that one fo the 2 polynomials is monic. Under this assumption, at every
  #step the same is true and we can discard the unti obtained from the fun_factor function
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  Rt = parent(f)
  R = base_ring(Rt)
  m = fmpz(modulus(R))
  e, p::fmpz = ispower(m)
  easy = isprime(p)
  
  if easy
    return resultant_ideal_pp(f,g)
  end
  
  #Some initial checks
  res = R(1)
  if degree(f) < 1 && degree(g) < 1
    if iszero(f) || iszero(g)
      return R(0)
    end
    return res
  end
  
  if degree(f) < 1
    res *= lead(f)^degree(g)
    return res
  end

  c, f = primsplit(f)
  if !isone(c)
    res *= R(c)^degree(g)
  end

  c, g = primsplit(g)
  if !isone(c)
    res *= R(c)^degree(f)
  end
  
  if degree(f) < degree(g)
    f, g = g, f
  end
  
  if iszero(res)
    return res
  end

  
  #Now, I can safely assume that the degree of f is always greater than the degree of g
  while true
    
    if degree(g) < 1
      res *= lead(g)^degree(f)
      return res
    end
  
    c, g = primsplit(g)
    if !isone(c)
      res *= R(c)^degree(f)
    end

    if iszero(res)
      return res
    end
    #want f % g which works iff lead(g) | lead(f)

    if isunit(lead(g)) #accelerate a bit...possibly.
      f = rem(f, g)
      f, g = g, f
      continue
    end
    break
  end

  # factoring case, need to split the ring as well.
  # we need a coprime factorisation and then we go recursively
  if easy
    return resultant_valuation_pp(f, g)
  else
    #If res is not coprime to the modulus, I can continue the computations modulo a smaller one.
    s = gcd(m, lift(res))
    if !isone(s)
      m = divexact(m, s)
    end
    cp = [gcd(lift(coeff(g, i)), m) for i=0:degree(g)]
    push!(cp, m)
    cp = [x for x = cp if !iszero(x)]
    cp = coprime_base(cp)
    cp = [x for x = cp if !isunit(x)] #error: [1, 1, 3, 27] -> [1,3]
    resp = fmpz[]
    pg = fmpz[]
    for p = cp
      lg = p^valuation(m, p)
      push!(pg, lg)

      if lg != m
        R1 = ResidueRing(FlintZZ, S(lg), cached = false)
        R1t = PolynomialRing(R1, cached = false)[1]
        #g is bad in R1, so factor it
        gR1 = R1t(lift(Zx, g))
        fR1 = R1t(lift(Zx, f))
      else
        gR1 = g
        fR1 = f
        R1 = R
        R1t = Rt
      end
  
      if degree(fR1) < degree(f) && degree(gR1) < degree(g)
        res1 = R1(0)
      elseif degree(fR1) < degree(f)
        res1 = lead(gR1)^(degree(f) - degree(fR1))
      else
        res1 = R1(1)
      end
  
      if !isunit(lead(gR1))
        g1, g2 = fun_factor(gR1)
        res1 *= resultant_ideal(fR1, g2)
        push!(resp, lift(res1))
      else
        #gR1 has a invertible leading coeff
        res1 *= resultant_ideal(fR1, gR1)
        push!(resp, lift(res1))
      end
    end
    res *=  lift(R(crt(resp, pg)))
    return res
  end
end

function resultant_ideal_pp(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer}
  #The algorithm is the same as the resultant. We assume that one fo the 2 polynomials is monic. Under this assumption, at every
  #step the same is true and we can discard the unti obtained from the fun_factor function
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  Rt = parent(f)
  R = base_ring(Rt)
  pn = fmpz(R.modulus)
  
  
  #Some initial checks
  if degree(f) < 1 && degree(g) < 1
    if iszero(f) || iszero(g)
      return R(0)
    else
      return R(1)
    end
  end

  res = R(1)
  
  if degree(f) < 1
    res *= lead(f)^degree(g)
    return res
  end

  if degree(g) < 1
    res *= lead(g)^degree(f)
    return res
  end

  c, f = primsplit(f)
  if !isone(c)
    res *= R(c)^degree(g)
  end

  c, g = primsplit(g)
  if !isone(c)
    res *= R(c)^degree(f)
  end
  
  if degree(f) < degree(g)
    f, g = g, f
  end
  
  if iszero(res)
    return res
  end
  
  while true
    #want f % g which works iff lead(g) | lead(f)

    if isunit(lead(g)) #accelerate a bit...possibly.
      f = rem(f, g)
      if degree(f) < 1
        res *= lead(f)^degree(g)
        return res
      end
      c, f = primsplit(f)
      if !isone(c)
        res *= R(c)^degree(g)
      end
      f, g = g, f
    else
      s = gcd(lift(res), pn)
      if !isone(s)
        new_pn = divexact(pn, s)
        Zx = PolynomialRing(FlintZZ, "x")[1]
        R1 = ResidueRing(FlintZZ, new_pn, cached = false)
        R1t = PolynomialRing(R1, "y", cached = false)[1]
        f1 = R1t(lift(Zx,f))
        g2 = R1t(lift(Zx,g))
        g3, g2 = fun_factor(g2)
        return res*R(lift(resultant_ideal_pp(f1, g2)))
      end
      g1, g = fun_factor(g)  
      if degree(g) < 1
        return res*lead(g)^degree(f)
      end
    end
  end

end


################################################################################
#
#  fmpq_poly with denominator 1 to fmpz_poly
#
################################################################################

function (a::FmpzPolyRing)(b::fmpq_poly)
  (!isone(denominator(b))) && error("Denominator has to be 1")
  z = a()
  ccall((:fmpq_poly_get_numerator, :libflint), Nothing,
              (Ref{fmpz_poly}, Ref{fmpq_poly}), z, b)
  return z
end

################################################################################
#
#  Power sums
#
################################################################################

@doc Markdown.doc"""
    polynomial_to_power_sums(f::PolyElem{T}, n::Int=degree(f)) -> Array{T, 1}
> Uses Newton (or Newton-Girard) formulas to compute the first $n$
> power sums from the coefficients of $f$.
"""
function polynomial_to_power_sums(f::PolyElem{T}, n::Int=degree(f)) where T <: FieldElem
  d = degree(f)
  R = base_ring(f)
  S = PowerSeriesRing(R, n+1, "gen(S)")[1]
  #careful: converting to power series and derivative do not commute
  #I also don't quite get this: I thought this was just the log,
  #but it isn't
  A = S([coeff(reverse(derivative(f)), i) for i=0:d-1], d, n+1, 0)
  B = S([coeff(reverse(f), i) for i=0:d], d+1, n+1, 0)
  L = A*inv(B)
  s = [coeff(L, i) for i=1:n]
  return s
end

#plain vanilla recursion
function polynomial_to_power_sums(f::PolyElem{T}, n::Int=degree(f)) where T 
  d = degree(f)
  R = base_ring(f)
  E = T[(-1)^i*coeff(f, d-i) for i=0:min(d, n)] #should be the elementary symm.
  while length(E) <= n
    push!(E, R(0))
  end
  P = T[]

  push!(P, E[1+1])
  for k=2:n
    push!(P, (-1)^(k-1)*k*E[k+1] + sum((-1)^(k-1+i)*E[k-i+1]*P[i] for i=1:k-1))
  end
  return P
end

@doc Markdown.doc"""
    power_sums_to_polynomial(P::Array{T, 1}) -> PolyElem{T}
> Uses the Newton (or Newton-Girard) identities to obtain the polynomial
> coefficients (the elementary symmetric functions) from the power sums.
"""
function power_sums_to_polynomial(P::Array{T, 1}) where T <: FieldElem
  d = length(P)
  R = parent(P[1])
  S = PowerSeriesRing(R, d, "gen(S)")[1]
  s = S(P, length(P), d, 0)
  if !false
    r = - integral(s)
    r = exp(r)
  end

  if false
    r = S(T[R(1), -P[1]], 2, 2, 0) 
    la = [d+1]
    while la[end]>1
      push!(la, div(la[end]+1, 2))
    end
    n = length(la)-1
    while n > 0
      set_prec!(r, la[n])
      rr = derivative(r)*inv(r)
      md = -(rr+s)
      m = S([R(1)], 1, la[n], 0)+integral(md)
      r *= m
      n -= 1
    end
    println("new exp $r")
  end
  v = valuation(r)
  @assert v==0
  Rx, x = PolynomialRing(R, cached = false)
  return Rx([Nemo.polcoeff(r, d-i) for i=0:d])
end

function power_sums_to_polynomial(P::Array{T, 1}) where T
  E = T[1]
  R = parent(P[1])
  last_non_zero = 0
  for k=1:length(P)
    push!(E, divexact(sum((-1)^(i-1)*E[k-i+1]*P[i] for i=1:k), R(k)))
    if E[end] != 0
      last_non_zero = k
    end
  end
  E = E[1:last_non_zero+1]
  d = length(E) #the length of the resulting poly...
  for i=1:div(d, 2)
    E[i], E[d-i+1] = (-1)^(d-i)*E[d-i+1], (-1)^(i-1)*E[i]
  end
  return PolynomialRing(R, cached = false)[1](E)
end

##############################################################
# all of this should be in Nemo/AbstractAlgebra
#
#TODO:
# expand systematically for all finite fields
# and for fmpz/fmpq poly
# for fun: ispower(a::nf_elem)
#

function factor(f::fmpq_poly, R::NmodRing)
  Rt, t = PolynomialRing(R, "t", cached=false)
  return factor(Rt(f))
end

function factor(f::fmpq_poly, R::GaloisField)
  Rt, t = PolynomialRing(R, "t", cached=false)
  return factor(Rt(f))
end

function factor(f::fmpz_poly, R::NmodRing)
  Rt, t = PolynomialRing(R, "t", cached=false)
  return factor(Rt(f))
end

function roots(f::fmpq_poly, R::Nemo.FqNmodFiniteField)
  Rt, t = PolynomialRing(R, "t", cached=false)
  fp = FlintZZ["t"][1](f*denominator(f))
  fpp = Rt(fp)
  return roots(fpp)
end

function roots(f::fmpq_poly, R::Nemo.NmodRing)
  Rt, t = PolynomialRing(R, "t", cached=false)
  fp = FlintZZ["t"][1](f*denominator(f))
  fpp = Rt(fp)
  return roots(fpp)
end

function ispower(a::Nemo.fq_nmod, m::Int)
  s = size(parent(a))
  if gcd(s-1, m) == 1
    return true, a^invmod(m, s-1)
  end
  St, t = PolynomialRing(parent(a), "t", cached=false)
  f = t^m-a
  rt = roots(f)
  if length(rt) > 0
    return true, rt[1]
  else
    return false, a
  end
end

function roots(f::T) where T <: Union{fq_nmod_poly, fq_poly} # should be in Nemo and
                                    # made available for all finite fields I guess.
  q = size(base_ring(f))
  x = gen(parent(f))
  if degree(f) < q
    x = powmod(x, q, f)-x
  else
    x = x^Int(q)-x
  end
  f = gcd(f, x)
  l = factor(f).fac
  return elem_type(base_ring(f))[-trailing_coefficient(x) for x = keys(l) if degree(x)==1]
end

# generic fall back
# ...
function roots(f::PolyElem)
  lf = factor(f)
  return elem_type(base_ring(f))[-trailing_coefficient(x) for x= keys(lf.fac) if degree(x)==1]
end    

function ispower(a::RingElem, n::Int)
  if isone(a) || iszero(a)
    return true, a
  end
  if isone(-a) && isodd(n)
    return true, a
  end
  R = parent(a)
  Rt, t = PolynomialRing(R, "t", cached = false)
  r = roots(t^n-a)
  if length(r) == 0
    return false, a
  else
    return true, r[1]
  end
end

function root(a::RingElem, n::Int)
  fl, b = ispower(a, n)
  fl || error("element does not have a $n-th root")
  return b
end

function setcoeff!(z::fq_nmod_poly, n::Int, x::fmpz)
   ccall((:fq_nmod_poly_set_coeff_fmpz, :libflint), Nothing,
         (Ref{fq_nmod_poly}, Int, Ref{fmpz}, Ref{FqNmodFiniteField}),
         z, n, x, base_ring(parent(z)))
     return z
end

###############################################################################
#
#  Sturm sequence
#
###############################################################################

#See Wikipedia as a reference
function _divide_by_content(f::fmpz_poly)
  
  p = primpart(f)
  if sign(lead(f))== sign(lead(p))
    return p
  else
    return -p
  end
end

function sturm_sequence(f::fmpz_poly)

  g = f
  h = _divide_by_content(derivative(g))
  seq = fmpz_poly[g,h]
  while true
    r = _divide_by_content(pseudorem(g,h))
    if r != 0
      push!(seq, -r)
      g, h = h, -r
    else 
      break
    end
  end
  return seq

end

function _number_changes(a::Array{Int,1})

  nc = 0
  filter!(x -> x != 0, a)
  for i = 2:length(a)
    if sign(a[i]) != sign(a[i-1])
      nc += 1
    end
  end  
  return nc

end

function number_positive_roots(f::fmpz_poly)

  s = sturm_sequence(f)
  evinf = Int[sign(coeff(x, degree(x))) for x in s]
  ev0 = Int[sign(coeff(x,0)) for x in s]
  return _number_changes(ev0)-_number_changes(evinf)

end

################################################################################
#
#  Squarefree factorization for fmpz_poly
#
################################################################################

@doc Markdown.doc"""
    factor_squarefree(x::fmpq_poly)
> Returns the squarefree factorization of $x$.
"""
function factor_squarefree(x::fmpq_poly)
   res, z = _factor_squarefree(x)
   return Fac(parent(x)(z), res)
end

function _factor_squarefree(x::fmpq_poly)
   res = Dict{fmpq_poly, Int}()
   y = fmpz_poly()
   ccall((:fmpq_poly_get_numerator, :libflint), Nothing,
         (Ref{fmpz_poly}, Ref{fmpq_poly}), y, x)
   fac = Nemo.fmpz_poly_factor()
   ccall((:fmpz_poly_factor_squarefree, :libflint), Nothing,
              (Ref{Nemo.fmpz_poly_factor}, Ref{fmpz_poly}), fac, y)
   z = fmpz()
   ccall((:fmpz_poly_factor_get_fmpz, :libflint), Nothing,
            (Ref{fmpz}, Ref{Nemo.fmpz_poly_factor}), z, fac)
   f = fmpz_poly()
   for i in 1:fac.num
      ccall((:fmpz_poly_factor_get_fmpz_poly, :libflint), Nothing,
            (Ref{fmpz_poly}, Ref{Nemo.fmpz_poly_factor}, Int), f, fac, i - 1)
      e = unsafe_load(fac.exp, i)
      res[parent(x)(f)] = e
   end
   return res, fmpq(z, denominator(x))

end

#=
function roots(f::fmpz_poly)
  g = gcd(f, derivative(f))
  p = p_start
  while true
    p = next_prime(p)
    R = GF(p)
    Rx,x = PolynomialRing(R, cached = false)
    gp = Rx(g)
    if !issquarefree(gp)
      continue
    end
    #TODO: try a few primes to find best (with fewest roots)
    rp = roots(gp)
    if length(rp) == 0
      return []
    end
    
  end
  
end

=#
