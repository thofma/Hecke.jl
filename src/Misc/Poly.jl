
export rational_reconstruction, farey_lift, div, valence, leading_coefficient,
       trailing_coefficient, constant_coefficient, factor_mod_pk,
       factor_mod_pk_init, hensel_lift, resultant_sircana

function PolynomialRing(R::Ring)
  return PolynomialRing(R, "_x")
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
  return ResidueRing(FlintZZ, p)
end

function FlintFiniteField(p::fmpz)
  @assert isprime(p)
  return ResidueRing(FlintZZ, p)
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

doc"""
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

doc"""
***
  leading_coefficient(f::PolyElem) -> RingElem

>  The last leading coefficient of f.
"""
leading_coefficient(f::PolyElem) = lead(f)

doc"""
***
  trailing_coefficient(f::PolyElem) -> RingElem
  constant_coefficient(f::PolyElem) -> RingElem

>  The constant coefficient of f.
"""
function trailing_coefficient(f::PolyElem)
  return coeff(f, 0)
end

doc"""
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
  ccall((:fmpz_poly_resultant_modular_div, :libflint), Void, 
     (Ptr{fmpz}, Ptr{fmpz_poly}, Ptr{fmpz_poly}, Ptr{fmpz}, Int), 
     &z, &f, &g, &d, nb)
  return z
end

##############################################################
#
# Hensel
#
##############################################################

mutable struct fmpz_poly_raw  ## fmpz_poly without parent like in c
  coeffs::Ptr{Void}
  alloc::Int
  length::Int

  function fmpz_poly_raw()
    error("should not get called")
    z = new()
    ccall((:fmpz_poly_init, :libflint), Void, (Ptr{fmpz_poly},), &z)
    finalizer(z, _fmpz_poly_raw_clear_fn)
    return z
  end
end

function _fmpz_poly_raw_clear_fn(a::fmpz_poly)
  ccall((:fmpz_poly_clear, :libflint), Void, (Ptr{fmpz_poly},), &a)
end


mutable struct fmpz_poly_factor
  c::Int   # really an fmpz  - but there is no fmpz_raw to be flint compatible
  poly::Ptr{fmpz_poly_raw}
  exp::Ptr{Int} 
  _num::Int
  _alloc::Int
    
  function fmpz_poly_factor()
    z = new()
    ccall((:fmpz_poly_factor_init, :libflint), Void,
            (Ptr{fmpz_poly_factor}, ), &z)
    finalizer(z, _fmpz_poly_factor_clear_fn)
    return z
  end
end

function _fmpz_poly_factor_clear_fn(a::fmpz_poly_factor)
  ccall((:fmpz_poly_factor_clear, :libflint), Void,
          (Ptr{fmpz_poly_factor}, ), &a)
end
 
function factor_to_dict(a::fmpz_poly_factor)
  res = Dict{fmpz_poly,Int}()
  Zx,x = PolynomialRing(FlintZZ, "x")
  for i in 1:a._num
    f = Zx()
    ccall((:fmpz_poly_set, :libflint), Void, (Ptr{fmpz_poly}, Ptr{fmpz_poly_raw}), &f, a.poly+(i-1)*sizeof(fmpz_poly_raw))
    res[f] = unsafe_load(a.exp, i)
  end  
  return res
end

function show(io::IO, a::fmpz_poly_factor)
  ccall((:fmpz_poly_factor_print, :libflint), Void, (Ptr{fmpz_poly_factor}, ), &a)
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
    Zx,x = PolynomialRing(FlintZZ, "x")
    Rx,x = PolynomialRing(ResidueRing(FlintZZ, p), "x")
    a.lf = Nemo.nmod_poly_factor(UInt(p))
    ccall((:nmod_poly_factor, :libflint), UInt,
          (Ptr{Nemo.nmod_poly_factor}, Ptr{nmod_poly}), &(a.lf), &Rx(f))
    r = a.lf.num
    a.r = r  
    a.LF = fmpz_poly_factor()
    @assert r > 1  #flint restriction
    a.v = ccall((:flint_malloc, :libflint), Ptr{fmpz_poly_raw}, (Int, ), (2*r-2)*sizeof(fmpz_poly_raw))
    a.w = ccall((:flint_malloc, :libflint), Ptr{fmpz_poly_raw}, (Int, ), (2*r-2)*sizeof(fmpz_poly_raw))
    for i=1:(2*r-2)
      ccall((:fmpz_poly_init, :libflint), Void, (Ptr{fmpz_poly_raw}, ), a.v+(i-1)*sizeof(fmpz_poly_raw))
      ccall((:fmpz_poly_init, :libflint), Void, (Ptr{fmpz_poly_raw}, ), a.w+(i-1)*sizeof(fmpz_poly_raw))
    end
    a.link = ccall((:flint_calloc, :libflint), Ptr{Int}, (Int, Int), 2*r-2, sizeof(Int))
    a.N = 0
    a.prev = 0
    finalizer(a, HenselCtx_free)
    return a
  end

  function free_fmpz_poly_array(p::Ptr{fmpz_poly_raw}, r::Int)
    for i=1:(2*r-2)
      ccall((:fmpz_poly_clear, :libflint), Void, (Ptr{fmpz_poly_raw}, ), p+(i-1)*sizeof(fmpz_poly_raw))
    end
    ccall((:flint_free, :libflint), Void, (Ptr{fmpz_poly_raw}, ), p)
  end
  function free_int_array(a::Ptr{Int})
    ccall((:flint_free, :libflint), Void, (Ptr{Int}, ), a)
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
       (Ptr{fmpz_poly_factor}, Ptr{Int}, Ptr{fmpz_poly_raw}, Ptr{fmpz_poly_raw}, Ptr{fmpz_poly}, Ptr{Nemo.nmod_poly_factor}, Int),
       &a.LF, a.link, a.v, a.w, &a.f, &a.lf, N)
  a.N = N
end

function continue_lift(a::HenselCtx, N::Int)
  a.prev = ccall((:_fmpz_poly_hensel_continue_lift, :libflint), Int, 
       (Ptr{fmpz_poly_factor}, Ptr{Int}, Ptr{fmpz_poly_raw}, Ptr{fmpz_poly_raw}, Ptr{fmpz_poly}, UInt, UInt, Int, Ptr{fmpz}),
       &a.LF, a.link, a.v, a.w, &a.f, a.prev, a.N, N, &fmpz(a.p))
  a.N = N
end

doc"""
***
  factor_mod_pk(f::fmpz_poly, p::Int, k::Int) -> Dict{fmpz_poly, Int}

>  For f that is square-free modulo p, return the factorisation modulo p^k.
"""
function factor_mod_pk(f::fmpz_poly, p::Int, k::Int)
  H = HenselCtx(f, fmpz(p))
  start_lift(H, k)
  return factor_to_dict(H.LF)
end

doc"""
***
  factor_mod_pk_init(f::fmpz_poly, p::Int) -> HenselCtx

>  For f that is square-free modulo p, return a structure that allows to compute
>  the factorisaion modulo p^k for any k
"""
function factor_mod_pk_init(f::fmpz_poly, p::Int)
  H = HenselCtx(f, fmpz(p))
  return H
end

doc"""
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
  ccall((:fmpz_poly_hensel_lift, :libflint), Void, (Ptr{fmpz_poly}, Ptr{fmpz_poly},  Ptr{fmpz_poly},  Ptr{fmpz_poly},  Ptr{fmpz_poly},  Ptr{fmpz_poly},  Ptr{fmpz_poly}, Ptr{fmpz_poly}, Ptr{fmpz_poly}, Ptr{fmpz}, Ptr{fmpz}), &G, &H, &A, &B, &f, &g, &h, &a, &b, &p, &p1)
end

doc"""
***
  hensel_lift(f::fmpz_poly, g::fmpz_poly, h::fmpz_poly, p::fmpz, k::Int) -> (fmpz_poly, fmpz_poly)

>  Given f = gh modulo p for g, h coprime modulo p, compute G, H s.th. f = GH mod p^k and
>  G = g mod p, H = h mod p.
"""
function hensel_lift(f::fmpz_poly, g::fmpz_poly, h::fmpz_poly, p::fmpz, k::Int)
  Rx, x = PolynomialRing(ResidueRing(FlintZZ, p))
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

doc"""
***
  hensel_lift(f::fmpz_poly, g::fmpz_poly, p::fmpz, k::Int) -> (fmpz_poly, fmpz_poly)

>  Given f and g such that g is a divisor of f mod p and g and f/g are coprime, compute a hensel lift of g modulo p^k.
"""
function hensel_lift(f::fmpz_poly, g::fmpz_poly, p::fmpz, k::Int)
  Rx, x = PolynomialRing(ResidueRing(FlintZZ, p))
  h = lift(parent(f), div(Rx(f), Rx(g)))
  return hensel_lift(f, g, h, p, k)[1]
end  
  

function fmpq_poly_to_nmod_poly_raw!(r::nmod_poly, a::fmpq_poly)
  ccall((:_fmpz_vec_get_nmod_poly, :libhecke), Void, (Ptr{nmod_poly}, Ptr{Int}, Int), &r, a.coeffs, a.length)
  p = r.mod_n
  den = ccall((:fmpz_fdiv_ui, :libflint), UInt, (Ptr{Int}, UInt), &a.den, p)
  if den != UInt(1)
    den = ccall((:n_invmod, :libflint), UInt, (UInt, UInt), den, p)
    mul!(r, r, den)
  end
end

function fmpq_poly_to_fmpz_mod_poly!(r::fmpz_mod_poly, a::fmpq_poly, t1::fmpz_poly = fmpz_poly(), t2::fmpz = fmpz())
  ccall((:fmpq_poly_get_numerator, :libflint), Void, (Ptr{fmpz_poly}, Ptr{fmpq_poly}), &t1, &a)
  ccall((:fmpz_mod_poly_set_fmpz_poly, :libflint), Void, (Ptr{fmpz_mod_poly}, Ptr{fmpz_poly}), &r, &t1)
  ccall((:fmpq_poly_get_denominator, :libflint), Void, (Ptr{fmpz}, Ptr{fmpq_poly}), &t2, &a)
  if !isone(t2)
    res = ccall((:fmpz_invmod, :libflint), Cint, (Ptr{fmpz}, Ptr{fmpz}, Ptr{fmpz}), &t2, &t2, &base_ring(r).modulus)
    @assert res != 0
    ccall((:fmpz_mod_poly_scalar_mul_fmpz, :libflint), Void, (Ptr{fmpz_mod_poly}, Ptr{fmpz_mod_poly}, Ptr{fmpz}), &r, &r, &t2)
  end
end

function fmpq_poly_to_nmod_poly(Rx::Nemo.NmodPolyRing, f::fmpq_poly)
  g = Rx()
  fmpq_poly_to_nmod_poly_raw!(g, f)
  return g
end

function fmpz_poly_to_nmod_poly_raw!(r::nmod_poly, a::fmpz_poly)
  ccall((:fmpz_poly_get_nmod_poly, :libflint), Void,
                  (Ptr{nmod_poly}, Ptr{fmpz_poly}), &r, &a)

end

function fmpz_poly_to_nmod_poly(Rx::Nemo.NmodPolyRing, f::fmpz_poly)
  g = Rx()
  fmpz_poly_to_nmod_poly_raw!(g, f)
  return g
end

#= this is handled bu subst (or by f(a))
function evaluate{S <: RingElem, T <: RingElem}(f::PolyElem{S}, a::T)
  v = lead(f)
  for i=degree(f)-1:-1:0
    v = v*a+coeff(f, i)
  end
  return v
end

=#

doc"""
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

doc"""
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

doc"""
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
  e = f-g*h 
  @assert ismonic(h)
  q, r = divrem(s*e, h)
#  @assert s*e == q*h+r
  g = g+t*e+q*g
  h = h+r
#  @assert ismonic(h)
  b = s*g+t*h-1
  c, d = divrem(s*b, h)
  s = s-d
  t = t-t*b-c*g

  return g, h, s, t
end

#factors f as monic * (unit mod lead(f))
# requires some coefficient of f to be a unit
function fun_factor(f::PolyElem{<:RingElem})
  local g0
  local h0
  if isunit(lead(f))
    l= lead(f)
    return f*inv(l), parent(f)(l)
  end
  t = gen(parent(f))
  g0 = parent(f)(0)
  for i=degree(f):-1:0
    if isunit(coeff(f, i))
      h0 = f - g0
      break
    else
      setcoeff!(g0, i, coeff(f, i))
    end
  end

  #co-factors:
  g0 = parent(f)()
  setcoeff!(g0, degree(f) - degree(h0), lead(f))
  setcoeff!(g0, 0, lead(h0))
  s = parent(f)(lead(h0))
  h0 *= inv(lead(h0))
  t = parent(f)(0)

  g, h, s,t = _hensel(f, g0, h0, s, t)
  i = 1
  while g!= g0 || h != h0
    i += 1
    g0 = g
    h0 = h
    g, h, s, t = _hensel(f, g0, h0, s, t)
#    if i>3 
#      error("too long")
#    end
  end

  return g0, h0
end

function my_div(a::T, b::T) where T <: RingElem
  if iszero(a)
    return a
  end
  A = lift(a)
  B = lift(b)
  R = parent(a)
  m = fmpz(modulus(R))
  ga = gcd(A, m)
  ua = div(A, ga)
  gb = gcd(B, m)
  ub = div(B, gb)
  _, x = Hecke.ppio(m, ub)
  r = R(div(ga, gb)*ua*invmod(ub, x))
  return r
end

doc"""
    resultant_sircana(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer} -> T
> The resultant of $f$ anf $g$ using a quadratic-time algorithm.
"""
function resultant_sircana(f::PolyElem{T}, g::PolyElem{T}) where T <: ResElem{S} where S <: Union{fmpz, Integer}
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  Rt = parent(f)
  R = base_ring(Rt)
  m = fmpz(modulus(R))
  Zx = PolynomialRing(FlintZZ)[1]

  if degree(f) < 1 && degree(g) < 1
    if iszero(f) || iszero(g)
      res = R(0)
    else
      res = R(1)
    end
    return res
  end

  if degree(f) < 1
    res = lead(f)^degree(g)
    return res
  end

  if degree(g) < 1
    res = lead(g)^degree(f)
    return res
  end

  c = content(f)
  if !isunit(c)
    f = deepcopy(f)
    for i=0:degree(f)
      setcoeff!(f, i, my_div(coeff(f, i), c))
    end
    res = c^degree(g)*resultant_sircana(f, g)
    return res
  end

  c = content(g)
  if !isunit(c)
    g = deepcopy(g)
    for i=0:degree(g)
      setcoeff!(g, i, my_div(coeff(g, i), c))
    end
    res = c^degree(f)*resultant_sircana(f, g)
    return res
  end

  if degree(f) < degree(g)
    res = (-1)^(degree(f)*degree(g))*resultant_sircana(g, f)
    return res
  end

  #want f % g which works iff lead(g) | lead(f)
  if isunit(lead(g)) ||
    gcd(lift(lead(f)), m)  % gcd(lift(lead(g)), m) == 0
    q = my_div(lead(f), lead(g))
    ff = f - q*g*gen(Rt)^(degree(f) - degree(g))
    @assert degree(f) > degree(ff)
    res = lead(g)^(degree(f) - degree(ff))
    res *= resultant_sircana(ff, g)*R(-1)^(degree(g)*(degree(f) - degree(ff)))
    return res
  end

  #factoring case, need to split the ring as well.
  #merde : we need a coprime factorisation: take
  # 6t^2+2t+3 mod 36....
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

    R1 = ResidueRing(FlintZZ, S(lg))
    R1t = PolynomialRing(R1)[1]
    #g is bad in R1, so factor it
    gR1 = R1t(lift(Zx, g))
    fR1 = R1t(lift(Zx, f))

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
  res = length(cp)==1 ? R(resp[1]) : R(crt(resp, pg))
  return res
end

doc"""
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


