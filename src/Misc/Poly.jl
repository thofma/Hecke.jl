
export rational_reconstruction, farey_lift, div, valence, leading_coefficient,
       trailing_coefficient, constant_coefficient, factor_mod_pk, factor_mod_pk_init, hensel_lift

function PolynomialRing(R::Ring)
  return PolynomialRing(R, "_x")
end

function FlintFiniteField(p::Integer)
  return ResidueRing(ZZ, p)
end

function FlintFiniteField(p::fmpz)
  return ResidueRing(ZZ, p)
end

function fmpz(a::GenRes{Nemo.fmpz})
  return a.data
end

function lift(R::FlintIntegerRing, a::GenRes{Nemo.fmpz})
  return a.data
end

function Base.call(R::FlintIntegerRing, a::GenRes{Nemo.fmpz})
  return a.data
end

## given some r/s = a mod b and deg(r) = n, deg(s) <= m find r,s
## a and b better be polynomials in the same poly ring.
## seems to work for Q (Qx) and Fp experimentally
#
# possibly should be rewritten to use an asymptotically (and practically)
# faster algorithm. For Q possibly using CRT and fast Fp techniques
# Algorithm copies from the bad-primes paper

function rational_reconstruction{S}(a::PolyElem{S}, b::PolyElem{S}, n::Int, m::Int)
  R = a.parent
  if degree(a) <= n return true, a, R(1); end

  M = MatrixSpace(R, 2, 2)()
  M[1,1] = b
  M[2,1] = a
  M[2,2] = R(1)

  T = MatrixSpace(R, 2, 2)()
  T[1,2] = R(1)
  T[2,1] = R(1)
  while degree(M[2,1]) > n
    q, r = divrem(M[1,1], M[2,1])
    T[2,2] = -q
    M = T*M
  end
  if degree(M[2,2]) <= m 
    return true, M[2,1], M[2,2]
  end

  return false, M[2,1], M[2,2]
end

function rational_reconstruction{T}(a::PolyElem{T}, b::PolyElem{T})
  return rational_reconstruction(a, b, div(degree(b), 2), div(degree(b), 2))
end

# to appease the Singular crowd...
farey_lift = rational_reconstruction

# in at least 2 examples produces the same result as Magma
# can do experiments to see if dedicated Berlekamp Massey would be
# faster as well as experiments if Berlekamp Massey yields faster 
# rational_reconstruction as well.
# Idea of using the same agorithm due to E. Thome
#

function berlekamp_massey{T}(a::Array{T, 1})
  Rx,x = PolynomialRing(parent(a[1]))
  f = Rx(a)
  xn= x^length(a)

  fl, n, d = rational_reconstruction(f, xn)
  if fl
    return true, d*(inv(trailing_coefficient(d)))
  else
    return false, Rx(0)
  end
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
function leading_coefficient(f::PolyElem)
  return coeff(f, degree(f))
end

doc"""
***
  trailing_coefficient(f::PolyElem) -> RingElem
  constant_coefficient(f::PolyElem) -> RingElem

>  The constant coefficient of f.
"""
function trailing_coefficient(f::PolyElem)
  return coeff(f, 0)
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

type fmpz_poly_raw  ## fmpz_poly without parent like in c
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


type fmpz_poly_factor
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

type HenselCtx
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
    r = a.lf._num
    a.r = r  
    a.LF = fmpz_poly_factor()
    @assert r > 1  #flint restriction
    a.v = ccall((:flint_malloc, :libflint), Ptr{fmpz_poly_raw}, (Int, ), (2*r-2)*sizeof(fmpz_poly_raw))
    a.w = ccall((:flint_malloc, :libflint), Ptr{fmpz_poly_raw}, (Int, ), (2*r-2)*sizeof(fmpz_poly_raw))
    for i=1:(2*r-2)
      ccall((:fmpz_poly_init, :libflint), Void, (Ptr{fmpz_poly_raw}, ), a.v+(i-1)*sizeof(fmpz_poly_raw))
      ccall((:fmpz_poly_init, :libflint), Void, (Ptr{fmpz_poly_raw}, ), a.w+(i-1)*sizeof(fmpz_poly_raw))
    end
    a.link = ccall((:flint_calloc, :libflint), Ptr{Int}, (Int, Int), r, sizeof(Int))
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

#I think, experimentally, that p = Q^i, p1 = Q^j and j<= i is the conditino to make it tick.
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

