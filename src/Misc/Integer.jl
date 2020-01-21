################################################################################
#
#  Integer functions
#
################################################################################

function rem(a::fmpz, b::UInt)
  return ccall((:fmpz_fdiv_ui, :libflint), UInt, (Ref{fmpz}, UInt), a, b)
end


function isless(a::BigFloat, b::Nemo.fmpz)
  if _fmpz_is_small(b)
    c = ccall((:mpfr_cmp_si, :libmpfr), Int32, (Ref{BigFloat}, Int), a, b.d)
  else
    c = ccall((:mpfr_cmp_z, :libmpfr), Int32, (Ref{BigFloat}, UInt), a, unsigned(b.d) << 2)
  end
  return c < 0
end

function mulmod(a::UInt, b::UInt, n::UInt, ni::UInt)
  ccall((:n_mulmod2_preinv, :libflint), UInt, (UInt, UInt, UInt, UInt), a, b, n, ni)
end


# TODO (CF):
# should be Bernstein'ed: this is slow for large valuations
# returns the maximal v s.th. z mod p^v == 0 and z div p^v
#   also useful if p is not prime....
#
# TODO: what happens to z = 0???

function remove(z::T, p::T) where T <: Integer
  z == 0 && return (0, z)
  v = 0
  while mod(z, p) == 0
    z = div(z, p)
    v += 1
  end
  return (v, z)
end 

function remove(z::Rational{T}, p::T) where T <: Integer
  z == 0 && return(0, z)
  v, d = remove(denominator(z), p)
  w, n = remove(numerator(z), p)
  return w-v, n//d
end 

function valuation(z::T, p::T) where T <: Integer
  z == 0 && return 0
  v = 0
  while mod(z, p) == 0
    z = div(z, p)
    v += 1
  end
  return v
end 

function valuation(z::Rational{T}, p::T) where T <: Integer
  z == 0 && error("Not yet implemented")
  v = valuation(denominator(z), p)
  w = valuation(numerator(z), p)
  return w-v
end 

function remove!(a::fmpz, b::fmpz)
  v = ccall((:fmpz_remove, :libflint), Clong, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), a, a, b)
  return v, a
end

function remove!(a::fmpq, b::fmpz)
  nr = ccall((:fmpq_numerator_ptr, :libflint), Ptr{fmpz}, (Ref{fmpq}, ), a)
  vn = ccall((:fmpz_remove, :libflint), Clong, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), nr, nr, b)
  #fmpq's are simplified: either num OR den will be non-trivial
  if vn != 0
    return vn, a
  end
  nr = ccall((:fmpq_denominator_ptr, :libflint), Ptr{fmpz}, (Ref{fmpq}, ), a)
  vn = ccall((:fmpz_remove, :libflint), Clong, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), nr, nr, b)
  return -vn, a
end

function valuation!(a::fmpq, b::fmpz)
  nr = ccall((:fmpq_numerator_ptr, :libflint), Ptr{fmpz}, (Ref{fmpq}, ), a)
  vn = ccall((:fmpz_remove, :libflint), Clong, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), nr, nr, b)
  #fmpq's are simplified: either num OR den will be non-trivial
  if vn != 0
    return vn
  end
  nr = ccall((:fmpq_denominator_ptr, :libflint), Ptr{fmpz}, (Ref{fmpq}, ), a)
  vn = ccall((:fmpz_remove, :libflint), Clong, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), nr, nr, b)
  return -vn
end

function *(a::fmpz, b::BigFloat)
  return BigInt(a)*b
end

function BigFloat(a::fmpq)
  r = BigFloat(0)
  ccall((:fmpq_get_mpfr, :libflint), Nothing, (Ref{BigFloat}, Ref{fmpq}, Int32), r, a, __get_rounding_mode())
  return r
end

function isless(a::Float64, b::fmpq) return a<b*1.0; end
function isless(a::fmpq, b::Float64) return a*1.0<b; end

function isless(a::Float64, b::fmpz) return a<b*1.0; end
function isless(a::fmpz, b::Float64) return a*1.0<b; end

function (a::FlintIntegerRing)(b::fmpq)
  !isone(denominator(b)) && error("Denominator not 1")
  return deepcopy(numerator(b))
end

function //(a::fmpq, b::fmpz)
  return a//fmpq(b)
end

function //(a::fmpz, b::fmpq)
  return fmpq(a)//b
end

function *(a::fmpz, b::Float64)
  return BigInt(a)*b
end

function *(b::Float64, a::fmpz)
  return BigInt(a)*b
end

function *(a::fmpq, b::Float64)
  return Rational(a)*b
end

function *(b::Float64, a::fmpq)
  return Rational(a)*b
end

function Float64(a::fmpq)
  b = a*fmpz(2)^53
  Float64(div(numerator(b), denominator(b)))/(Float64(2)^53) #CF 2^53 is bad in 32bit
end

function convert(R::Type{Rational{Base.GMP.BigInt}}, a::Nemo.fmpz)
  return R(BigInt(a))
end

log(a::fmpz) = log(BigInt(a))
log(a::fmpq) = log(numerator(a)) - log(denominator(a))

function round(::Type{fmpz}, a::fmpq)
  s = sign(numerator(a))
  n = abs(numerator(a))
  d = denominator(a)
  if isone(d)
    return numerator(a)
  end
  q = div(n, d)
  r = mod(n, d)
  if r >= div(d, 2)
    return s*(q+1)
  else
    return s*q
  end
end

function round(a::fmpq)
  return round(fmpz, a)
end


function one(::Type{Nemo.fmpz})
  return fmpz(1)
end

function divisible(x::Integer, y::Integer)
  return iszero(rem(x, y))
end

@doc Markdown.doc"""
  modord(a::fmpz, m::fmpz) -> Int
  modord(a::Integer, m::Integer)

  The multiplicative order of a modulo m (not a good algorithm).
"""
function modord(a::fmpz, m::fmpz)
  gcd(a,m)!=1 && throw("1st agrument not a unit")
  i = 1
  b = a % m
  while b != 1
    i += 1
    b = b*a % m
  end
  return i
end

function modord(a::Integer, m::Integer)
  gcd(a,m)!=1 && throw("1st agrument not a unit")
  i = 1
  b = a % m
  while b != 1
    i += 1
    b = b*a % m
  end
  return i
end


if Nemo.version() <= v"0.15.1"
  function isodd(a::fmpz)
    ccall((:fmpz_is_odd, :libflint), Int, (Ref{fmpz},), a) == 1
  end

  function iseven(a::fmpz)
    ccall((:fmpz_is_even, :libflint), Int, (Ref{fmpz},), a) == 1
  end
end

function neg!(a::fmpz)
  ccall((:fmpz_neg, :libflint), Nothing, (Ref{fmpz}, Ref{fmpz}), a, a)
  return a
end

##
## to support rand(fmpz:fmpz)....
##
# note, we cannot get a UnitRange as this is only legal for subtypes of Real

function colon(a::Int, b::fmpz)
  return fmpz(a):b
end

function one(::fmpz)
  return fmpz(1)
end

function zero(::fmpz)
  return fmpz(0)
end

#the build-in show fails due to Integer(a::fmpz) not defined
# I don't think it would efficient to provide this for printing
#display() seems to NOT call my show function, why, I don't know
function Integer(a::fmpz)
  return BigInt(a)
end

function show(io::IO, a::StepRange{fmpz, fmpz})
  println(io, "2-element ", typeof(a), ":\n ", a.start, ",", a.stop)
end

#TODO
# need to be mapped onto proper Flint primitives
# flints needs a proper interface to randomness - I think
# currently one simply cannot use it at all
#
# should be tied(?) to the Julia rng stuff?
# similarly, all the derived rand functions should probably also do this
#
# inspired by/ copied from the Base/random.jl
#

function rand(a::StepRange{fmpz, fmpz})
  return rand(Random.GLOBAL_RNG, a)
end

function rand(rng::AbstractRNG, a::StepRange{fmpz, fmpz})
  m = Base.last(a) - Base.first(a)
  m < 0 && throw("range empty")
  nd = ndigits(m, 2)
  nl, high = divrem(nd, 8*sizeof(Base.GMP.Limb))
  if high>0
    mask = m>>(nl*8*sizeof(Base.GMP.Limb))
  end  
  s = fmpz(0)
  while true
    s = fmpz(0)
    for i=1:nl
      s = s << (8*sizeof(Base.GMP.Limb))
      s += rand(Base.GMP.Limb)
    end
    if high >0 
      s = s << high
      s += rand(0:Base.GMP.Limb(mask))
    end
    if s <= m break; end
  end
  return s + first(a)
end

function length(a::StepRange{fmpz, fmpz})
  return a.stop - a.start +1
end

struct RangeGeneratorfmpz# <: Base.Random.RangeGenerator
  a::StepRange{fmpz, fmpz}
end

function Random.RangeGenerator(r::StepRange{fmpz,fmpz})
    m = last(r) - first(r)
    m < 0 && throw(ArgumentError("range must be non-empty"))
    return RangeGeneratorfmpz(r)
end

function rand(rng::AbstractRNG, g::RangeGeneratorfmpz)
  return rand(rng, g.a)
end

function Base.getindex(a::StepRange{fmpz,fmpz}, i::fmpz)
  a.start+(i-1)*Base.step(a)
end

function Base.divrem(a::fmpz, b::Int)
  return (div(a, b), rem(a, b))
end

################################################################################
#
#  Should go to Nemo?
#
################################################################################

one(::Type{fmpq}) = fmpq(1)

############################################################
# more unsafe function that Bill does not want to have....
############################################################


function mod!(z::fmpz, x::fmpz, y::fmpz)
  ccall((:fmpz_mod, :libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), z, x, y)
  return z
end

function divexact!(z::fmpz, x::fmpz, y::fmpz)
  iszero(y) && throw(DivideError())
  ccall((:fmpz_divexact, :libflint), Nothing, 
        (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), z, x, y)
  return z
end

function lcm!(z::fmpz, x::fmpz, y::fmpz)
   ccall((:fmpz_lcm, :libflint), Nothing, 
         (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), z, x, y)
   return z
end

function gcd!(z::fmpz, x::fmpz, y::fmpz)
   ccall((:fmpz_gcd, :libflint), Nothing, 
         (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), z, x, y)
   return z
end

function mul!(z::fmpz, x::fmpz, y::Int)
  ccall((:fmpz_mul_si, :libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, Int), z, x, y)
  return z
end

function mul!(z::fmpz, x::fmpz, y::UInt)
  ccall((:fmpz_mul_ui, :libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, UInt), z, x, y)
  return z
end

function mul!(z::fmpz, x::fmpz, y::Integer)
  mul!(z, x, fmpz(y))
  return z
end

function one!(a::fmpz)
  ccall((:fmpz_one, :libflint), Nothing, (Ref{fmpz}, ), a)
  return a
end

################################################################################
#
#  power detection
#
################################################################################

@doc Markdown.doc"""
    ispower(a::fmpz) -> Int, fmpz
    ispower(a::Integer) -> Int, Integer
Returns $e$, $r$ such that $a = r^e$ with $e$ maximal. Note: $1 = 1^0$.
"""
function ispower(a::fmpz)
  if iszero(a)
    error("must not be zero")
  end
  if isone(a)
    return 0, a
  end
  if a < 0
    e, r = ispower(-a)
    if isone(e)
      return 1, a
    end
    v, s = remove(e, 2)
    return s, -r^(2^v)
  end
  rt = fmpz()
  e = 1
  while true
    ex = ccall((:fmpz_is_perfect_power, :libflint), Int, (Ref{fmpz}, Ref{fmpz}), rt, a)
    if ex == 1 || ex == 0
      return e, a
    end
    e *= ex
    a = rt
  end
end

function ispower(a::Integer)
  e,r = ispower(fmpz(a))
  return e, typeof(a)(r)
end

@doc Markdown.doc"""
    ispower(a::fmpq) -> Int, fmpq
    ispower(a::Rational) -> Int, Rational
Writes $a = r^e$ with $e$ maximal. Note: $1 = 1^0$.
"""
function ispower(a::fmpq)
  e, r = ispower(numerator(a))
  if e==1
    return e, a
  end
  f, s = ispower(denominator(a))
  g = gcd(e, f)
  return g, r^div(e, g)//s^div(f, g)
end

function ispower(a::Rational)
  T = typeof(denominator(a))
  e, r = ispower(fmpq(a))
  return e, T(numerator(r))//T(denominator(r))
end

@doc Markdown.doc"""
    ispower(a::fmpz, n::Int) -> Bool, fmpz
    ispower(a::fmpq, n::Int) -> Bool, fmpq
    ispower(a::Integer, n::Int) -> Bool, Integer
Tests if $a$ is an $n$-th power. Return {{{true}}} and the root if successful.
"""    
function ispower(a::fmpz, n::Int)
  b = root(a, n)
  return b^n==a, b
end

function ispower(a::Integer, n::Int)
  return ispower(fmpz(a), n)
end

function ispower(a::fmpq, n::Int)
  fl, nu = ispower(numerator(a), n)
  if !fl 
    return fl, a
  end
  fl, de = ispower(denominator(a), n)
  return fl, fmpq(nu, de)
end

function issquare(x::fmpq)
  return x > 0 && issquare(numerator(x)) && issquare(denominator(x))
end

################################################################################
#
#  Chinese remaindering modulo UInts to fmpz
#
################################################################################

mutable struct fmpz_comb
  primes::Ptr{UInt}
  num_primes::Int
  n::Int
  comb::Ptr{Ptr{fmpz}}
  res::Ptr{Ptr{fmpz}}
  mod_n::UInt
  mod_ninv::UInt
  mod_norm::UInt

  function fmpz_comb(primes::Array{UInt, 1})
    z = new()
    ccall((:fmpz_comb_init, :libflint), Nothing, (Ref{fmpz_comb}, Ptr{UInt}, Int),
            z, primes, length(primes))
    finalizer(z, _fmpz_comb_clear_fn)
    return z
  end
end

function _fmpz_comb_clear_fn(z::fmpz_comb)
  ccall((:fmpz_comb_clear, :libflint), Nothing, (Ref{fmpz_comb}, ), z)
end

mutable struct fmpz_comb_temp
  n::Int
  comb_temp::Ptr{Ptr{fmpz}}
  temp::Ptr{fmpz}
  temp2::Ptr{fmpz}

  function fmpz_comb_temp(comb::fmpz_comb)
    z = new()
    ccall((:fmpz_comb_temp_init, :libflint), Nothing,
            (Ref{fmpz_comb_temp}, Ref{fmpz_comb}), z, comb)
    finalizer(z, _fmpz_comb_temp_clear_fn)
    return z
  end
end

function _fmpz_comb_temp_clear_fn(z::fmpz_comb_temp)
  ccall((:fmpz_comb_temp_clear, :libflint), Nothing, (Ref{fmpz_comb_temp}, ), z)
end


function fmpz_multi_crt_ui!(z::fmpz, a::Array{UInt, 1}, b::fmpz_comb, c::fmpz_comb_temp)
  ccall((:fmpz_multi_CRT_ui, :libflint), Nothing,
          (Ref{fmpz}, Ptr{UInt}, Ref{fmpz_comb}, Ref{fmpz_comb_temp}, Cint),
          z, a, b, c, 1)
  return z
end

function _fmpz_preinvn_struct_clear_fn(z::fmpz_preinvn_struct)
  ccall((:fmpz_preinvn_clear, :libflint), Nothing, (Ref{fmpz_preinvn_struct}, ), z)
end

function fdiv_qr_with_preinvn!(q::fmpz, r::fmpz, g::fmpz, h::fmpz, hinv::fmpz_preinvn_struct)
  ccall((:fmpz_fdiv_qr_preinvn, :libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}, Ref{fmpz}, Ref{fmpz_preinvn_struct}), q, r, g, h, hinv)
end

function submul!(z::fmpz, x::fmpz, y::fmpz)
  ccall((:fmpz_submul, :libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), z, x, y)
end

################################################################################
#
#  Number of bits
#
################################################################################

function nbits(a::BigInt)
  return ndigits(a, 2)
end

@doc Markdown.doc"""
  nbits(a::Int) -> Int
  nbits(a::UInt) -> Int
  nbits(a::BigInt) -> Int

  Returns the number of bits necessary to represent a
"""
function nbits(a::Int)
  a==0 && return 0
  return Int(ceil(log(abs(a))/log(2)))
end
function nbits(a::UInt)
  a==0 && return 0
  return Int(ceil(log(a)/log(2)))
end


################################################################################
#
#  Modular reduction with symmetric residue system
#
################################################################################

function mod_sym(a::fmpz, b::fmpz)
  c = mod(a,b)
  @assert c>=0
  if b > 0 && 2*c > b
    return c-b
  elseif b < 0 && 2*c > -b
    return c+b
  else
    return c
  end
end

@doc Markdown.doc"""
    isinteger(a::fmpq) -> Bool

Returns true iff the denominator of $a$ is one.
"""
function isinteger(a::fmpq)
  return isone(denominator(a))
end

################################################################################
#
#  sunit group
#
################################################################################

mutable struct MapSUnitGrpZFacElem{T} <: Map{T, FacElemMon{FlintRationalField}, HeckeMap, MapSUnitGrpZFacElem}
  header::MapHeader
  idl::Array{fmpz, 1}

  function MapSUnitGrpZFacElem{T}() where {T}
    return new{T}()
  end
end

function show(io::IO, mC::MapSUnitGrpZFacElem)
  println(io, "SUnits (in factored form) map of $(codomain(mC)) for $(mC.idl)")
end

mutable struct MapSUnitGrpZ{T} <: Map{T, FlintRationalField, HeckeMap, MapSUnitGrpZ}
  header::MapHeader
  idl::Array{fmpz, 1}

  function MapSUnitGrpZ{T}() where {T}
    return new{T}()
  end
end

function show(io::IO, mC::MapSUnitGrpZ)
  println(io, "SUnits map of $(codomain(mC)) for $(mC.idl)")
end

@doc Markdown.doc"""
    sunit_group_fac_elem(S::Array{fmpz, 1}) -> GrpAbFinGen, Map
    sunit_group_fac_elem(S::Array{Integer, 1}) -> GrpAbFinGen, Map
The $S$-unit group of $Z$ supported at $S$: the group of
rational numbers divisible only by primes in $S$.
The second return value is the map mapping group elements to rationals
in factored form or rationals back to group elements.
"""
function sunit_group_fac_elem(S::Array{T, 1}) where T <: Integer
  return sunit_group_fac_elem(fmpz[x for x=S])
end

function sunit_group_fac_elem(S::Array{fmpz, 1})
  S = coprime_base(S)  #TODO: for S-units use factor???
  G = DiagonalGroup(vcat([fmpz(2)], fmpz[0 for i=S]))
  S = vcat(fmpz[-1], S)

  mp = MapSUnitGrpZFacElem{typeof(G)}()
  mp.idl = S

  Sq = fmpq[x for x=S]

  function dexp(a::GrpAbFinGenElem)
    return FacElem(Sq, [a.coeff[1,i] for i=1:length(S)])
  end

  function dlog(a::fmpz)
    g = [a>=0 ? 0 : 1]
    g = vcat(g, [valuation(a, x) for x=S[2:end]])
    return G(g)
  end

  function dlog(a::Integer)
    return dlog(fmpz(a))
  end

  function dlog(a::Rational)
    return dlog(fmpq(a))
  end

  function dlog(a::fmpq)
    return dlog(numerator(a)) - dlog(denominator(a))
  end

  function dlog(a::FacElem)
    return sum([e*dlog(k) for (k,e) = a.fac])
  end

  mp.header = MapHeader(G, FacElemMon(FlintQQ), dexp, dlog)

  return G, mp
end

@doc Markdown.doc"""
    sunit_group(S::Array{fmpz, 1}) -> GrpAbFinGen, Map
    sunit_group(S::Array{Integer, 1}) -> GrpAbFinGen, Map
The $S$-unit group of $Z$ supported at $S$: the group of
rational numbers divisible only by primes in $S$.
The second return value is the map mapping group elements to rationals
or rationals back to group elements.
"""
function sunit_group(S::Array{T, 1}) where T <: Integer
  return sunit_group(fmpz[x for x=S])
end

function sunit_group(S::Array{fmpz, 1})
  u, mu = sunit_group_fac_elem(S)

  mp = MapSUnitGrpZ{typeof(u)}()
  mp.idl = S

  function dexp(a::GrpAbFinGenElem)
    return evaluate(image(mu, a))
  end

  mp.header = MapHeader(u, FlintQQ, dexp, mu.header.preimage)

  return u, mp
end

@doc Markdown.doc"""
    isprime_power(n::fmpz) -> Bool
    isprime_power(n::Integer) -> Bool
Tests is $n$ is the exact power of a prime number.
"""
function isprime_power(n::fmpz)
  e, p = ispower(n)
  return isprime(p)
end

function isprime_power(n::Integer)
  return isprime_power(fmpz(n))
end

################################################################################
# random and factor
################################################################################

factor(a::RingElem) = Nemo.factor(a)
factor(a::Integer) = factor(fmpz(a))

mutable struct flint_rand_ctx_t
  a::Ptr{Nothing}
  function flint_rand_ctx_t()
    return new()
  end
end  

function show(io::IO, A::flint_rand_ctx_t)
  println(io, "Flint random state")
end

function flint_rand_state()
  A = flint_rand_ctx_t()
  A.a = ccall((:flint_rand_alloc, :libflint), Ptr{Nothing}, (Int, ), 1)
  ccall((:flint_randinit, :libflint), Nothing, (Ptr{Nothing}, ), A.a)
  
  function clean_rand_state(A::flint_rand_ctx_t)
    ccall((:flint_randclear, :libflint), Nothing, (Ptr{Nothing}, ), A.a)
    ccall((:flint_rand_free, :libflint), Nothing, (Ptr{Nothing}, ), A.a)
    nothing
  end  
  finalizer(clean_rand_state, A)
  return A
end  

global flint_rand_ctx 

function ecm(a::fmpz, B1::UInt, B2::UInt, ncrv::UInt, rnd = flint_rand_ctx)
  f = fmpz()
  r = ccall((:fmpz_factor_ecm, :libflint), Int32, (Ref{fmpz}, UInt, UInt, UInt, Ptr{Nothing}, Ref{fmpz}), f, ncrv, B1, B2, rnd.a, a)
  return r, f
end  

function ecm(a::fmpz, B1::Int, B2::Int, ncrv::Int, rnd = flint_rand_ctx)
  return ecm(a, UInt(B1), UInt(B2), UInt(ncrv), rnd)
end

#data from http://www.mersennewiki.org/index.php/Elliptic_Curve_Method
B1 = [2, 11, 50, 250, 1000, 3000, 11000, 43000, 110000, 260000, 850000, 2900000];
nC = [25, 90, 300, 700, 1800, 5100, 10600, 19300, 49000, 124000, 210000, 340000];

function ecm(a::fmpz, max_digits::Int = div(ndigits(a), 2)+1, rnd = flint_rand_ctx)
  n = ndigits(a, 10)
  B1s = 15

  i = 1
  s = div(max_digits-15, 5)+2
  #i = s = max(i, s)
  while i <= s
    e,f = ecm(a, B1[i]*1000, B1[i]*1000*100, nC[i], rnd)
    if e != 0
      return (e,f)
    end
    i += 1
    if i > length(B1)
      return (e, f)
    end
  end
  return (Int32(0), a)
end

function factor_trial_range(N::fmpz, start::Int=0, np::Int=10^5)
   F = Nemo.fmpz_factor()
   ccall((:fmpz_factor_trial_range, :libflint), Nothing, (Ref{Nemo.fmpz_factor}, Ref{fmpz}, UInt, UInt), F, N, start, np)
   res = Dict{fmpz, Int}()
   for i in 1:F.num
     z = fmpz()
     ccall((:fmpz_factor_get_fmpz, :libflint), Nothing,
           (Ref{fmpz}, Ref{Nemo.fmpz_factor}, Int), z, F, i - 1)
     res[z] = unsafe_load(F.exp, i)
   end
   return res, canonical_unit(N)
end

const big_primes = fmpz[]

function factor(N::fmpz)
  if iszero(N)
    throw(ArgumentError("Argument is not non-zero"))
  end
  N_in = N
  global big_primes
  r, c = factor_trial_range(N)
  for (p, v) = r
    N = divexact(N, p^v)
  end
  if isunit(N)
    @assert N == c
    return Nemo.Fac(c, r)
  end
  N *= c
  @assert N > 0

  for p = big_primes
    v, N = remove(N, p)
    if v > 0
      @assert !haskey(r, p)
      r[p] = v
    end
  end
  factor_insert!(r, N)
  for p = keys(r)
    if nbits(p) > 60 && !(p in big_primes)
      push!(big_primes, p)
    end
  end
  return Nemo.Fac(c, r)
end

function factor_insert!(r::Dict{fmpz, Int}, N::fmpz, scale::Int = 1)
  #assumes N to be positive
  #        no small divisors 
  #        no big_primes
  if isone(N)
    return r
  end
  fac, N = ispower(N)
  if fac > 1
    return factor_insert!(r, N, fac)
  end
  if isprime(N)
    @assert !haskey(r, N)
    r[N] = fac
    return r
  end
  if ndigits(N) < 60
    s = Nemo.factor(N) #MPQS
    for (p, k) in s
      if haskey(r, p)
        r[p] += k*scale
      else
        r[p] = k*scale
      end
    end
    return r
  end

  e, f = ecm(N)
  if e == 0
    s = Nemo.factor(N)
    for (p, k) in s
      if haskey(r, p)
        r[p] += k*scale
      else
        r[p] = k*scale
      end
    end
    return r
  end
  k, N = remove(N, f)
  @assert k > 0
  factor_insert!(r, N, scale)
  factor_insert!(r, f, scale*k)
  return r
end
  
#TODO: problem(s)
# Nemo.factor = mpqs is hopeless if > n digits, but asymptotically and practically
# faster than ecm.
# ecm is much better if there are "small" factors.
# p-1 and p+1 methods are missing
# so probably
# if n is small enough -> Nemo
# if n is too large: ecm
# otherwise
#  need ecm to find small factors
# then recurse...

function ceil(::Type{fmpz}, a::BigFloat)
  return fmpz(ceil(BigInt, a))
end

function floor(::Type{fmpz}, a::BigFloat)
  return fmpz(floor(BigInt, a))
end

function round(::Type{fmpz}, a::BigFloat)
  return fmpz(round(BigInt, a))
end

/(a::BigFloat, b::fmpz) = a/BigInt(b)

function rand!(A::Vector{fmpz}, v::StepRange{fmpz, fmpz})
  for i in 1:length(A)
    A[i] = rand(v)
  end
  return A
end

Base.isless(a::Int, b::fmpz) = a < b

Base.isless(a::fmpz, b::Int) = a < b

function (::Type{Base.Rational{BigInt}})(x::fmpq)
  return Rational{BigInt}(BigInt(numerator(x)), BigInt(denominator(x)))
end

export euler_phi_inv, Divisors, carmichael_lambda

@doc Markdown.doc"""
    Divisors{T}

An iterator for the divisors of a given object.
Create using 
    Divisors(A, power::Int = 1)
where A is either a FacElem or a direct element. Power can be used
to restrict to objects B s.th. B^power still divides A, e.g. 
    Divisors(12, powers = 2)
will produce square divisors.

For rings where this makes sense, ie. where the unit group is finite,
```units = true``` can be passed in to also take into accound
the units.
"""
mutable struct Divisors{T} 
  n::T
  lf::MSet{T}
  s#::Iterator
  f::Function
  U::GrpAbFinGen
  function Divisors(a::T; units::Bool = false, power::Int = 1) where {T}
    r = new{T}()
    r.n = a
    r.lf = MSet{T}()
    for (p, k) = factor(a).fac
      k = div(k, power)
      if k > 0 
        push!(r.lf, p, k)
      end
    end
    r.f = x -> length(x) == 0 ? one(parent(a)) : prod(x)
    r.s = subsets(r.lf)
    if units
      U, mU = unit_group(parent(a))
      r.U = U
      g = r.f
      r.f = x->mU(x[1]) * g(x[2])
      r.s = Base.Iterators.ProductIterator((U, r.s))
    end
   return r
  end
  function Divisors(a::NfOrdIdl; units::Bool = false, power::Int = 1)
    r = new{NfOrdIdl}()
    r.n = a
    r.lf = MSet{NfOrdIdl}()
    for (p, k) = factor(a)
      k = div(k, power)
      if k > 0 
        push!(r.lf, p, k)
      end
    end
    r.f = x -> length(x) == 0 ? one(parent(a)) : prod(x)
    r.s = subsets(r.lf)
    return r
  end
  function Divisors(a::FacElem{NfOrdIdl}; units::Bool = false, power::Int = 1)
    r = new{NfOrdIdl}()
    r.n = evaluate(a)
    r.lf = MSet{NfOrdIdl}()
    for (p, k) = factor(a)
      k = div(k, power)
      if k > 0 
        push!(r.lf, p, k)
      end
    end
    r.f = x -> length(x) == 0 ? one(parent(a)) : prod(x)
    r.s = subsets(r.lf)
    return r
  end

  function Divisors(a::FacElem{fmpz, FlintIntegerRing}; units::Bool = false, power::Int = 1) 
    r = new{fmpz}()
    r.n = evaluate(a)
    r.lf = MSet{fmpz}()
    for (p, k) = factor(a).fac
      k = div(k, power)
      if k > 0 
        push!(r.lf, p, k)
      end
    end
    r.f = x -> length(x) == 0 ? one(parent(r.n)) : prod(x)
    r.s = subsets(r.lf)
    if units
      U, mU = unit_group(parent(a))
      r.U = U
      g = r.f
      r.f = x->mU(x[1]) * g(x[2])
      r.s = Base.Iterators.ProductIterator((U, r.s))
    end
   return r
  end
  function Divisors(a::Fac{fmpz}; units::Bool = false, power::Int = 1)
    return Divisors(FacElem(a), units = units, power = power)
  end
end
Base.IteratorSize(::Divisors) = Base.HasLength() 
Base.length(D::Divisors) = length(D.s)                                                    

function Base.iterate(D::Divisors)
  x = iterate(D.s)
  if x == nothing
    return x
  end
  return D.f(x[1]), x[2]
end

function Base.iterate(D::Divisors, i)
  x = iterate(D.s, i)
  if x == nothing
    return x
  end
  return D.f(x[1]), x[2]
end

function Base.show(io::IO, D::Divisors)
  print(io, "Divisors of $(D.n) = $(D.lf)")
  if isdefined(D, :U)
    print(io, " times $(D.U)")
  end
  print(io, "\n")
end

@doc Markdown.doc"""
    unit_group(::FlintIntegerRing) -> GrpAbFinGen, Map

The unit group of Z, ie. C_2 and the map translating between the group and Z.    
"""
function unit_group(::FlintIntegerRing)
  G = DiagonalGroup([2])
  exp = function(z::GrpAbFinGenElem)
    return isodd(z[1]) ? fmpz(-1) : fmpz(1)
  end
  log = function(z::fmpz)
    return z == -1 ? G[1] : G[0]
  end
  return G, MapFromFunc(exp, log, G, FlintZZ)
end

@doc Markdown.doc"""
    unit_group(::Integers{T}) -> GrpAbFinGen, Map

The unit group of , ie. C_2 and the map translating between the group and Z.    
"""
function unit_group(R::AbstractAlgebra.Integers{T}) where {T}
  G = DiagonalGroup([2])
  exp = function(z::GrpAbFinGenElem)
    return isodd(z[1]) ? T(-1) : T(1)
  end
  log = function(z::T)
    return z == -1 ? G[1] : G[0]
  end
  return G, MapFromFunc(exp, log, G, R)
end

#Nemo.GaloisField = nmod?
# PolyRing

#basically from
#http://people.math.gatech.edu/~ecroot/shparlinski_final.pdf
#Contini, Croot, Shparlinski: Complexity of inverting the Euler function
@doc Markdown.doc"""
    euler_phi_inv_fac_elem(n::fmpz)
The inverse of the Euler totient functions: find all $x$ s.th. $phi(x) = n$
holde. The elements are returned in factored form.
"""
function euler_phi_inv_fac_elem(n::fmpz)
  lp = fmpz[]
  for d = Divisors(n)
    if isprime(d+1)
      push!(lp, d+1)
    end
  end
#  println("possible primes: ", lp)

  E = Tuple{fmpz, Vector{Tuple{fmpz, Int}}}[]
  res = FacElem{fmpz, FlintIntegerRing}[]
  for p = lp
    v = valuation(n, p)
    for i=0:v
      push!(E, ((p-1)*p^i, [(p, i+1)]))
      if E[end][1] == n
        push!(res, FacElem(Dict(E[end][2])))
      end
    end
  end
  while true
    F = []
    for e = E
      nn = divexact(n, e[1])
      x = e[2]
      pm = x[end][1]
      for p = lp
        if p <= pm
          continue
        end
        if nn % (p-1) == 0
          v = valuation(nn, p)
          for i = 0:v
            push!(F, (e[1]*(p-1)*p^i, vcat(e[2], [(p, i+1)])))
            if F[end][1] == n
              push!(res, FacElem(Dict(F[end][2])))
            end
          end
        end
      end
    end
    if length(F) == 0
      return res
    end
    E = F
  end
end

function euler_phi(x::Fac{fmpz})
  return prod((p-1)*p^(v-1) for (p,v) = x.fac)
end

function euler_phi(x::FacElem{fmpz, FlintIntegerRing})
  x = factor(x)
  return prod((p-1)*p^(v-1) for (p,v) = x.fac)
end

function carmichael_lambda(x::Fac{fmpz})
  if haskey(x.fac, fmpz(2))
    y = deepcopy(x.fac)
    v = y[fmpz(2)]
    delete!(y, fmpz(2))
    if v > 2
      c = fmpz(2)^(v-2)
    else
      c = fmpz(1)
    end
  else
    c = fmpz(1)
    y = x.fac
  end
  if length(y) == 0
    return c
  end
  return c * reduce(lcm, (p-1)*p^(v-1) for (p,v) = y)
end

function carmichael_lambda(x::fmpz)
  v, x = remove(x, fmpz(2))
  if isone(x)
    c = x
  else
    x = factor(x)
    c = reduce(lcm, (p-1)*p^(v-1) for (p,v) = x.fac)
  end
  if v < 2
    return c
  else 
    return fmpz(2)^(v-2)*c
  end
end

function carmichael_lambda(x::FacElem{fmpz, FlintIntegerRing})
  x = factor(x)
  return carmichael_lambda(x)
end

function carmichael_lambda(n::T) where {T <: Integer}
  return T(carmichael_lambda(fmpz(n)))
end

@doc Markdown.doc"""
    euler_phi_inv(n::Integer) -> Array{fmpz, 1}
The inverse of the Euler totient functions: find all $x$ s.th. $phi(x) = n$
holds.
"""
function euler_phi_inv(n::Integer)
  return euler_phi_inv(fmpz(n))
end

@doc Markdown.doc"""
    euler_phi_inv(n::fmpz) -> Array{fmpz, 1}
The inverse of the Euler totient functions: find all $x$ s.th. $phi(x) = n$
holds.
"""
function euler_phi_inv(n::fmpz)
  return [ evaluate(x) for x = euler_phi_inv_fac_elem(n)]
end

function factor(a::FacElem{fmpz, FlintIntegerRing})
  b = simplify(a)
  c = Dict{fmpz, Int}()
  s = fmpz(1)
  for (p,k) = b.fac
    lp = factor(p)
    s *= lp.unit
    for (q,w) = lp.fac
      c[q] = w*k
    end
  end
  l = Fac{fmpz}()
  l.fac = c
  l.unit = s
  return l
end

function FacElem(a::Fac{fmpz})
  f = FacElem(a.fac)
  if a.unit == -1
    return a.unit * f
  end
  return f
end

#= for torsion units:

   [maximum([maximum(vcat([fmpz(-1)], euler_phi_inv(x))) for x = Divisors(fmpz(n))]) for n = 1:250]

=# 

radical(a::fmpz) = prod(keys(factor(a).fac))
function radical(a::T) where {T <: Integer}
  return T(radical(fmpz(a)))
end

function quo(::FlintIntegerRing, a::fmpz)
  R = ResidueRing(FlintZZ, a)
  f = MapFromFunc(x -> R(x), y->lift(y), FlintZZ, R)
  return R, f
end

function quo(::FlintIntegerRing, a::Integer)
  R = ResidueRing(FlintZZ, a)
  f = MapFromFunc(x -> R(x), y->lift(y), FlintZZ, R)
  return R, f
end

function (::FlintIntegerRing)(x::Rational{Int})
  @assert denominator(x) == 1
  return fmpz(numerator(x))
end

module BitsMod

using Hecke
import Nemo
import Base: ^, show, getindex, iterate, length
import Hecke.bits
export bits, Limbs


const hb = UInt(1)<<63

#= not used - lacks length
struct BitsUInt
  a::UInt
end

function bits(a::UInt)
  l = nbits(a)
  return BitsUInt(a<<(sizeof(a)*8-l))
end


function Base.iterate(x::BitsUInt)
  return iterate(x, x.a)
end

@inline function Base.iterate(x::BitsUInt, u::UInt)
  iszero(u) && return nothing
  return (u&hb) != 0, u<<1
end
=#


struct Limbs
  a::fmpz
  len::Int
  b::Ptr{UInt}
  function Limbs(a::fmpz)
    if Nemo._fmpz_is_small(a)
      return new(a, 0, convert(Ptr{UInt}, 0))
    end
    z = convert(Ptr{Cint}, unsigned(a.d)<<2)
    len = unsafe_load(z, 2)
    d = convert(Ptr{Ptr{UInt}}, unsigned(a.d) << 2) + 2*sizeof(Cint)
    p = unsafe_load(d)
    return new(a, len, p)
  end
end

function show(io::IO, L::Limbs)
  print(io, "limb-access for: ", L.a)
end

@inline function getindex(L::Limbs, i::Int)
  @boundscheck @assert i <= L.len
  if L.len == 0
    return UInt(abs(L.a.d)) #error???
  end
  return unsafe_load(L.b, i)
end

function iterate(L::Limbs)
  return L[L.len], L.len
end

function iterate(L::Limbs, i::Int)
  i == 0 && return nothing
  return L[i-1], i-1
end

length(L::Limbs) = L.len+1

#=
#from https://github.com/JuliaLang/julia/issues/11592
#compiles directly down to the ror/rol in assembly
for T in Base.BitInteger_types
  mask = UInt8(sizeof(T) << 3 - 1)
  @eval begin
    ror(x::$T, k::Integer) = (x >>> ($mask & k)) | (x <<  ($mask & -k))
    rol(x::$T, k::Integer) = (x <<  ($mask & k)) | (x >>> ($mask & -k))
  end
end
=#

struct BitsFmpz
  L::Limbs

  function BitsFmpz(b::fmpz)
    return new(Limbs(b))
  end
end

function iterate(B::BitsFmpz)
  L = B.L
  a = L[L.len]
  b = UInt(1) << (nbits(a)-1)
  return true, (b, L.len)
end

function iterate(B::BitsFmpz, s::Tuple{UInt, Int})
  b = s[1] >> 1
  if b == 0
    l = s[2] - 1
    if l < 1
      return nothing
    end
    b = hb
    a = B.L[l]
    return a&b != 0, (b, l)
  end
  return B.L[s[2]]&b != 0, (b, s[2])
end

function show(io::IO, B::BitsFmpz)
  print(io, "bit iterator for:", B.L.a)
end

length(B::BitsFmpz) = nbits(B.L.a)

bits(a::fmpz) = BitsFmpz(a)
#= wrong order, thus disabled

function getindex(B::BitsFmpz, i::Int) 
  return ccall((:fmpz_tstbit, :libflint), Int, (Ref{fmpz}, Int), B.L.a, i) != 0
end
=#

function ^(a::T, n::fmpz) where {T}
  fits(Int, n) && return a^Int(n)
  if isnegative(n)
    a = inv(a)
    n = -n
  end
  r = one(parent(a))
  for b = bits(n)
    r = mul!(r, r, r)
    if b 
      r = mul!(r, r, a)
    end
  end
  return r
end

end

using .BitsMod
export bits, Limbs

################################################################################
#
#  Prime numbers up to
#
################################################################################

@doc Markdown.doc"""
    primes_up_to(n::Int) -> Vector{Int}
Returns a vector containing all the prime numbers up to $n$
"""
function primes_up_to(n::Int)
  list = trues(n)
  list[1] = false
  i = 2
  s = 4
  while s <= n
    list[s] = false
    s += 2
  end
  i = 3
  b = sqrt(n)
  while i <= b
    if list[i]
      j = 3*i
      s = 2*i
      while j <= n
        list[j] = false
        j += s
      end
    end
    i += 1
  end
  return findall(list)
end

################################################################################
#
#  Squarefree numbers up to
#
################################################################################

@doc Markdown.doc"""
    squarefree_up_to(n::Int) -> Vector{Int}
Returns a vector containing all the squarefree numbers up to $n$
"""
function squarefree_up_to(n::Int; coprime_to::Array{fmpz,1}=fmpz[])
  list = trues(n)
  for x in coprime_to
    if !fits(Int, x)
      continue
    end
    t = Int(x)
    while t <= n
      list[t]=false
      t += Int(x)
    end
  end
  i = 2
  b = root(n, 2)
  lp = primes_up_to(b)
  for i = 1:length(lp)
    p2 = lp[i]^2
    ind = p2
    while ind <= n
      list[ind] = false
      ind += p2
    end
  end
  return findall(list)
end

################################################################################
#
#  issquarefree
#
################################################################################

#TODO (Hard): Implement this properly.
@doc Markdown.doc"""
    issquarefree(n::Union{Int, fmpz}) -> Bool
Returns true if $n$ is squarefree, false otherwise.
"""
function issquarefree(n::Union{Int,fmpz})
  if iszero(n)
    error("Argument must be non-zero")
  end
  if isone(abs(n))
    return true
  end
  e, b = ispower(n)
  if e > 1
    return false
  end
  return isone(maximum(values(factor(n).fac)))
end



