################################################################################
#
#  Integer functions
#
################################################################################

function rem(a::fmpz, b::UInt)
  return ccall((:fmpz_fdiv_ui, :libflint), UInt, (Ptr{fmpz}, UInt), &a, b)
end

function isless(a::BigFloat, b::Nemo.fmpz)
  if _fmpz_is_small(b)
    c = ccall((:mpfr_cmp_si, :libmpfr), Int32, (Ptr{BigFloat}, Int), &a, b.d)
  else
    c = ccall((:mpfr_cmp_z, :libmpfr), Int32, (Ptr{BigFloat}, UInt), &a, unsigned(b.d) << 2)
  end
  return c < 0
end

# TODO (CF):
# should be Bernstein'ed: this is slow for large valuations
# returns the maximal v s.th. z mod p^v == 0 and z div p^v
#   also useful if p is not prime....

function remove(z::T, p::T) where T <: Integer
  z == 0 && error("Not yet implemented")
  const v = 0
  while mod(z, p) == 0
    z = div(z, p)
    v += 1
  end
  return (v, z)
end 

function remove(z::Rational{T}, p::T) where T <: Integer
  z == 0 && error("Not yet implemented")
  v, d = remove(denominator(z), p)
  w, n = remove(numerator(z), p)
  return w-v, n//d
end 

function valuation(z::T, p::T) where T <: Integer
  z == 0 && error("Not yet implemented")
  const v = 0
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
  v = ccall((:fmpz_remove, :libflint), Int64, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), a, a, b)
  return v, a
end

function remove!(a::fmpq, b::fmpz)
  nr = ccall((:fmpq_numerator_ptr, :libflint), Ptr{fmpz}, (Ref{fmpq}, ), a)
  vn = ccall((:fmpz_remove, :libflint), Int64, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), nr, nr, b)
  #fmpq's are simplified: either num OR den will be non-trivial
  if vn != 0
    return vn, a
  end
  nr = ccall((:fmpq_denominator_ptr, :libflint), Ptr{fmpz}, (Ref{fmpq}, ), a)
  vn = ccall((:fmpz_remove, :libflint), Int64, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), nr, nr, b)
  return -vn, a
end

function valuation!(a::fmpq, b::fmpz)
  nr = ccall((:fmpq_numerator_ptr, :libflint), Ptr{fmpz}, (Ref{fmpq}, ), a)
  vn = ccall((:fmpz_remove, :libflint), Int64, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), nr, nr, b)
  #fmpq's are simplified: either num OR den will be non-trivial
  if vn != 0
    return vn
  end
  nr = ccall((:fmpq_denominator_ptr, :libflint), Ptr{fmpz}, (Ref{fmpq}, ), a)
  vn = ccall((:fmpz_remove, :libflint), Int64, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), nr, nr, b)
  return -vn
end

function *(a::fmpz, b::BigFloat)
  return BigInt(a)*b
end

function BigFloat(a::fmpq)
  r = BigFloat(0)
  ccall((:fmpq_get_mpfr, :libflint), Void, (Ref{BigFloat}, Ref{fmpq}, Int32), r, a, __get_rounding_mode())
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

function zero(::Type{Nemo.fmpz})
  return fmpz(0)
end

function one(::Type{Nemo.fmpz})
  return fmpz(1)
end

@doc """
  modord(a::fmpz, m::fmpz) -> Int
  modord(a::Integer, m::Integer)

  The multiplicative order of a modulo m (not a good algorithm).
""" ->
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


function isodd(a::fmpz)
  ccall((:fmpz_is_odd, :libflint), Int, (Ref{fmpz},), a) == 1
end

function iseven(a::fmpz)
  ccall((:fmpz_is_even, :libflint), Int, (Ref{fmpz},), a) == 1
end

function neg!(a::fmpz)
  ccall((:fmpz_neg, :libflint), Void, (Ref{fmpz}, Ref{fmpz}), a, a)
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

struct RangeGeneratorfmpz <: Base.Random.RangeGenerator
  a::StepRange{fmpz, fmpz}
end

function Base.Random.RangeGenerator(r::StepRange{fmpz,fmpz})
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

################################################################################
#
#  Should go to Nemo?
#
################################################################################

one(::Type{fmpq}) = fmpq(1)

############################################################
# more unsafe function that Bill does not want to have....
############################################################

function divexact!(z::fmpz, x::fmpz, y::fmpz)
    y == 0 && throw(DivideError())
    ccall((:fmpz_divexact, :libflint), Void, 
          (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), z, x, y)
    return z
end

function lcm!(z::fmpz, x::fmpz, y::fmpz)
   ccall((:fmpz_lcm, :libflint), Void, 
         (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), z, x, y)
   return z
end

function gcd!(z::fmpz, x::fmpz, y::fmpz)
   ccall((:fmpz_gcd, :libflint), Void, 
         (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), z, x, y)
   return z
end

function mul!(z::fmpz, x::fmpz, y::Int)
  ccall((:fmpz_mul_si, :libflint), Void, (Ref{fmpz}, Ref{fmpz}, Int), z, x, y)
  return z
end

function mul!(z::fmpz, x::fmpz, y::UInt)
  ccall((:fmpz_mul_ui, :libflint), Void, (Ref{fmpz}, Ref{fmpz}, UInt), z, x, y)
  return z
end

function mul!(z::fmpz, x::fmpz, y::Integer)
  mul!(z, x, fmpz(y))
  return z
end

function one!(a::fmpz)
  ccall((:fmpz_one, :libflint), Void, (Ref{fmpz}, ), a)
  return a
end

################################################################################
#
#  power detection
#
################################################################################

doc"""
    ispower(a::fmpz) -> Int, fmpz
    ispower(a::Integer) -> Int, Integer
> Writes $a = r^e$ with $e$ maximal. Note: $1 = 1^0$.
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

doc"""
    ispower(a::fmpq) -> Int, fmpq
    ispower(a::Rational) -> Int, Rational
> Writes $a = r^e$ with $e$ maximal. Note: $1 = 1^0$.
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

doc"""
    ispower(a::fmpz, n::Int) -> Bool, fmpz
    ispower(a::fmpq, n::Int) -> Bool, fmpq
    ispower(a::Integer, n::Int) -> Bool, Integer
> Tests if $a$ is an $n$-th power. Return {{{true}}} and the root if successful.
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
    ccall((:fmpz_comb_init, :libflint), Void, (Ptr{fmpz_comb}, Ptr{UInt}, Int),
            &z, primes, length(primes))
    finalizer(z, _fmpz_comb_clear_fn)
    return z
  end
end

function _fmpz_comb_clear_fn(z::fmpz_comb)
  ccall((:fmpz_comb_clear, :libflint), Void, (Ptr{fmpz_comb}, ), &z)
end

mutable struct fmpz_comb_temp
  n::Int
  comb_temp::Ptr{Ptr{fmpz}}
  temp::Ptr{fmpz}
  temp2::Ptr{fmpz}

  function fmpz_comb_temp(comb::fmpz_comb)
    z = new()
    ccall((:fmpz_comb_temp_init, :libflint), Void,
            (Ptr{fmpz_comb_temp}, Ptr{fmpz_comb}), &z, &comb)
    finalizer(z, _fmpz_comb_temp_clear_fn)
    return z
  end
end

function _fmpz_comb_temp_clear_fn(z::fmpz_comb_temp)
  ccall((:fmpz_comb_temp_clear, :libflint), Void, (Ptr{fmpz_comb_temp}, ), &z)
end


function fmpz_multi_crt_ui!(z::fmpz, a::Array{UInt, 1}, b::fmpz_comb, c::fmpz_comb_temp)
  ccall((:fmpz_multi_CRT_ui, :libflint), Void,
          (Ptr{fmpz}, Ptr{UInt}, Ptr{fmpz_comb}, Ptr{fmpz_comb_temp}, Cint),
          &z, a, &b, &c, 1)
  return z
end

function _fmpz_preinvn_struct_clear_fn(z::fmpz_preinvn_struct)
  ccall((:fmpz_preinvn_clear, :libflint), Void, (Ptr{fmpz_preinvn_struct}, ), &z)
end

function fdiv_qr_with_preinvn!(q::fmpz, r::fmpz, g::fmpz, h::fmpz, hinv::fmpz_preinvn_struct)
  ccall((:fmpz_fdiv_qr_preinvn, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}, Ptr{fmpz}, Ptr{fmpz}, Ptr{fmpz_preinvn_struct}), &q, &r, &g, &h, &hinv)
end

function submul!(z::fmpz, x::fmpz, y::fmpz)
  ccall((:fmpz_submul, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}, Ptr{fmpz}), &z, &x, &y)
end

################################################################################
#
#  Number of bits
#
################################################################################

function nbits(a::BigInt)
  return ndigits(a, 2)
end

doc"""
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

doc"""
    isinteger(a::fmpq) -> Bool

> Returns true iff the denominator of $a$ is one.
"""
function isinteger(a::fmpq)
  return isone(denominator(a))
end

################################################################################
#
#  sunit group
#
################################################################################

mutable struct MapSUnitGrpZFacElem{T} <: Hecke.Map{T, FacElemMon{FlintRationalField}}
  header::MapHeader
  idl::Array{fmpz, 1}

  function MapSUnitGrpZFacElem{T}() where {T}
    return new{T}()
  end
end

function show(io::IO, mC::MapSUnitGrpZFacElem)
  println(io, "SUnits (in factored form) map of $(codomain(mC)) for $(mC.idl)")
end

mutable struct MapSUnitGrpZ{T} <: Map{T, FlintRationalField}
  header::MapHeader
  idl::Array{fmpz, 1}

  function MapSUnitGrpZ{T}() where {T}
    return new{T}()
  end
end

function show(io::IO, mC::MapSUnitGrpZ)
  println(io, "SUnits map of $(codomain(mC)) for $(mC.idl)")
end

doc"""
***
    sunit_group_fac_elem(S::Array{fmpz, 1}) -> GrpAbFinGen, Map
    sunit_group_fac_elem(S::Array{Integer, 1}) -> GrpAbFinGen, Map
> The $S$-unit group of $Z$ supported at $S$: the group of
> rational numbers divisible only by primes in $S$.
> The second return value is the map mapping group elements to rationals
> in factored form or rationals back to group elements.
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

  mp.header = Hecke.MapHeader(G, FacElemMon(FlintQQ), dexp, dlog)

  return G, mp
end

doc"""
***
    sunit_group(S::Array{fmpz, 1}) -> GrpAbFinGen, Map
    sunit_group(S::Array{Integer, 1}) -> GrpAbFinGen, Map
> The $S$-unit group of $Z$ supported at $S$: the group of
> rational numbers divisible only by primes in $S$.
> The second return value is the map mapping group elements to rationals
> or rationals back to group elements.
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

  mp.header = Hecke.MapHeader(u, FlintQQ, dexp, mu.header.preimage)

  return u, mp
end

Hecke.gcd(a::fmpz, b::Integer) = Hecke.gcd(a, fmpz(b))
Hecke.gcd(a::Integer, b::fmpz) = Hecke.gcd(fmpz(a), b)
Hecke.lcm(a::fmpz, b::Integer) = Hecke.lcm(a, fmpz(b))
Hecke.lcm(a::Integer, b::fmpz) = Hecke.lcm(fmpz(a), b)

doc"""
    isprime_power(n::fmpz) -> Bool
    isprime_power(n::Integer) -> Bool
> Tests is $n$ is the exact power of a prime number.
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
  a::Ptr{Void}
  function flint_rand_ctx_t()
    return new()
  end
end  

function show(io::IO, A::flint_rand_ctx_t)
  println(io, "Flint random state\n")
end

function flint_rand_state()
  A = flint_rand_ctx_t()
  A.a = ccall((:flint_rand_alloc, :libflint), Ptr{Void}, (Int, ), 1)
  ccall((:flint_randinit, :libflint), Void, (Ptr{Void}, ), A.a)
  
  function clean_rand_state(A::flint_rand_ctx_t)
    ccall((:flint_randclear, :libflint), Void, (Ptr{Void}, ), A.a)
    ccall((:flint_rand_free, :libflint), Void, (Ptr{Void}, ), A.a)
    nothing
  end  
  finalizer(A, clean_rand_state)
  return A
end  

global flint_rand_ctx 

function ecm(a::fmpz, B1::UInt, B2::UInt, ncrv::UInt, rnd = flint_rand_ctx)
  f = fmpz()
  r = ccall((:fmpz_factor_ecm, :libflint), Int32, (Ptr{fmpz}, UInt, UInt, UInt, Ptr{Void}, Ptr{fmpz}), &f, ncrv, B1, B2, rnd.a, &a)
  return r, f
end  

function ecm(a::fmpz, B1::Int, B2::Int, ncrv::Int, rnd = flint_rand_ctx)
  return ecm(a, UInt(B1), UInt(B2), UInt(ncrv), rnd)
end


function factor_trial_range(N::fmpz, start::Int=0, np::Int=10^5)
   F = Nemo.fmpz_factor()
   ccall((:fmpz_factor_trial_range, :libflint), Void, (Ptr{Nemo.fmpz_factor}, Ptr{fmpz}, UInt, UInt), &F, &N, start, np)
   res = Dict{fmpz, Int}()
   for i in 1:F.num
     z = fmpz()
     ccall((:fmpz_factor_get_fmpz, :libflint), Void,
           (Ptr{fmpz}, Ptr{Nemo.fmpz_factor}, Int), &z, &F, i - 1)
     res[z] = unsafe_load(F.exp, i)
   end
   return res, canonical_unit(N)
end

big_primes = fmpz[]

function factor(N::fmpz)
  N_in = N
  global big_primes
  r, c = factor_trial_range(N)
  for (p, v) = r
    N = divexact(N, p^v)
  end
#  if length(r)==0
#    r[1] = 1
#  end
#  @assert prod(p^v for (p, v) = r)*N == N_in
  if isunit(N)
#    @assert all(isprime, keys(r))
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
#  @assert prod(p^v for (p, v) = r)*N == N_in
  fac, N = ispower(N)

  e, f = ecm(N, UInt(10^3), UInt(10^5), UInt(100))
  #TODO: use coprime basis to refine stuff...
  while e != 0
    ee, f = ispower(f)
    ee = valuation(N, f) #careful, f does not need to be prime, so N/f^ee is not coprime to f
    if isprime(f)
      if haskey(r, f)
        r[f] += fac*ee
      else
        r[f] = fac*ee
      end
    else
      s = factor(f)
      for (p, ex) = s.fac
        if haskey(r, p)
          r[p] += fac*ex*ee
        else
          r[p] = fac*ex*ee
        end
      end
    end
#    @assert N % f^ee == 0
#    @assert N % f^(ee+1) != 0
    N = divexact(N, f^ee)
#    @assert prod(p^v for (p, v) = r)*N == N_in
    if isone(N)
      break
    end
    e, f = ecm(N, UInt(10^3), UInt(10^5), UInt(100))
  end
  s = Nemo.factor(N)
  for (p, ex) = s.fac
    if haskey(r, p)
      r[p] += fac*ex
    else
      r[p] = fac*ex
    end
  end
  for p = keys(r)
    if nbits(p) > 60 && !(p in big_primes)
      push!(big_primes, p)
    end
  end
  @assert all(isprime, keys(r))
  @assert prod(a^b for (a,b) = r) * c == N_in
  return Nemo.Fac(c, r)
end


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



