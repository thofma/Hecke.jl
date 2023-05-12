################################################################################
#
#  Integer functions
#
################################################################################

function rem(a::ZZRingElem, b::UInt)
  return ccall((:fmpz_fdiv_ui, libflint), UInt, (Ref{ZZRingElem}, UInt), a, b)
end


function isless(a::BigFloat, b::Nemo.ZZRingElem)
  if _fmpz_is_small(b)
    c = ccall((:mpfr_cmp_si, :libmpfr), Int32, (Ref{BigFloat}, Int), a, b.d)
  else
    c = ccall((:mpfr_cmp_z, :libmpfr), Int32, (Ref{BigFloat}, UInt), a, unsigned(b.d) << 2)
  end
  return c < 0
end

function mulmod(a::UInt, b::UInt, n::UInt, ni::UInt)
  ccall((:n_mulmod2_preinv, libflint), UInt, (UInt, UInt, UInt, UInt), a, b, n, ni)
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
  @assert p > 1
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
  @assert p > 1
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

function remove!(a::ZZRingElem, b::ZZRingElem)
  v = ccall((:fmpz_remove, libflint), Clong, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), a, a, b)
  return v, a
end

function remove!(a::QQFieldElem, b::ZZRingElem)
  nr = ccall((:fmpq_numerator_ptr, libflint), Ptr{ZZRingElem}, (Ref{QQFieldElem}, ), a)
  vn = ccall((:fmpz_remove, libflint), Clong, (Ptr{ZZRingElem}, Ptr{ZZRingElem}, Ref{ZZRingElem}), nr, nr, b)
  #QQFieldElem's are simplified: either num OR den will be non-trivial
  if vn != 0
    return vn, a
  end
  nr = ccall((:fmpq_denominator_ptr, libflint), Ptr{ZZRingElem}, (Ref{QQFieldElem}, ), a)
  vn = ccall((:fmpz_remove, libflint), Clong, (Ptr{ZZRingElem}, Ptr{ZZRingElem}, Ref{ZZRingElem}), nr, nr, b)
  return -vn, a
end

function valuation!(a::QQFieldElem, b::ZZRingElem)
  nr = ccall((:fmpq_numerator_ptr, libflint), Ptr{ZZRingElem}, (Ref{QQFieldElem}, ), a)
  vn = ccall((:fmpz_remove, libflint), Clong, (Ptr{ZZRingElem}, Ptr{ZZRingElem}, Ref{ZZRingElem}), nr, nr, b)
  #QQFieldElem's are simplified: either num OR den will be non-trivial
  if vn != 0
    return vn
  end
  nr = ccall((:fmpq_denominator_ptr, libflint), Ptr{ZZRingElem}, (Ref{QQFieldElem}, ), a)
  vn = ccall((:fmpz_remove, libflint), Clong, (Ptr{ZZRingElem}, Ptr{ZZRingElem}, Ref{ZZRingElem}), nr, nr, b)
  return -vn
end

function *(a::ZZRingElem, b::BigFloat)
  return BigInt(a)*b
end

function BigFloat(a::QQFieldElem)
  r = BigFloat(0)
  ccall((:fmpq_get_mpfr, libflint), Nothing, (Ref{BigFloat}, Ref{QQFieldElem}, Int32), r, a, __get_rounding_mode())
  return r
end

function isless(a::Float64, b::QQFieldElem) return a<b*1.0; end
function isless(a::QQFieldElem, b::Float64) return a*1.0<b; end

function isless(a::Float64, b::ZZRingElem) return a<b*1.0; end
function isless(a::ZZRingElem, b::Float64) return a*1.0<b; end

is_commutative(::ZZRing) = true

#function ^(a::ZZRingElem, k::ZZRingElem)
#  if a == 0
#    if k == 0
#      return ZZRingElem(1)
#    end
#    return ZZRingElem(0)
#  end
#
#  if a == 1
#    return ZZRingElem(1)
#  end
#  if a == -1
#    if isodd(k)
#      return ZZRingElem(-1)
#    else
#      return ZZRingElem(1)
#    end
#  end
#  return a^Int(k)
#end

function ^(a::QQFieldElem, k::ZZRingElem)
  if a == 0
    if k == 0
      return QQFieldElem(1)
    end
    return QQFieldElem(0)
  end

  if a == 1
    return QQFieldElem(1)
  end
  if a == -1
    if isodd(k)
      return QQFieldElem(-1)
    else
      return QQFieldElem(1)
    end
  end
  return a^Int(k)
end

function //(a::ZZRingElem, b::QQFieldElem)
  return QQFieldElem(a)//b
end

function *(a::ZZRingElem, b::Float64)
  return BigInt(a)*b
end

function *(b::Float64, a::ZZRingElem)
  return BigInt(a)*b
end

function *(a::QQFieldElem, b::Float64)
  return Rational(a)*b
end

function *(b::Float64, a::QQFieldElem)
  return Rational(a)*b
end

function Float64(a::QQFieldElem)
  b = a*ZZRingElem(2)^53
  Float64(div(numerator(b), denominator(b)))/(Float64(2)^53) #CF 2^53 is bad in 32bit
end

function convert(R::Type{Rational{Base.GMP.BigInt}}, a::Nemo.ZZRingElem)
  return R(BigInt(a))
end

log(a::ZZRingElem) = log(BigInt(a))
log(a::QQFieldElem) = log(numerator(a)) - log(denominator(a))

one(::ZZRingElem) = ZZRingElem(1)
zero(::ZZRingElem) = ZZRingElem(0)

isinteger(::ZZRingElem) = true
isfinite(::ZZRingElem) = true

Integer(a::ZZRingElem) = BigInt(a)

function divisible(x::Integer, y::Integer)
  return iszero(rem(x, y))
end

@doc raw"""
    modord(a::ZZRingElem, m::ZZRingElem) -> Int
    modord(a::Integer, m::Integer)

  The multiplicative order of a modulo $m$ (not a good algorithm).
"""
function modord(a::ZZRingElem, m::ZZRingElem)
  gcd(a,m)!=1 && error("1st argument not a unit")
  i = 1
  b = a % m
  while b != 1
    i += 1
    b = b*a % m
  end
  return i
end

function modord(a::Integer, m::Integer)
  gcd(a,m)!=1 && error("1st argument not a unit")
  i = 1
  b = a % m
  while b != 1
    i += 1
    b = b*a % m
  end
  return i
end


if Nemo.version() <= v"0.15.1"
  function isodd(a::ZZRingElem)
    ccall((:fmpz_is_odd, libflint), Int, (Ref{ZZRingElem},), a) == 1
  end

  function iseven(a::ZZRingElem)
    ccall((:fmpz_is_even, libflint), Int, (Ref{ZZRingElem},), a) == 1
  end
end

function neg!(a::ZZRingElem)
  ccall((:fmpz_neg, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}), a, a)
  return a
end

##
## Ranges
##
# Note, we cannot get a UnitRange as this is only legal for subtypes of Real.
# So, we use an AbstractUnitRange here mostly copied from `base/range.jl`.
# `StepRange`s on the other hand work out of the box thanks to duck typing.

struct fmpzUnitRange <: AbstractUnitRange{ZZRingElem}
  start::ZZRingElem
  stop::ZZRingElem
  fmpzUnitRange(start, stop) = new(start, fmpz_unitrange_last(start, stop))
end
fmpz_unitrange_last(start::ZZRingElem, stop::ZZRingElem) =
  ifelse(stop >= start, stop, start - one(ZZRingElem))

Base.:(:)(a::ZZRingElem, b::ZZRingElem) = fmpzUnitRange(a, b)

@inline function getindex(r::fmpzUnitRange, i::ZZRingElem)
    val = r.start + (i - 1)
    @boundscheck _in_unit_range(r, val) || throw_boundserror(r, i)
    val
end
_in_unit_range(r::fmpzUnitRange, val::ZZRingElem) = r.start <= val <= r.stop

show(io::IO, r::fmpzUnitRange) = print(io, repr(first(r)), ':', repr(last(r)))

in(x::IntegerUnion, r::fmpzUnitRange) = first(r) <= x <= last(r)

in(x::IntegerUnion, r::AbstractRange{ZZRingElem}) =
  !isempty(r) && first(r) <= x <= last(r) &&
    mod(convert(ZZRingElem,x),step(r)) == mod(first(r),step(r))

mod(i::IntegerUnion, r::fmpzUnitRange) = mod(i-first(r), length(r)) + first(r)

Base.:(:)(a::ZZRingElem, b::Integer) = (:)(promote(a,b)...)
Base.:(:)(a::Integer, b::ZZRingElem) = (:)(promote(a,b)...)

# Construct StepRange{ZZRingElem, T} where +(::ZZRingElem, zero(::T)) must be defined
Base.:(:)(a::ZZRingElem, s, b::Integer) = ((a_,b_)=promote(a,b); a_:s:b_)
Base.:(:)(a::Integer, s, b::ZZRingElem) = ((a_,b_)=promote(a,b); a_:s:b_)

#TODO
# need to be mapped onto proper Flint primitives
# flints needs a proper interface to randomness - I think
# currently one simply cannot use it at all
#
# should be tied(?) to the Julia rng stuff?
# similarly, all the derived rand functions should probably also do this
#
# inspired by/copied from a former BigInt implementation from the stdlib in
# `Random/src/generation.jl`
#

function rand(rng::AbstractRNG, a::fmpzUnitRange)
  m = Base.last(a) - Base.first(a)
  m < 0 && error("range empty")
  nd = ndigits(m, 2)
  nl, high = divrem(nd, 8*sizeof(Base.GMP.Limb))
  if high>0
    mask = m>>(nl*8*sizeof(Base.GMP.Limb))
  end
  s = ZZRingElem(0)
  while true
    s = ZZRingElem(0)
    for i=1:nl
      s = s << (8*sizeof(Base.GMP.Limb))
      s += rand(rng, Base.GMP.Limb)
    end
    if high >0
      s = s << high
      s += rand(rng, 0:Base.GMP.Limb(mask))
    end
    if s <= m break; end
  end
  return s + first(a)
end

struct RangeGeneratorfmpz# <: Base.Random.RangeGenerator
  a::StepRange{ZZRingElem, ZZRingElem}
end

function Random.RangeGenerator(r::StepRange{ZZRingElem,ZZRingElem})
    m = last(r) - first(r)
    m < 0 && throw(ArgumentError("range must be non-empty"))
    return RangeGeneratorfmpz(r)
end

function rand(rng::AbstractRNG, g::RangeGeneratorfmpz)
  return rand(rng, g.a)
end

function Base.getindex(a::StepRange{ZZRingElem,ZZRingElem}, i::ZZRingElem)
  a.start+(i-1)*Base.step(a)
end

function Base.divrem(a::ZZRingElem, b::Int)
  return (div(a, b), rem(a, b))
end

############################################################
# more unsafe function that Bill does not want to have....
############################################################


function mod!(z::ZZRingElem, x::ZZRingElem, y::ZZRingElem)
  ccall((:fmpz_mod, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), z, x, y)
  return z
end

function divexact!(z::ZZRingElem, x::ZZRingElem, y::ZZRingElem)
  iszero(y) && throw(DivideError())
  ccall((:fmpz_divexact, libflint), Nothing,
        (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), z, x, y)
  return z
end

function lcm!(z::ZZRingElem, x::ZZRingElem, y::ZZRingElem)
   ccall((:fmpz_lcm, libflint), Nothing,
         (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), z, x, y)
   return z
end

function gcd!(z::ZZRingElem, x::ZZRingElem, y::ZZRingElem)
   ccall((:fmpz_gcd, libflint), Nothing,
         (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), z, x, y)
   return z
end

################################################################################
#
#  power detection
#
################################################################################
#compare to Oscar/examples/PerfectPowers.jl which is, for large input,
#far superiour over gmp/ fmpz_is_perfect_power

@doc raw"""
    is_power(a::ZZRingElem) -> Int, ZZRingElem
    is_power(a::Integer) -> Int, Integer

Returns $e$, $r$ such that $a = r^e$ with $e$ maximal. Note: $1 = 1^0$.
"""
function is_power(a::ZZRingElem)
  if iszero(a)
    error("must not be zero")
  end
  if isone(a)
    return 0, a
  end
  if a < 0
    e, r = is_power(-a)
    if isone(e)
      return 1, a
    end
    v, s = iszero(e) ? (0, 0) : remove(e, 2)
    return s, -r^(2^v)
  end
  rt = ZZRingElem()
  e = 1
  while true
    ex = ccall((:fmpz_is_perfect_power, libflint), Int, (Ref{ZZRingElem}, Ref{ZZRingElem}), rt, a)
    if ex == 1 || ex == 0
      return e, a
    end
    e *= ex
    a = rt
  end
end

function is_power(a::Integer)
  e, r = is_power(ZZRingElem(a))
  return e, typeof(a)(r)
end

@doc raw"""
    is_power(a::QQFieldElem) -> Int, QQFieldElem
    is_power(a::Rational) -> Int, Rational

Writes $a = r^e$ with $e$ maximal. Note: $1 = 1^0$.
"""
function is_power(a::QQFieldElem)
  e, r = is_power(numerator(a))
  if e==1
    return e, a
  end
  f, s = is_power(denominator(a))
  g = gcd(e, f)
  return g, r^div(e, g)//s^div(f, g)
end

function is_power(a::Rational)
  T = typeof(denominator(a))
  e, r = is_power(QQFieldElem(a))
  return e, T(numerator(r))//T(denominator(r))
end

@doc raw"""
    is_power(a::ZZRingElem, n::Int) -> Bool, ZZRingElem
    is_power(a::QQFieldElem, n::Int) -> Bool, QQFieldElem
    is_power(a::Integer, n::Int) -> Bool, Integer

Tests if $a$ is an $n$-th power. Return `true` and the root if successful.
"""
function is_power(a::ZZRingElem, n::Int)
   if a < 0 && iseven(n)
    return false, a
  end
  b = iroot(a, n)
  return b^n == a, b
end

function is_power(a::QQFieldElem, n::Int)
  fl, nu = is_power(numerator(a), n)
  if !fl
    return fl, a
  end
  fl, de = is_power(denominator(a), n)
  return fl, QQFieldElem(nu, de)
end

################################################################################
#
#  Chinese remaindering modulo UInts to ZZRingElem
#
################################################################################

mutable struct fmpz_comb
  primes::Ptr{UInt}
  num_primes::Int
  n::Int
  comb::Ptr{Ptr{ZZRingElem}}
  res::Ptr{Ptr{ZZRingElem}}
  mod_n::UInt
  mod_ninv::UInt
  mod_norm::UInt

  function fmpz_comb(primes::Vector{UInt})
    z = new()
    ccall((:fmpz_comb_init, libflint), Nothing, (Ref{fmpz_comb}, Ptr{UInt}, Int),
            z, primes, length(primes))
    finalizer(_fmpz_comb_clear_fn, z)
    return z
  end
end

function _fmpz_comb_clear_fn(z::fmpz_comb)
  ccall((:fmpz_comb_clear, libflint), Nothing, (Ref{fmpz_comb}, ), z)
end

mutable struct fmpz_comb_temp
  n::Int
  comb_temp::Ptr{Ptr{ZZRingElem}}
  temp::Ptr{ZZRingElem}
  temp2::Ptr{ZZRingElem}

  function fmpz_comb_temp(comb::fmpz_comb)
    z = new()
    ccall((:fmpz_comb_temp_init, libflint), Nothing,
            (Ref{fmpz_comb_temp}, Ref{fmpz_comb}), z, comb)
    finalizer(_fmpz_comb_temp_clear_fn, z)
    return z
  end
end

function _fmpz_comb_temp_clear_fn(z::fmpz_comb_temp)
  ccall((:fmpz_comb_temp_clear, libflint), Nothing, (Ref{fmpz_comb_temp}, ), z)
end


function fmpz_multi_crt_ui!(z::ZZRingElem, a::Vector{UInt}, b::fmpz_comb, c::fmpz_comb_temp)
  ccall((:fmpz_multi_CRT_ui, libflint), Nothing,
          (Ref{ZZRingElem}, Ptr{UInt}, Ref{fmpz_comb}, Ref{fmpz_comb_temp}, Cint),
          z, a, b, c, 1)
  return z
end

function _fmpz_preinvn_struct_clear_fn(z::fmpz_preinvn_struct)
  ccall((:fmpz_preinvn_clear, libflint), Nothing, (Ref{fmpz_preinvn_struct}, ), z)
end

function fdiv_qr_with_preinvn!(q::ZZRingElem, r::ZZRingElem, g::ZZRingElem, h::ZZRingElem, hinv::fmpz_preinvn_struct)
  ccall((:fmpz_fdiv_qr_preinvn, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{fmpz_preinvn_struct}), q, r, g, h, hinv)
end

function submul!(z::ZZRingElem, x::ZZRingElem, y::ZZRingElem)
  ccall((:fmpz_submul, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), z, x, y)
end

################################################################################
#
#  Number of bits
#
################################################################################


@doc raw"""
    nbits(a::Integer) -> Int

  Returns the number of bits necessary to represent $a$.
"""
function nbits(a::Integer)
  return ndigits(a, base=2)
end


################################################################################
#
#  Modular reduction with symmetric residue system
#
################################################################################

function mod_sym(a::ZZRingElem, b::ZZRingElem)
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

@doc raw"""
    isinteger(a::QQFieldElem) -> Bool

Returns `true` iff the denominator of $a$ is one.
"""
function isinteger(a::QQFieldElem)
  return isone(denominator(a))
end

################################################################################
#
#  sunit group
#
################################################################################

mutable struct MapSUnitGrpZFacElem <: Map{GrpAbFinGen, FacElemMon{QQField}, HeckeMap, MapSUnitGrpZFacElem}
  header::MapHeader{GrpAbFinGen, FacElemMon{QQField}}
  idl::Vector{ZZRingElem}

  function MapSUnitGrpZFacElem()
    return new()
  end
end

function show(io::IO, mC::MapSUnitGrpZFacElem)
  println(io, "SUnits (in factored form) map of $(codomain(mC)) for $(mC.idl)")
end

mutable struct MapSUnitGrpZ <: Map{GrpAbFinGen, QQField, HeckeMap, MapSUnitGrpZ}
  header::MapHeader{GrpAbFinGen, QQField}
  idl::Vector{ZZRingElem}

  function MapSUnitGrpZ()
    return new()
  end
end

function show(io::IO, mC::MapSUnitGrpZ)
  println(io, "SUnits map of $(codomain(mC)) for $(mC.idl)")
end

@doc raw"""
    sunit_group_fac_elem(S::Vector{ZZRingElem}) -> GrpAbFinGen, Map
    sunit_group_fac_elem(S::Vector{Integer}) -> GrpAbFinGen, Map

The $S$-unit group of $Z$ supported at $S$: the group of
rational numbers divisible only by primes in $S$.
The second return value is the map mapping group elements to rationals
in factored form or rationals back to group elements.
"""
function sunit_group_fac_elem(S::Vector{T}) where T <: Integer
  return sunit_group_fac_elem(ZZRingElem[x for x=S])
end

function sunit_group_fac_elem(S::Vector{ZZRingElem})
  S = coprime_base(S)  #TODO: for S-units use factor???
  G = abelian_group(vcat(ZZRingElem[2], ZZRingElem[0 for i=S]))
  S = vcat(ZZRingElem[-1], S)

  mp = MapSUnitGrpZFacElem()
  mp.idl = S

  Sq = QQFieldElem[x for x=S]

  function dexp(a::GrpAbFinGenElem)
    return FacElem(Sq, ZZRingElem[a.coeff[1,i] for i=1:length(S)])
  end

  mp.header = MapHeader(G, FacElemMon(FlintQQ), dexp)

  return G, mp
end

function preimage(f::MapSUnitGrpZFacElem, a::ZZRingElem)
  g = Int[a>=0 ? 0 : 1]
  S = f.idl
  g = vcat(g, Int[valuation(a, x) for x=S[2:end]])
  return domain(f)(g)
end

function preimage(f::MapSUnitGrpZFacElem, a::Integer)
  return preimage(f, ZZRingElem(a))
end

function preimage(f::MapSUnitGrpZFacElem, a::Rational)
  return preimage(f, QQFieldElem(a))
end

function preimage(f::MapSUnitGrpZFacElem, a::QQFieldElem)
  return preimage(f, numerator(a)) - preimage(f, denominator(a))
end

function preimage(f::MapSUnitGrpZFacElem, a::FacElem)
  return sum(GrpAbFinGenElem[e*preimage(f, k) for (k,e) = a.fac])
end

@doc raw"""
    sunit_group(S::Vector{ZZRingElem}) -> GrpAbFinGen, Map
    sunit_group(S::Vector{Integer}) -> GrpAbFinGen, Map

The $S$-unit group of $Z$ supported at $S$: the group of
rational numbers divisible only by primes in $S$.
The second return value is the map mapping group elements to rationals
or rationals back to group elements.
"""
function sunit_group(S::Vector{T}) where T <: Integer
  return sunit_group(ZZRingElem[x for x=S])
end

function sunit_group(S::Vector{ZZRingElem})
  u, mu = sunit_group_fac_elem(S)

  mp = MapSUnitGrpZ()
  mp.idl = S

  function dexp(a::GrpAbFinGenElem)
    return evaluate(image(mu, a))
  end

  mp.header = MapHeader(u, FlintQQ, dexp, mu.header.preimage)

  return u, mp
end

@doc raw"""
    is_prime_power(n::ZZRingElem) -> Bool
    is_prime_power(n::Integer) -> Bool

Tests if $n$ is the exact power of a prime number.
"""
function is_prime_power(n::ZZRingElem)
  e, p = is_power(n)
  return is_prime(p)
end

function is_prime_power(n::Integer)
  return is_prime_power(ZZRingElem(n))
end

################################################################################
# random and factor
################################################################################

factor(a...; b...) = Nemo.factor(a...; b...)

factor(a::Integer) = factor(ZZRingElem(a))

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
  A.a = ccall((:flint_rand_alloc, libflint), Ptr{Nothing}, (Int, ), 1)
  ccall((:flint_randinit, libflint), Nothing, (Ptr{Nothing}, ), A.a)

  function clean_rand_state(A::flint_rand_ctx_t)
    ccall((:flint_randclear, libflint), Nothing, (Ptr{Nothing}, ), A.a)
    ccall((:flint_rand_free, libflint), Nothing, (Ptr{Nothing}, ), A.a)
    nothing
  end
  finalizer(clean_rand_state, A)
  return A
end

global flint_rand_ctx

function ecm(a::ZZRingElem, B1::UInt, B2::UInt, ncrv::UInt, rnd = flint_rand_ctx)
  f = ZZRingElem()
  r = ccall((:fmpz_factor_ecm, libflint), Int32, (Ref{ZZRingElem}, UInt, UInt, UInt, Ptr{Nothing}, Ref{ZZRingElem}), f, ncrv, B1, B2, rnd.a, a)
  return r, f
end

function ecm(a::ZZRingElem, B1::Int, B2::Int, ncrv::Int, rnd = flint_rand_ctx)
  return ecm(a, UInt(B1), UInt(B2), UInt(ncrv), rnd)
end

#data from http://www.mersennewiki.org/index.php/Elliptic_Curve_Method
B1 = [2, 11, 50, 250, 1000, 3000, 11000, 43000, 110000, 260000, 850000, 2900000];
nC = [25, 90, 300, 700, 1800, 5100, 10600, 19300, 49000, 124000, 210000, 340000];

function ecm(a::ZZRingElem, max_digits::Int = div(ndigits(a), 3), rnd = flint_rand_ctx)
  n = ndigits(a, 10)
  B1s = 15

  i = 1
  s = max(div(max_digits - 10, 5), 1)
  #i = s = max(i, s)
  while i <= s
    e, f = ecm(a, B1[i]*1000, B1[i]*1000*100, nC[i], rnd)
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

function factor_trial_range(N::ZZRingElem, start::Int=0, np::Int=10^5)
   F = Nemo.fmpz_factor()
   ccall((:fmpz_factor_trial_range, libflint), Nothing, (Ref{Nemo.fmpz_factor}, Ref{ZZRingElem}, UInt, UInt), F, N, start, np)
   res = Dict{ZZRingElem, Int}()
   for i in 1:F.num
     z = ZZRingElem()
     ccall((:fmpz_factor_get_fmpz, libflint), Nothing,
           (Ref{ZZRingElem}, Ref{Nemo.fmpz_factor}, Int), z, F, i - 1)
     res[z] = unsafe_load(F.exp, i)
   end
   return res, canonical_unit(N)
end

const big_primes = ZZRingElem[]

function factor(N::ZZRingElem)
  if iszero(N)
    throw(ArgumentError("Argument is not non-zero"))
  end
  N_in = N
  global big_primes
  r, c = factor_trial_range(N)
  for (p, v) = r
    N = divexact(N, p^v)
  end
  if is_unit(N)
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

function factor_insert!(r::Dict{ZZRingElem, Int}, N::ZZRingElem, scale::Int = 1)
  #assumes N to be positive
  #        no small divisors
  #        no big_primes
  if isone(N)
    return r
  end
  fac, N = is_power(N)
  if fac > 1
    return factor_insert!(r, N, fac)
  end
  if is_prime(N)
    @assert !haskey(r, N)
    r[N] = scale
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
  cp = coprime_base([N, f])
  for i = cp
    factor_insert!(r, i, scale*valuation(N, i))
  end
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

function _factors_trial_division(n::ZZRingElem, np::Int = 10^5)
  res, u = factor_trial_range(n, 0, np)
  factors = ZZRingElem[]
  for (p, v) in res
    push!(factors, p)
    n = divexact(n, p^v)
  end
  return factors, n

end

function ceil(::Type{ZZRingElem}, a::BigFloat)
  return ZZRingElem(ceil(BigInt, a))
end

function ceil(::Type{Int}, a::QQFieldElem)
  return Int(ceil(ZZRingElem, a))
end

function floor(::Type{ZZRingElem}, a::BigFloat)
  return ZZRingElem(floor(BigInt, a))
end

function floor(::Type{Int}, a::QQFieldElem)
  return Int(floor(ZZRingElem, a))
end

function round(::Type{ZZRingElem}, a::BigFloat)
  return ZZRingElem(round(BigInt, a))
end

function round(::Type{Int}, a::BigFloat)
  return Int(round(ZZRingElem, a))
end

/(a::BigFloat, b::ZZRingElem) = a/BigInt(b)

function rand!(A::Vector{ZZRingElem}, v::StepRange{ZZRingElem, ZZRingElem})
  for i in 1:length(A)
    A[i] = rand(v)
  end
  return A
end

Base.isless(a::Int, b::ZZRingElem) = a < b

Base.isless(a::ZZRingElem, b::Int) = a < b

function (::Type{Base.Rational{BigInt}})(x::QQFieldElem)
  return Rational{BigInt}(BigInt(numerator(x)), BigInt(denominator(x)))
end

export euler_phi_inv, Divisors, carmichael_lambda

@doc raw"""
    Divisors{T}

An iterator for the divisors of a given object.
Create using
    `Divisors(A, power::Int = 1)`
where $A$ is either a FacElem or a direct element. Power can be used
to restrict to objects $B$ s.th. $B$^power still divides $A$, e.g.
    `Divisors(12, powers = 2)`
will produce square divisors.

For rings where this makes sense, i.e. where the unit group is finite,
```units = true``` can be passed in to also take into account
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
        push!(r.lf, T(p), k)
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

  function Divisors(a::FacElem{ZZRingElem, ZZRing}; units::Bool = false, power::Int = 1)
    r = new{ZZRingElem}()
    r.n = evaluate(a)
    r.lf = MSet{ZZRingElem}()
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
  function Divisors(a::Fac{ZZRingElem}; units::Bool = false, power::Int = 1)
    return Divisors(FacElem(a), units = units, power = power)
  end
end
Base.IteratorSize(::Divisors) = Base.HasLength()
Base.length(D::Divisors) = length(D.s)
Base.eltype(::Divisors{T}) where T = T

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

@doc raw"""
    unit_group(::ZZRing) -> GrpAbFinGen, Map

The unit group of $\mathbb{Z}$, i.e. $C_2$ and the map translating between the group and $\mathbb{Z}$.
"""
function unit_group(::ZZRing)
  G = abelian_group([2])
  exp = function(z::GrpAbFinGenElem)
    return isodd(z[1]) ? ZZRingElem(-1) : ZZRingElem(1)
  end
  log = function(z::ZZRingElem)
    return z == -1 ? G[1] : G[0]
  end
  return G, MapFromFunc(exp, log, G, FlintZZ)
end

@doc raw"""
    unit_group(::Integers{T}) -> GrpAbFinGen, Map

The unit group of , i.e. $C_2$ and the map translating between the group and $\mathbb{Z}$.
"""
function unit_group(R::AbstractAlgebra.Integers{T}) where {T}
  G = abelian_group([2])
  exp = function(z::GrpAbFinGenElem)
    return isodd(z[1]) ? T(-1) : T(1)
  end
  log = function(z::T)
    return z == -1 ? G[1] : G[0]
  end
  return G, MapFromFunc(exp, log, G, R)
end

#Nemo.fpField = zzModRingElem?
# PolyRing

#basically from
#http://people.math.gatech.edu/~ecroot/shparlinski_final.pdf
#Contini, Croot, Shparlinski: Complexity of inverting the Euler function
@doc raw"""
    euler_phi_inv_fac_elem(n::ZZRingElem)

The inverse of the Euler totient functions: find all $x$ s.th. $phi(x) = n$
holds. The elements are returned in factored form.
"""
function euler_phi_inv_fac_elem(n::ZZRingElem)
  lp = ZZRingElem[]
  for d = Divisors(n)
    if is_prime(d+1)
      push!(lp, d+1)
    end
  end
#  println("possible primes: ", lp)

  E = Tuple{ZZRingElem, Vector{Tuple{ZZRingElem, Int}}}[]
  res = FacElem{ZZRingElem, ZZRing}[]
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

#phi(n) < n and n/phi(n) can be arbitrarily large.
#whowever, prod(p/(p-1) for p = PrimesSet(1, 1000000)) < 25
#so for 32-bit input, the output is also small
function euler_phi_inv(n::Int)
  @assert n>0
  T = Int
  if nbits(n) > 55 #to be safe...
    return T[T(x) for x = euler_phi_inv(ZZ(n))]
  end
  lp = T[]
  for d = Divisors(n)
    if is_prime(d+1)
      push!(lp, d+1)
    end
  end
#  println("possible primes: ", lp)

  E = Tuple{T, T, T}[]
  res = T[]
  for p = lp
    v = valuation(n, p)
    push!(E, (p-1, p, p))
    if n == p-1
      push!(res, p)
    end
    for i=1:v
      push!(E, (p*E[end][1], p*E[end][2], p))
      if E[end][1] == n
        push!(res, prod(E[end][2]))
      end
    end
  end
  while true
    F = Tuple{T, T, T}[]
    for e = E
      nn = divexact(n, e[1])
      pm = e[3]
      for p = lp
        if p <= pm
          continue
        end
        if nn % (p-1) == 0
          v = valuation(nn, p)
          push!(F, (e[1]*(p-1), e[2]*p, p))
          if F[end][1] == n
            push!(res, F[end][2])
          end
          for i = 1:v
            push!(F, (p*F[end][1], p*F[end][2], p))
            if F[end][1] == n
              push!(res, F[end][2])
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


function euler_phi(x::Fac{ZZRingElem})
  return prod((p-1)*p^(v-1) for (p,v) = x.fac)
end

function euler_phi(x::FacElem{ZZRingElem, ZZRing})
  x = factor(x)
  return prod((p-1)*p^(v-1) for (p,v) = x.fac)
end

function carmichael_lambda(x::Fac{ZZRingElem})
  two = ZZRingElem(2)
  if haskey(x.fac, two)
    y = deepcopy(x.fac)
    v = y[two]
    delete!(y, two)
    if v == 2
      c = two
    elseif v > 2
      c = two^(v-2)
    else
      c = ZZRingElem(1)
    end
  else
    c = ZZRingElem(1)
    y = x.fac
  end
  if length(y) == 0
    return c
  end
  return lcm(c, reduce(lcm, (p-1)*p^(v-1) for (p,v) = y))
end

function carmichael_lambda(x::ZZRingElem)
  v, x = remove(x, ZZRingElem(2))
  if isone(x)
    c = ZZRingElem(1)
  else
    x = factor(x)
    c = reduce(lcm, (p-1)*p^(v-1) for (p,v) = x.fac)
  end
  if v == 2
    c = lcm(2, c)
  elseif v > 2
    c = lcm(ZZRingElem(2)^(v-2), c)
  end
  return c
end

function carmichael_lambda(x::FacElem{ZZRingElem, ZZRing})
  x = factor(x)
  return carmichael_lambda(x)
end

function carmichael_lambda(n::T) where {T <: Integer}
  return T(carmichael_lambda(ZZRingElem(n)))
end

@doc raw"""
    euler_phi_inv(n::Integer) -> Vector{ZZRingElem}

The inverse of the Euler totient functions: find all $x$ s.th. $phi(x) = n$
holds.
"""
function euler_phi_inv(n::Integer)
  return euler_phi_inv(ZZRingElem(n))
end

@doc raw"""
    euler_phi_inv(n::ZZRingElem) -> Vector{ZZRingElem}

The inverse of the Euler totient functions: find all $x$ s.th. $phi(x) = n$
holds.
"""
function euler_phi_inv(n::ZZRingElem)
  return [ evaluate(x) for x = euler_phi_inv_fac_elem(n)]
end

function factor(a::FacElem{ZZRingElem, ZZRing})
  b = simplify(a)
  c = Dict{ZZRingElem, Int}()
  s = ZZRingElem(1)
  for (p,k) = b.fac
    lp = factor(p)
    s *= lp.unit
    for (q,w) = lp.fac
      c[q] = w*k
    end
  end
  l = Fac{ZZRingElem}()
  l.fac = c
  l.unit = s
  return l
end

function FacElem(a::Fac{ZZRingElem})
  f = FacElem(a.fac)
  if a.unit == -1
    return a.unit * f
  end
  return f
end

#= for torsion units:

   [maximum([maximum(vcat([ZZRingElem(-1)], euler_phi_inv(x))) for x = Divisors(ZZRingElem(n))]) for n = 1:250]

=#

radical(a::ZZRingElem) = prod(keys(factor(a).fac))
function radical(a::T) where {T <: Integer}
  return T(radical(ZZRingElem(a)))
end

function quo(::ZZRing, a::ZZRingElem)
  R = residue_ring(FlintZZ, a)
  f = MapFromFunc(x -> R(x), y->lift(y), FlintZZ, R)
  return R, f
end

function quo(::ZZRing, a::Integer)
  R = residue_ring(FlintZZ, a)
  f = MapFromFunc(x -> R(x), y->lift(y), FlintZZ, R)
  return R, f
end

function (::ZZRing)(x::Rational{Int})
  @assert denominator(x) == 1
  return ZZRingElem(numerator(x))
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
  a::ZZRingElem
  len::Int
  b::Ptr{UInt}
  function Limbs(a::ZZRingElem; MSW::Bool = true)
    if Nemo._fmpz_is_small(a)
      return new(a, 0, convert(Ptr{UInt}, 0))
    end
    z = convert(Ptr{Cint}, unsigned(a.d)<<2)
    len = unsafe_load(z, 2)
    d = convert(Ptr{Ptr{UInt}}, unsigned(a.d) << 2) + 2*sizeof(Cint)
    p = unsafe_load(d)
    if !MSW
      new(a, -len, p)
    else
      new(a, len, p)
    end
  end
end

function show(io::IO, L::Limbs)
  print(io, "limb-access for: ", L.a)
end

@inline function getindex(L::Limbs, i::Int)
  if L.len == 0
    return UInt(abs(L.a.d)) #error???
  end
  @boundscheck @assert i <= abs(L.len)
  return unsafe_load(L.b, i)
end

function iterate(L::Limbs)
  L.len < 0 && return L[1], 1

  return L[L.len], L.len
end

function iterate(L::Limbs, i::Int)
  if L.len < 0
    i > -L.len && return nothing
    return L[i+1], i+1
  end
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

  function BitsFmpz(b::ZZRingElem)
    return new(Limbs(b))
  end
end

function iterate(B::BitsFmpz)
  L = B.L
  a = L[L.len]
  b = UInt(1) << (nbits(a)-1)
  return true, (b, L.len)
end

@inline function iterate(B::BitsFmpz, s::Tuple{UInt, Int})
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

bits(a::ZZRingElem) = BitsFmpz(a)
#= wrong order, thus disabled

function getindex(B::BitsFmpz, i::Int)
  return ccall((:fmpz_tstbit, libflint), Int, (Ref{ZZRingElem}, Int), B.L.a, i) != 0
end
=#

end

using .BitsMod
export bits, Limbs

^(a::T, n::IntegerUnion) where {T <: RingElem} = _generic_power(a, n)

^(a::NfAbsOrdIdl, n::IntegerUnion)  = _generic_power(a, n)

#^(a::NfRelOrdIdl, n::IntegerUnion)  = _generic_power(a, n)
is_negative(n::IntegerUnion) = cmp(n, 0) < 0
is_positive(n::IntegerUnion) = cmp(n, 0) > 0

function _generic_power(a, n::IntegerUnion)
  fits(Int, n) && return a^Int(n)
  if is_negative(n)
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

#square-and-multiply algorithm to compute f^e mod g
function powermod(f::T, e::ZZRingElem, g::T) where {T}
    #small exponent -> use powermod
    if nbits(e) <= 63
        return powermod(f, Int(e), g)
    else
        #go through binary representation of exponent and multiply with res
        #or (res and f)
        res = parent(f)(1)
        for b=bits(e)
            res = mod(res^2, g)
            if b
                res = mod(res*f, g)
            end
        end
        return res
    end
end


################################################################################
#
#  Prime numbers up to
#
################################################################################

@doc raw"""
    primes_up_to(n::Int) -> Vector{Int}

Returns a vector containing all the prime numbers up to $n$.
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

@doc raw"""
    squarefree_up_to(n::Int) -> Vector{Int}

Returns a vector containing all the squarefree numbers up to $n$.
"""
function squarefree_up_to(n::Int; coprime_to::Vector{ZZRingElem} = ZZRingElem[], prime_base::Vector{ZZRingElem} = ZZRingElem[])

  @assert isempty(coprime_to) || isempty(prime_base)
  if !isempty(prime_base)
    listi = Int[1]
    for x in prime_base
      if x > n
        continue
      end
      el = Int(x)
      to_add = Int[]
      for i = 1:length(listi)
        eln = el * listi[i]
        if eln <= n
          push!(to_add, eln)
        else
          break
        end
      end
      append!(listi, to_add)
      sort!(listi)
    end
    return listi
  end
  list = trues(n)
  for x in coprime_to
    if x > n
      continue
    end
    t = Int(x)
    while t <= n
      list[t] = false
      t += Int(x)
    end
  end
  i = 2
  b = isqrt(n)
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
#  is_squarefree
#
################################################################################

#TODO (Hard): Implement this properly.
@doc raw"""
    is_squarefree(n::Union{Int, ZZRingElem}) -> Bool

Returns true if $n$ is squarefree, false otherwise.
"""
function is_squarefree(n::Union{Int,ZZRingElem})
  if iszero(n)
    error("Argument must be non-zero")
  end
  if isone(abs(n))
    return true
  end
  e, b = is_power(n)
  if e > 1
    return false
  end
  return isone(maximum(values(factor(n).fac)))
end

################################################################################
#
#  Rounding and friends
#
################################################################################

Base.floor(::Type{ZZRingElem}, x::ZZRingElem) = x

Base.ceil(::Type{ZZRingElem}, x::ZZRingElem) = x

Base.floor(::Type{ZZRingElem}, x::Int) = ZZRingElem(x)

Base.ceil(::Type{ZZRingElem}, x::Int) = ZZRingElem(x)

Base.floor(::Type{ZZRingElem}, x::QQFieldElem) = fdiv(numerator(x), denominator(x))

Base.ceil(::Type{ZZRingElem}, x::QQFieldElem) = cdiv(numerator(x), denominator(x))

Base.round(x::QQFieldElem, ::RoundingMode{:Up}) = ceil(x)

Base.round(::Type{ZZRingElem}, x::QQFieldElem, ::RoundingMode{:Up}) = ceil(ZZRingElem, x)

Base.round(x::QQFieldElem, ::RoundingMode{:Down}) = floor(x)

Base.round(::Type{ZZRingElem}, x::QQFieldElem, ::RoundingMode{:Down}) = floor(ZZRingElem, x)

function Base.round(x::QQFieldElem, ::RoundingMode{:Nearest})
  d = denominator(x)
  n = numerator(x)
  if d == 2
    if mod(n, 4) == 1
      if n > 0
        return div(n, d)
      else
        return div(n, d) - 1
      end
    else
      if n > 0
        return div(n, d) + 1
      else
        return div(n, d)
      end
    end
  end

  return floor(x + 1//2)
end

Base.round(x::QQFieldElem, ::RoundingMode{:NearestTiesAway}) = sign(x) * floor(abs(x) + 1//2)

Base.round(::Type{ZZRingElem}, x::QQFieldElem, ::RoundingMode{:NearestTiesAway}) = sign(x) == 1 ? floor(ZZRingElem, abs(x) + 1//2) : -floor(ZZRingElem, abs(x) + 1//2)

function Base.round(::Type{ZZRingElem}, a::QQFieldElem)
  return round(ZZRingElem, a, RoundNearestTiesAway)
end

function Base.round(a::QQFieldElem)
  return round(ZZRingElem, a)
end

################################################################################
#
#  Squarefree part
#
################################################################################

@doc raw"""
    squarefree_part(a::ZZRingElem) -> ZZRingElem

Returns the squarefee part $b$ of $a$, which is the smallest (absolute value)
integer $b$ such that $a/b$ is positive and squarefree.
"""
function squarefree_part(a::ZZRingElem)
  f = factor(a)
  s = sign(a)
  for (p, e) in f
    if isodd(e)
      s = s * p
    end
  end
  return s
end

################################################################################
#
#  Factorization of a rational
#
################################################################################

@doc raw"""
    factor(a::QQFieldElem, ::ZZRing) -> Fac{ZZRingElem}

Factor the rational number $a$ into prime numbers.
"""
function factor(a::QQFieldElem, ::ZZRing)
  fn = factor(numerator(a))
  fd = factor(denominator(a))
  for (p, e) = fd
    fn.fac[p] = -e
  end
  return fn
end

#missing in Nemo...
Hecke.clog(a::Int, b::Int) = clog(ZZRingElem(a), b)

################################################################################
#
#   Support
#
################################################################################

function support(d::ZZRingElem)
  return collect(keys(factor(d).fac))
end

function support(a::QQFieldElem)
  d = denominator(a)
  n = numerator(a)
  res = ZZRingElem[]
  for (p, _) in factor(d)
    push!(res, p)
  end
  for (p, _) in factor(n)
    push!(res, p)
  end
  return res
end

