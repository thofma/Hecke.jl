################################################################################
#
#  Integer functions
#
################################################################################

function rem(a::fmpz, b::UInt)
  return ccall((:fmpz_fdiv_ui, libflint), UInt, (Ref{fmpz}, UInt), a, b)
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

function remove!(a::fmpz, b::fmpz)
  v = ccall((:fmpz_remove, libflint), Clong, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), a, a, b)
  return v, a
end

function remove!(a::fmpq, b::fmpz)
  nr = ccall((:fmpq_numerator_ptr, libflint), Ptr{fmpz}, (Ref{fmpq}, ), a)
  vn = ccall((:fmpz_remove, libflint), Clong, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), nr, nr, b)
  #fmpq's are simplified: either num OR den will be non-trivial
  if vn != 0
    return vn, a
  end
  nr = ccall((:fmpq_denominator_ptr, libflint), Ptr{fmpz}, (Ref{fmpq}, ), a)
  vn = ccall((:fmpz_remove, libflint), Clong, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), nr, nr, b)
  return -vn, a
end

function valuation!(a::fmpq, b::fmpz)
  nr = ccall((:fmpq_numerator_ptr, libflint), Ptr{fmpz}, (Ref{fmpq}, ), a)
  vn = ccall((:fmpz_remove, libflint), Clong, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), nr, nr, b)
  #fmpq's are simplified: either num OR den will be non-trivial
  if vn != 0
    return vn
  end
  nr = ccall((:fmpq_denominator_ptr, libflint), Ptr{fmpz}, (Ref{fmpq}, ), a)
  vn = ccall((:fmpz_remove, libflint), Clong, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), nr, nr, b)
  return -vn
end

function *(a::fmpz, b::BigFloat)
  return BigInt(a)*b
end

function BigFloat(a::fmpq)
  r = BigFloat(0)
  ccall((:fmpq_get_mpfr, libflint), Nothing, (Ref{BigFloat}, Ref{fmpq}, Int32), r, a, __get_rounding_mode())
  return r
end

function isless(a::Float64, b::fmpq) return a<b*1.0; end
function isless(a::fmpq, b::Float64) return a*1.0<b; end

function isless(a::Float64, b::fmpz) return a<b*1.0; end
function isless(a::fmpz, b::Float64) return a*1.0<b; end

is_commutative(::FlintIntegerRing) = true

#function ^(a::fmpz, k::fmpz)
#  if a == 0
#    if k == 0
#      return fmpz(1)
#    end
#    return fmpz(0)
#  end
#
#  if a == 1
#    return fmpz(1)
#  end
#  if a == -1
#    if isodd(k)
#      return fmpz(-1)
#    else
#      return fmpz(1)
#    end
#  end
#  return a^Int(k)
#end

function ^(a::fmpq, k::fmpz)
  if a == 0
    if k == 0
      return fmpq(1)
    end
    return fmpq(0)
  end

  if a == 1
    return fmpq(1)
  end
  if a == -1
    if isodd(k)
      return fmpq(-1)
    else
      return fmpq(1)
    end
  end
  return a^Int(k)
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

one(::Type{fmpz}) = fmpz(1)
one(::fmpz) = fmpz(1)
zero(::fmpz) = fmpz(0)

isinteger(::fmpz) = true
isfinite(::fmpz) = true

Integer(a::fmpz) = BigInt(a)

function divisible(x::Integer, y::Integer)
  return iszero(rem(x, y))
end

@doc Markdown.doc"""
    modord(a::fmpz, m::fmpz) -> Int
    modord(a::Integer, m::Integer)

  The multiplicative order of a modulo $m$ (not a good algorithm).
"""
function modord(a::fmpz, m::fmpz)
  gcd(a,m)!=1 && error("1st agrument not a unit")
  i = 1
  b = a % m
  while b != 1
    i += 1
    b = b*a % m
  end
  return i
end

function modord(a::Integer, m::Integer)
  gcd(a,m)!=1 && error("1st agrument not a unit")
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
    ccall((:fmpz_is_odd, libflint), Int, (Ref{fmpz},), a) == 1
  end

  function iseven(a::fmpz)
    ccall((:fmpz_is_even, libflint), Int, (Ref{fmpz},), a) == 1
  end
end

function neg!(a::fmpz)
  ccall((:fmpz_neg, libflint), Nothing, (Ref{fmpz}, Ref{fmpz}), a, a)
  return a
end

##
## Ranges
##
# Note, we cannot get a UnitRange as this is only legal for subtypes of Real.
# So, we use an AbstractUnitRange here mostly copied from `base/range.jl`.
# `StepRange`s on the other hand work out of the box thanks to duck typing.

struct fmpzUnitRange <: AbstractUnitRange{fmpz}
  start::fmpz
  stop::fmpz
  fmpzUnitRange(start, stop) = new(start, fmpz_unitrange_last(start, stop))
end
fmpz_unitrange_last(start::fmpz, stop::fmpz) =
  ifelse(stop >= start, stop, start - one(fmpz))

Base.:(:)(a::fmpz, b::fmpz) = fmpzUnitRange(a, b)

@inline function getindex(r::fmpzUnitRange, i::fmpz)
    val = r.start + (i - 1)
    @boundscheck _in_unit_range(r, val) || throw_boundserror(r, i)
    val
end
_in_unit_range(r::fmpzUnitRange, val::fmpz) = r.start <= val <= r.stop

show(io::IO, r::fmpzUnitRange) = print(io, repr(first(r)), ':', repr(last(r)))

in(x::IntegerUnion, r::fmpzUnitRange) = first(r) <= x <= last(r)

in(x::IntegerUnion, r::AbstractRange{fmpz}) =
  !isempty(r) && first(r) <= x <= last(r) &&
    mod(convert(fmpz,x),step(r)) == mod(first(r),step(r))

mod(i::IntegerUnion, r::fmpzUnitRange) = mod(i-first(r), length(r)) + first(r)

Base.:(:)(a::fmpz, b::Integer) = (:)(promote(a,b)...)
Base.:(:)(a::Integer, b::fmpz) = (:)(promote(a,b)...)

# Construct StepRange{fmpz, T} where +(::fmpz, zero(::T)) must be defined
Base.:(:)(a::fmpz, s, b::Integer) = ((a_,b_)=promote(a,b); a_:s:b_)
Base.:(:)(a::Integer, s, b::fmpz) = ((a_,b_)=promote(a,b); a_:s:b_)

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
  s = fmpz(0)
  while true
    s = fmpz(0)
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
  ccall((:fmpz_mod, libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), z, x, y)
  return z
end

function divexact!(z::fmpz, x::fmpz, y::fmpz)
  iszero(y) && throw(DivideError())
  ccall((:fmpz_divexact, libflint), Nothing,
        (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), z, x, y)
  return z
end

function lcm!(z::fmpz, x::fmpz, y::fmpz)
   ccall((:fmpz_lcm, libflint), Nothing,
         (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), z, x, y)
   return z
end

function gcd!(z::fmpz, x::fmpz, y::fmpz)
   ccall((:fmpz_gcd, libflint), Nothing,
         (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), z, x, y)
   return z
end

################################################################################
#
#  power detection
#
################################################################################
#compare to Oscar/examples/PerfectPowers.jl which is, for large input,
#far superiour over gmp/ fmpz_is_perfect_power

@doc Markdown.doc"""
    is_power(a::fmpz) -> Int, fmpz
    is_power(a::Integer) -> Int, Integer

Returns $e$, $r$ such that $a = r^e$ with $e$ maximal. Note: $1 = 1^0$.
"""
function is_power(a::fmpz)
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
  rt = fmpz()
  e = 1
  while true
    ex = ccall((:fmpz_is_perfect_power, libflint), Int, (Ref{fmpz}, Ref{fmpz}), rt, a)
    if ex == 1 || ex == 0
      return e, a
    end
    e *= ex
    a = rt
  end
end

function is_power(a::Integer)
  e, r = is_power(fmpz(a))
  return e, typeof(a)(r)
end

@doc Markdown.doc"""
    is_power(a::fmpq) -> Int, fmpq
    is_power(a::Rational) -> Int, Rational

Writes $a = r^e$ with $e$ maximal. Note: $1 = 1^0$.
"""
function is_power(a::fmpq)
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
  e, r = is_power(fmpq(a))
  return e, T(numerator(r))//T(denominator(r))
end

@doc Markdown.doc"""
    is_power(a::fmpz, n::Int) -> Bool, fmpz
    is_power(a::fmpq, n::Int) -> Bool, fmpq
    is_power(a::Integer, n::Int) -> Bool, Integer

Tests if $a$ is an $n$-th power. Return `true` and the root if successful.
"""
function is_power(a::fmpz, n::Int)
   if a < 0 && iseven(n)
    return false, a
  end
  b = root(a, n)
  return b^n==a, b
end

function is_power(a::fmpq, n::Int)
  fl, nu = is_power(numerator(a), n)
  if !fl
    return fl, a
  end
  fl, de = is_power(denominator(a), n)
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

  function fmpz_comb(primes::Vector{UInt})
    z = new()
    ccall((:fmpz_comb_init, libflint), Nothing, (Ref{fmpz_comb}, Ptr{UInt}, Int),
            z, primes, length(primes))
    finalizer(z, _fmpz_comb_clear_fn)
    return z
  end
end

function _fmpz_comb_clear_fn(z::fmpz_comb)
  ccall((:fmpz_comb_clear, libflint), Nothing, (Ref{fmpz_comb}, ), z)
end

mutable struct fmpz_comb_temp
  n::Int
  comb_temp::Ptr{Ptr{fmpz}}
  temp::Ptr{fmpz}
  temp2::Ptr{fmpz}

  function fmpz_comb_temp(comb::fmpz_comb)
    z = new()
    ccall((:fmpz_comb_temp_init, libflint), Nothing,
            (Ref{fmpz_comb_temp}, Ref{fmpz_comb}), z, comb)
    finalizer(z, _fmpz_comb_temp_clear_fn)
    return z
  end
end

function _fmpz_comb_temp_clear_fn(z::fmpz_comb_temp)
  ccall((:fmpz_comb_temp_clear, libflint), Nothing, (Ref{fmpz_comb_temp}, ), z)
end


function fmpz_multi_crt_ui!(z::fmpz, a::Vector{UInt}, b::fmpz_comb, c::fmpz_comb_temp)
  ccall((:fmpz_multi_CRT_ui, libflint), Nothing,
          (Ref{fmpz}, Ptr{UInt}, Ref{fmpz_comb}, Ref{fmpz_comb_temp}, Cint),
          z, a, b, c, 1)
  return z
end

function _fmpz_preinvn_struct_clear_fn(z::fmpz_preinvn_struct)
  ccall((:fmpz_preinvn_clear, libflint), Nothing, (Ref{fmpz_preinvn_struct}, ), z)
end

function fdiv_qr_with_preinvn!(q::fmpz, r::fmpz, g::fmpz, h::fmpz, hinv::fmpz_preinvn_struct)
  ccall((:fmpz_fdiv_qr_preinvn, libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}, Ref{fmpz}, Ref{fmpz_preinvn_struct}), q, r, g, h, hinv)
end

function submul!(z::fmpz, x::fmpz, y::fmpz)
  ccall((:fmpz_submul, libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), z, x, y)
end

################################################################################
#
#  Number of bits
#
################################################################################


@doc Markdown.doc"""
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

Returns `true` iff the denominator of $a$ is one.
"""
function isinteger(a::fmpq)
  return isone(denominator(a))
end

################################################################################
#
#  sunit group
#
################################################################################

mutable struct MapSUnitGrpZFacElem <: Map{GrpAbFinGen, FacElemMon{FlintRationalField}, HeckeMap, MapSUnitGrpZFacElem}
  header::MapHeader{GrpAbFinGen, FacElemMon{FlintRationalField}}
  idl::Vector{fmpz}

  function MapSUnitGrpZFacElem()
    return new()
  end
end

function show(io::IO, mC::MapSUnitGrpZFacElem)
  println(io, "SUnits (in factored form) map of $(codomain(mC)) for $(mC.idl)")
end

mutable struct MapSUnitGrpZ <: Map{GrpAbFinGen, FlintRationalField, HeckeMap, MapSUnitGrpZ}
  header::MapHeader{GrpAbFinGen, FlintRationalField}
  idl::Vector{fmpz}

  function MapSUnitGrpZ()
    return new()
  end
end

function show(io::IO, mC::MapSUnitGrpZ)
  println(io, "SUnits map of $(codomain(mC)) for $(mC.idl)")
end

@doc Markdown.doc"""
    sunit_group_fac_elem(S::Vector{fmpz}) -> GrpAbFinGen, Map
    sunit_group_fac_elem(S::Vector{Integer}) -> GrpAbFinGen, Map

The $S$-unit group of $Z$ supported at $S$: the group of
rational numbers divisible only by primes in $S$.
The second return value is the map mapping group elements to rationals
in factored form or rationals back to group elements.
"""
function sunit_group_fac_elem(S::Vector{T}) where T <: Integer
  return sunit_group_fac_elem(fmpz[x for x=S])
end

function sunit_group_fac_elem(S::Vector{fmpz})
  S = coprime_base(S)  #TODO: for S-units use factor???
  G = abelian_group(vcat(fmpz[2], fmpz[0 for i=S]))
  S = vcat(fmpz[-1], S)

  mp = MapSUnitGrpZFacElem()
  mp.idl = S

  Sq = fmpq[x for x=S]

  function dexp(a::GrpAbFinGenElem)
    return FacElem(Sq, fmpz[a.coeff[1,i] for i=1:length(S)])
  end

  mp.header = MapHeader(G, FacElemMon(FlintQQ), dexp)

  return G, mp
end

function preimage(f::MapSUnitGrpZFacElem, a::fmpz)
  g = Int[a>=0 ? 0 : 1]
  S = f.idl
  g = vcat(g, Int[valuation(a, x) for x=S[2:end]])
  return domain(f)(g)
end

function preimage(f::MapSUnitGrpZFacElem, a::Integer)
  return preimage(f, fmpz(a))
end

function preimage(f::MapSUnitGrpZFacElem, a::Rational)
  return preimage(f, fmpq(a))
end

function preimage(f::MapSUnitGrpZFacElem, a::fmpq)
  return preimage(f, numerator(a)) - preimage(f, denominator(a))
end

function preimage(f::MapSUnitGrpZFacElem, a::FacElem)
  return sum(GrpAbFinGenElem[e*preimage(f, k) for (k,e) = a.fac])
end

@doc Markdown.doc"""
    sunit_group(S::Vector{fmpz}) -> GrpAbFinGen, Map
    sunit_group(S::Vector{Integer}) -> GrpAbFinGen, Map

The $S$-unit group of $Z$ supported at $S$: the group of
rational numbers divisible only by primes in $S$.
The second return value is the map mapping group elements to rationals
or rationals back to group elements.
"""
function sunit_group(S::Vector{T}) where T <: Integer
  return sunit_group(fmpz[x for x=S])
end

function sunit_group(S::Vector{fmpz})
  u, mu = sunit_group_fac_elem(S)

  mp = MapSUnitGrpZ()
  mp.idl = S

  function dexp(a::GrpAbFinGenElem)
    return evaluate(image(mu, a))
  end

  mp.header = MapHeader(u, FlintQQ, dexp, mu.header.preimage)

  return u, mp
end

@doc Markdown.doc"""
    is_prime_power(n::fmpz) -> Bool
    is_prime_power(n::Integer) -> Bool

Tests if $n$ is the exact power of a prime number.
"""
function is_prime_power(n::fmpz)
  e, p = is_power(n)
  return is_prime(p)
end

function is_prime_power(n::Integer)
  return is_prime_power(fmpz(n))
end

################################################################################
# random and factor
################################################################################

factor(a...; b...) = Nemo.factor(a...; b...)

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

function ecm(a::fmpz, B1::UInt, B2::UInt, ncrv::UInt, rnd = flint_rand_ctx)
  f = fmpz()
  r = ccall((:fmpz_factor_ecm, libflint), Int32, (Ref{fmpz}, UInt, UInt, UInt, Ptr{Nothing}, Ref{fmpz}), f, ncrv, B1, B2, rnd.a, a)
  return r, f
end

function ecm(a::fmpz, B1::Int, B2::Int, ncrv::Int, rnd = flint_rand_ctx)
  return ecm(a, UInt(B1), UInt(B2), UInt(ncrv), rnd)
end

#data from http://www.mersennewiki.org/index.php/Elliptic_Curve_Method
B1 = [2, 11, 50, 250, 1000, 3000, 11000, 43000, 110000, 260000, 850000, 2900000];
nC = [25, 90, 300, 700, 1800, 5100, 10600, 19300, 49000, 124000, 210000, 340000];

function ecm(a::fmpz, max_digits::Int = div(ndigits(a), 3), rnd = flint_rand_ctx)
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

function factor_trial_range(N::fmpz, start::Int=0, np::Int=10^5)
   F = Nemo.fmpz_factor()
   ccall((:fmpz_factor_trial_range, libflint), Nothing, (Ref{Nemo.fmpz_factor}, Ref{fmpz}, UInt, UInt), F, N, start, np)
   res = Dict{fmpz, Int}()
   for i in 1:F.num
     z = fmpz()
     ccall((:fmpz_factor_get_fmpz, libflint), Nothing,
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

function factor_insert!(r::Dict{fmpz, Int}, N::fmpz, scale::Int = 1)
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

function _factors_trial_division(n::fmpz, np::Int = 10^5)
  res, u = factor_trial_range(n, 0, np)
  factors = fmpz[]
  for (p, v) in res
    push!(factors, p)
    n = divexact(n, p^v)
  end
  return factors, n

end

function ceil(::Type{fmpz}, a::BigFloat)
  return fmpz(ceil(BigInt, a))
end

function ceil(::Type{Int}, a::fmpq)
  return Int(ceil(fmpz, a))
end

function floor(::Type{fmpz}, a::BigFloat)
  return fmpz(floor(BigInt, a))
end

function floor(::Type{Int}, a::fmpq)
  return Int(floor(fmpz, a))
end

function round(::Type{fmpz}, a::BigFloat)
  return fmpz(round(BigInt, a))
end

function round(::Type{Int}, a::BigFloat)
  return Int(round(fmpz, a))
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

The unit group of $\mathbb{Z}$, i.e. $C_2$ and the map translating between the group and $\mathbb{Z}$.
"""
function unit_group(::FlintIntegerRing)
  G = abelian_group([2])
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

#Nemo.GaloisField = nmod?
# PolyRing

#basically from
#http://people.math.gatech.edu/~ecroot/shparlinski_final.pdf
#Contini, Croot, Shparlinski: Complexity of inverting the Euler function
@doc Markdown.doc"""
    euler_phi_inv_fac_elem(n::fmpz)

The inverse of the Euler totient functions: find all $x$ s.th. $phi(x) = n$
holds. The elements are returned in factored form.
"""
function euler_phi_inv_fac_elem(n::fmpz)
  lp = fmpz[]
  for d = Divisors(n)
    if is_prime(d+1)
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
    euler_phi_inv(n::Integer) -> Vector{fmpz}

The inverse of the Euler totient functions: find all $x$ s.th. $phi(x) = n$
holds.
"""
function euler_phi_inv(n::Integer)
  return euler_phi_inv(fmpz(n))
end

@doc Markdown.doc"""
    euler_phi_inv(n::fmpz) -> Vector{fmpz}

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
  function Limbs(a::fmpz; MSW::Bool = true)
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

bits(a::fmpz) = BitsFmpz(a)
#= wrong order, thus disabled

function getindex(B::BitsFmpz, i::Int)
  return ccall((:fmpz_tstbit, libflint), Int, (Ref{fmpz}, Int), B.L.a, i) != 0
end
=#

end

using .BitsMod
export bits, Limbs

^(a::T, n::IntegerUnion) where {T <: RingElem} = _generic_power(a, n)

^(a::NfAbsOrdIdl, n::IntegerUnion)  = _generic_power(a, n)

#^(a::NfRelOrdIdl, n::IntegerUnion)  = _generic_power(a, n)

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
function powermod(f::T, e::fmpz, g::T) where {T}
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

@doc Markdown.doc"""
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

@doc Markdown.doc"""
    squarefree_up_to(n::Int) -> Vector{Int}

Returns a vector containing all the squarefree numbers up to $n$.
"""
function squarefree_up_to(n::Int; coprime_to::Vector{fmpz} = fmpz[], prime_base::Vector{fmpz} = fmpz[])

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
@doc Markdown.doc"""
    is_squarefree(n::Union{Int, fmpz}) -> Bool

Returns true if $n$ is squarefree, false otherwise.
"""
function is_squarefree(n::Union{Int,fmpz})
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

Base.floor(::Type{fmpz}, x::fmpz) = x

Base.ceil(::Type{fmpz}, x::fmpz) = x

Base.floor(::Type{fmpz}, x::Int) = fmpz(x)

Base.ceil(::Type{fmpz}, x::Int) = fmpz(x)

Base.floor(::Type{fmpz}, x::fmpq) = fdiv(numerator(x), denominator(x))

Base.ceil(::Type{fmpz}, x::fmpq) = cdiv(numerator(x), denominator(x))

Base.round(x::fmpq, ::RoundingMode{:Up}) = ceil(x)

Base.round(::Type{fmpz}, x::fmpq, ::RoundingMode{:Up}) = ceil(fmpz, x)

Base.round(x::fmpq, ::RoundingMode{:Down}) = floor(x)

Base.round(::Type{fmpz}, x::fmpq, ::RoundingMode{:Down}) = floor(fmpz, x)

function Base.round(x::fmpq, ::RoundingMode{:Nearest})
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

Base.round(x::fmpq, ::RoundingMode{:NearestTiesAway}) = sign(x) * floor(abs(x) + 1//2)

Base.round(::Type{fmpz}, x::fmpq, ::RoundingMode{:NearestTiesAway}) = sign(x) == 1 ? floor(fmpz, abs(x) + 1//2) : -floor(fmpz, abs(x) + 1//2)

function Base.round(::Type{fmpz}, a::fmpq)
  return round(fmpz, a, RoundNearestTiesAway)
end

function Base.round(a::fmpq)
  return round(fmpz, a)
end

################################################################################
#
#  Squarefree part
#
################################################################################

@doc Markdown.doc"""
    squarefree_part(a::fmpz) -> fmpz

Returns the squarefee part $b$ of $a$, which is the smallest (absolute value)
integer $b$ such that $a/b$ is positive and squarefree.
"""
function squarefree_part(a::fmpz)
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

@doc Markdown.doc"""
    factor(a::fmpq, ::FlintIntegerRing) -> Fac{fmpz}

Factor the rational number $a$ into prime numbers.
"""
function factor(a::fmpq, ::FlintIntegerRing)
  fn = factor(numerator(a))
  fd = factor(denominator(a))
  for (p, e) = fd
    fn.fac[p] = -e
  end
  return fn
end

#missing in Nemo...
Hecke.clog(a::Int, b::Int) = clog(fmpz(a), b)

################################################################################
#
#   Support
#
################################################################################

function support(d::fmpz)
  return collect(keys(factor(d).fac))
end

function support(a::fmpq)
  d = denominator(a)
  n = numerator(a)
  res = fmpz[]
  for (p, _) in factor(d)
    push!(res, p)
  end
  for (p, _) in factor(n)
    push!(res, p)
  end
  return res
end

