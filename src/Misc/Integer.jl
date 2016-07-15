################################################################################
#
#  Integer functions
#
################################################################################

function next_prime(x::UInt, proof::Bool)
  z = ccall((:n_nextprime, :libflint), UInt, (UInt, Cint), x, Cint(proof))
  return z
end

function next_prime(x::Int, proof::Bool)
  z = next_prime(UInt(x), proof)
  z > typemax(Int) && error("Next prime of input is not an Int")
  return Int(z)
end

function next_prime(x::Int)
  z = next_prime(x, false)
  return z
end

function next_prime{T <: Integer}(z::T)
  z < 0 && error("Argument must be positive")

  Tone = one(z)
  Tzero = zero(z)
  Ttwo = one(z) + one(z)

  if z == Tone || z == Tzero
    return Ttwo
  end

  if iseven(z)
    z += Tone
  else z += Ttwo
  end

  while !isprime(z)
    z += Ttwo
  end

  return z
end

function next_prime(z::fmpz)
  z < 0 && error("Argument must be positive")

  Tone = one(z)
  Tzero = zero(z)
  Ttwo = one(z) + one(z)

  if z == Tone || z == Tzero
    return Ttwo
  end

  if iseven(z)
    z += Tone
  else z += Ttwo
  end

  while !isprime(z)
    Nemo.addeq!(z, Ttwo)
  end

  return z
end


# should be Bernstein'ed: this is slow for large valuations
# returns the maximal v s.th. z mod p^v == 0 and z div p^v
#   also useful if p is not prime....

function valuation{T <: Integer}(z::T, p::T)
  z == 0 && error("Not yet implemented")
  const v = 0
  while mod(z, p) == 0
    z = div(z, p)
    v += 1
  end
  return (v, z)
end 

function valuation{T <: Integer}(z::Rational{T}, p::T)
  z == 0 && error("Not yet implemented")
  v, d = valuation(den(z), p)
  w, n = valuation(num(z), p)
  return w-v, n//d
end 

function valuation(z::fmpz, p::fmpz)
  z == 0 && error("Not yet implemented")
  v = 0
  while mod(z, p) == 0
    z = div(z, p)
    v += 1
  end
  return v, z
end 

function valuation(z::fmpq, p::fmpz)
  z == 0 && error("Not yet implemented")
  v, d = valuation(den(z), p)
  w, n = valuation(num(z), p)
  return w-v, n//d
end 

valuation(z::fmpz, p::Int) = valuation(z, fmpz(p))

function *(a::fmpz, b::BigFloat)
  return BigInt(a)*b
end

function Float64(a::fmpz)
  return ccall((:fmpz_get_d, :libflint), Float64, (Ptr{fmpz},), &a)
end

function BigFloat(a::fmpq)
  r = BigFloat(0)
  ccall((:fmpq_get_mpfr, :libflint), Void, (Ptr{BigFloat}, Ptr{fmpq}, Int32), &r, &a, Base.MPFR.ROUNDING_MODE[end])
  return r
end

function isless(a::Float64, b::fmpq) return a<b*1.0; end
function isless(a::fmpq, b::Float64) return a*1.0<b; end

function isless(a::Float64, b::fmpz) return a<b*1.0; end
function isless(a::fmpz, b::Float64) return a*1.0<b; end

function Base.call(a::FlintIntegerRing, b::fmpq)
  !isone(den(b)) && error("Denominator not 1")
  return deepcopy(num(b))
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
  Float64(div(num(b), den(b)))/(Float64(2)^53) #CF 2^53 is bad in 32bit
end

function convert(R::Type{Rational{Base.GMP.BigInt}}, a::Nemo.fmpz)
  return R(BigInt(a))
end

log(a::fmpz) = log(BigInt(a))
log(a::fmpq) = log(num(a)) - log(den(a))

function round(a::fmpq)
  n = num(a)
  d = den(a)
  q = div(n, d)
  r = mod(n, d)
  if r >= d//2
    return q+1
  else
    return q
  end
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

  The multiplicative order of a modulo m, no good algorithm.
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
  ccall((:fmpz_is_odd, :libflint), Int, (Ptr{fmpz},), &a) == 1
end

function iseven(a::fmpz)
  ccall((:fmpz_is_even, :libflint), Int, (Ptr{fmpz},), &a) == 1
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

immutable RangeGeneratorfmpz <: Base.Random.RangeGenerator
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

function ^(x::fmpq, y::fmpz)
  if typemax(Int) > y
    return x^Int(y)
  else
    error("Not implemented (yet)")
  end
end


############################################################
# more unsafe function that Bill does not want to have....
############################################################

function divexact!(z::fmpz, x::fmpz, y::fmpz)
    y == 0 && throw(DivideError())
    ccall((:fmpz_divexact, :libflint), Void, 
          (Ptr{fmpz}, Ptr{fmpz}, Ptr{fmpz}), &z, &x, &y)
    z
end

function lcm!(z::fmpz, x::fmpz, y::fmpz)
   ccall((:fmpz_lcm, :libflint), Void, 
         (Ptr{fmpz}, Ptr{fmpz}, Ptr{fmpz}), &z, &x, &y)
end

function gcd!(z::fmpz, x::fmpz, y::fmpz)
   ccall((:fmpz_gcd, :libflint), Void, 
         (Ptr{fmpz}, Ptr{fmpz}, Ptr{fmpz}), &z, &x, &y)
end
 
function inv!(a::perm)
  R = parent(a)
  ccall((:_perm_inv, :libflint), Void, (Ref{Int}, Ref{Int}, Int), a.d, a.d, R.n)
  nothing
end

################################################################################
#
#  Chinese remaindering modulo UInts to fmpz
#
################################################################################

type fmpz_comb
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

type fmpz_comb_temp
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

type fmpz_preinvn_struct
  dinv::Ptr{UInt}
  n::Int
  norm::Int

  function fmpz_preinvn_struct(f::fmpz)
    z = new()
    ccall((:fmpz_preinvn_init, :libflint), Void, (Ptr{fmpz_preinvn_struct}, Ptr{fmpz}), &z, &f)
    finalizer(z, _fmpz_preinvn_struct_clear_fn)
    return z
  end
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
