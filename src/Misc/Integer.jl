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

function factor_dict(A::BigInt)
  D = Dict{BigInt, Int}()
  a = factor(A)
  for i = 1:a.len 
    D[a.d[i][1]] = a.d[i][2]
  end
  return D
end

function factor_dict(A::fmpz)
  D = Dict{fmpz, Int}()
  a = factor(A)
  for i = 1:a.len 
    D[a.d[i][1]] = a.d[i][2]
  end
  return D
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

