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

# Bernstein: coprime bases
# ppio(a,b) = (c,n) where v_p(c) = v_p(a) if v_p(b) !=0, 0 otherwise
#                         c*n = a
# or c = gcd(a, b^infty)

function ppio(a::fmpz, b::fmpz) 
  c = gcd(a, b)
  n = div(a, c)
  m = c
  g = gcd(c, n)
  while g != 1
    c = c*g
    n = div(n, g)
    g = gcd(c, n)
  end
  return (c, n)
end

function ppio{T <: Integer}(a::T, b::T) 
  c = gcd(a, b)
  n = div(a, c)
  m = c
  g = gcd(c, n)
  while g != 1
    c = c*g
    n = div(n, g)
    g = gcd(c, n)
  end
  return (c, n)
end

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

