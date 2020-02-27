export PrimesSet

################################################################################
#
#  Missing isprime functionality
#
################################################################################

# Fallback
function isprime(x::Integer)
  return isprime(fmpz(x))
end

################################################################################
#
#  Missing next_prime functionality
#
################################################################################

function next_prime(x::UInt, proof::Bool)
  z = ccall((:n_nextprime, libflint), UInt, (UInt, Cint), x, Cint(proof))
  return z
end

function next_prime(x::Int, proof::Bool)
  x < 0 && error("Argument must be positive")
  z = next_prime(UInt(x), proof)
  z > typemax(Int) && error("Next prime of input does not fit into an Int")
  return Int(z)
end

function next_prime(x::Int)
  x < 0 && error("Argument must be positive")
  z = next_prime(x, false)
  return z
end

function next_prime(z::T) where T <: Integer
  z < 0 && error("Argument must be positive")

  Tone = one(z)
  Tzero = zero(z)
  Ttwo = T(2)

  if iszero(z) || isone(z)
    return Ttwo
  end

  if iseven(z)
    z += Tone
  else
    z += Ttwo
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
  Ttwo = fmpz(2)

  if isone(z) || iszero(z)
    return Ttwo
  end

  if iseven(z)
    z += Tone
  else
    z += Ttwo
  end

  while !isprime(z)
    Nemo.addeq!(z, Ttwo)
  end

  return z
end

################################################################################
#
#  Primes iterator
#
################################################################################

# TODO (Tommy):
# At the moment proof doesn't do anything. The only reason is that
# next_prime() and isprime() do not support it generically.
# Once they do, it is easy to fix.
struct PrimesSet{T}
  from::T
  to::T
  nocond::Bool  # If set, there is no condition on the prime.
  proof::Bool   # Does not do anything at the moment
  mod::T        # If set (i.e. > 1), only primes p % mod == a are returned
  a::T
  sv::UInt

  function PrimesSet{T}(f::T, t::T) where {T}
    z = new{T}(f, t, true, false, T(1), T(0), UInt(1))
    return z
  end

  function PrimesSet{T}(f::T, t::T, mod::T, val::T) where {T}
    sv = UInt(1)
    p = UInt(2)
    while sv < 2^30 && p < f
      if !iszero(mod % p)
        sv *= p
      end
      p = next_prime(p, false)
    end
    if !isone(gcd(mod, val))
      error("Modulus and value need to be coprime.")
    end  
    r = new{T}(f, t, false, false, mod, val, sv)
    return r
  end
end

@doc Markdown.doc"""
    PrimesSet(f::Integer, t::Integer) -> PrimesSet
    PrimesSet(f::fmpz, t::fmpz) -> PrimesSet

Returns an iterable object $S$ representing the prime numbers $p$
for $f \le p \le t$. If $t=-1$, then the upper bound is infinite.
"""  
function PrimesSet(f::T, t::T) where T
  return PrimesSet{T}(f, t)
end

@doc Markdown.doc"""
    PrimesSet(f::Integer, t::Integer, mod::Integer, val::Integer)  
    PrimesSet(f::fmpz, t::fmpz, mod::fmpz, val::fmpz) 

Returns an iterable object $S$ representing the prime numbers $p$
for $f \le p \le t$ and $p\equiv val \bmod mod$ (primes in arithmetic
progression).  
 If $t=-1$, then the upper bound is infinite.
"""  
function PrimesSet(f::T, t::T, mod::T, val::T) where {T}
  return PrimesSet{T}(f, t, mod, val)
end

function Base.iterate(A::PrimesSet{T}) where {T <: Integer}
  if A.to != -1 && A.from > A.to
    return nothing
  end

  if A.nocond
    if !isprime(fmpz(A.from))
      p = next_prime(A.from)
    else
      p = A.from
    end

    if A.to != -1 && p > A.to
      return nothing
    else
      return p, p
    end
  end

  curr = A.from 
  c = curr % A.mod
  if A.mod > 1 && c != A.a
    curr += (- c + A.a) % A.mod
  end
  c_U = curr % A.sv
  c_M = A.mod % A.sv
  UIntone = one(UInt)
  i = zero(UInt)
  while gcd(c_U + i * c_M, A.sv) != UInt(1) || !isprime(fmpz(curr))
    curr += A.mod
    i += UIntone
  end

  if A.to != -1 && curr > A.to
    return nothing
  else
    return curr, curr
  end
end

function Base.iterate(A::PrimesSet{fmpz})
  if A.to != -1 && A.from > A.to
    return nothing
  end

  if A.nocond
    if !isprime(A.from)
      p = next_prime(A.from)
    else
      p = A.from
    end

    if A.to != -1 && p > A.to
      return nothing
    else
      return p, p
    end
  end

  curr = A.from 
  c = curr % A.mod
  if A.mod > 1 && c != A.a
    curr += (-c + A.a) % A.mod
  end

  c_U = curr % A.sv
  c_M = A.mod % A.sv
  UIntone = one(UInt)
  i = zero(UInt)
  while !isone(gcd(c_U + i * c_M, A.sv)) || !isprime(fmpz(curr))
    curr += A.mod
    i += UIntone
  end
  
  if A.to != -1 && curr > A.to
    return nothing
  else
    return curr, curr
  end
end

function Base.iterate(A::PrimesSet{T}, p) where T<: Union{Integer, fmpz}
  if A.nocond
    if p == 2
      nextp = T(3)
    else
      if T == Int
        nextp = next_prime(p, A.proof)
      else
        nextp = next_prime(p)
      end
    end

    if A.to != -1 && nextp > A.to
      return nothing
    else
      return nextp, nextp
    end
  end

  if A.mod > 1
    m = A.mod
  else
    if p==2
      nextp = T(3)
    end
    m = T(2)
  end
  nextp = p+m
  i = zero(UInt)
  UIntone = one(UInt)
  c_U = nextp % A.sv
  c_M = m % A.sv
  while !isone(gcd(c_U + i * c_M, A.sv)) || !isprime(fmpz(nextp))
    nextp += m
    i += UIntone
  end

  if A.to != -1 && nextp > A.to
    return nothing
  else
    return nextp, nextp
  end
end

# Iteration interface
#function Base.start(A::PrimesSet{T}) where T <: Integer
#  if A.nocond
#    if !isprime(fmpz(A.from))
#      p = next_prime(A.from)
#    else
#      p = A.from
#    end
#    return p
#  end
#
#  curr = A.from 
#  c = curr % A.mod
#  if A.mod > 1 && c != A.a
#    curr += (- c + A.a) % A.mod
#  end
#  c_U = curr % A.sv
#  c_M = A.mod % A.sv
#  UIntone = one(UInt)
#  i = zero(UInt)
#  while gcd(c_U + i * c_M, A.sv) != UInt(1) || !isprime(fmpz(curr))
#    curr += A.mod
#    i += UIntone
#  end
#  return curr
#end

#function Base.start(A::PrimesSet{fmpz})
#  if A.nocond
#    if !isprime(A.from)
#      p = next_prime(A.from)
#    else
#      p = A.from
#    end
#    return p
#  end
#
#  curr = A.from 
#  c = curr % A.mod
#  if A.mod > 1 && c != A.a
#    curr += (-c + A.a) % A.mod
#  end
#
#  c_U = curr % A.sv
#  c_M = A.mod % A.sv
#  UIntone = one(UInt)
#  i = zero(UInt)
#  while !isone(gcd(c_U + i * c_M, A.sv)) || !isprime(fmpz(curr))
#    curr += A.mod
#    i += UIntone
#  end
#  return curr
#end
#
#function Base.next(A::PrimesSet{T}, st::T) where T<: Union{Integer, fmpz}
#  p = st
#  if A.nocond
#    if p == 2
#      st = T(3)
#      return p, st
#    else
#      if T == Int
#        st = next_prime(p, A.proof)
#      else
#        st = next_prime(p)
#      end
#      return p, st
#    end
#  end
#
#  if A.mod > 1
#    m = A.mod
#  else
#    if p==2
#      st = T(3)
#      return p, st
#    end
#    m = T(2)
#  end
#  st = p+m
#  i = zero(UInt)
#  UIntone = one(UInt)
#  c_U = st % A.sv
#  c_M = m % A.sv
#  while !isone(gcd(c_U + i * c_M, A.sv)) || !isprime(fmpz(st))
#    st += m
#    i += UIntone
#  end
#
#  return p, st
#end
#
#function Base.done(A::PrimesSet{T}, st::T) where T <: Union{Integer, fmpz}
#  return A.to != -1 && st > A.to
#end

Base.eltype(::PrimesSet{T}) where {T <: Union{Integer, fmpz}} = T

Base.length(A::PrimesSet) = length(collect(A))

Base.IteratorSize(::Type{PrimesSet{T}}) where {T} = Base.SizeUnknown()

#Base.iteratorsize(::Type{PrimesSet{T}}) where {T} = Base.SizeUnknown()
