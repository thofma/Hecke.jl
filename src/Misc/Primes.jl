export PrimesSet

################################################################################
#
#  Missing is_prime functionality
#
################################################################################

# Fallback
function is_prime(x::Integer)
  return is_prime(fmpz(x))
end

function next_prime(x::BigInt, proved::Bool = true)
  return BigInt(next_prime(fmpz(x), proved))
end

function next_prime(x::T, proved::Bool = true) where {T <: Integer}
  return T(next_prime(BigInt(x), proved))
end

################################################################################
#
#  Primes iterator
#
################################################################################

# TODO (Tommy):
# At the moment proof doesn't do anything. The only reason is that
# next_prime() and is_prime() do not support it generically.
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
    mod = abs(mod)
    val = Base.mod(val, mod)
    if mod == 1 && val == 0
      return new{T}(f, t, false, false, mod, val, sv)
    end
    if mod < 2
      error("modulus needs to be > 1")
    end
    if val < 1 || val >= mod
      error("wrong congruence condition: value needs to be > 0 and < modulus")
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
    if !is_prime(fmpz(A.from))
      p = next_prime(A.from)
    else
      p = A.from
    end

    if A.to != -1 && p > A.to
      return nothing
    else
      if p % A.mod != A.a
        return nothing
      else
        @show return p, p
      end
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
  while gcd(c_U + i * c_M, A.sv) != UInt(1) || !is_prime(fmpz(curr))
    curr += A.mod
    i += UIntone
    if A.to != -1 && curr > A.to
      break
    end
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
    if !is_prime(A.from)
      p = next_prime(A.from)
    else
      p = A.from
    end

    if A.to != -1 && p > A.to
      return nothing
    else
      if p % A.mod != A.a
        return nothing
      else
        return p, p
      end
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
  while !isone(gcd(c_U + i * c_M, A.sv)) || !is_prime(fmpz(curr))
    curr += A.mod
    i += UIntone
    if A.to != -1 && curr > A.to
      break
    end
  end

  if A.to != -1 && curr > A.to
    return nothing
  else
    return curr, curr
  end
end

function Base.iterate(A::PrimesSet{T}, p) where T<: IntegerUnion
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
  while !isone(gcd(c_U + i * c_M, A.sv)) || !is_prime(fmpz(nextp))
    nextp += m
    i += UIntone
    if A.to != -1 && nextp > A.to
      break
    end
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
#    if !is_prime(fmpz(A.from))
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
#  while gcd(c_U + i * c_M, A.sv) != UInt(1) || !is_prime(fmpz(curr))
#    curr += A.mod
#    i += UIntone
#  end
#  return curr
#end

#function Base.start(A::PrimesSet{fmpz})
#  if A.nocond
#    if !is_prime(A.from)
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
#  while !isone(gcd(c_U + i * c_M, A.sv)) || !is_prime(fmpz(curr))
#    curr += A.mod
#    i += UIntone
#  end
#  return curr
#end
#
#function Base.next(A::PrimesSet{T}, st::T) where T<: IntegerUnion
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
#  while !isone(gcd(c_U + i * c_M, A.sv)) || !is_prime(fmpz(st))
#    st += m
#    i += UIntone
#  end
#
#  return p, st
#end
#
#function Base.done(A::PrimesSet{T}, st::T) where T <: IntegerUnion
#  return A.to != -1 && st > A.to
#end

Base.eltype(::PrimesSet{T}) where {T <: IntegerUnion} = T

Base.length(A::PrimesSet) = length(collect(A))

Base.IteratorSize(::Type{PrimesSet{T}}) where {T} = Base.SizeUnknown()

#Base.iteratorsize(::Type{PrimesSet{T}}) where {T} = Base.SizeUnknown()
