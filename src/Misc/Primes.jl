################################################################################
#
#  Primes iterator
#
################################################################################

mutable struct n_primes_struct
  small_i::Int   # should be Clong, but in Windows this does not work
  small_num::Int # Clong
  small_prime::Ptr{UInt}

  sieve_a::UInt
  sieve_b::UInt
  sieve_i::Int
  sieve_num::Int
  sieve::Ptr{Cchar}

  function n_primes_struct()
    r = new()
    n_primes_init!(r)
    finalizer(r) do r
      ccall((:n_primes_clear, Nemo.libflint), Cvoid, (Ref{n_primes_struct}, ), r)
    end
    return r
  end

  last_st::Int #to satisfy the iterator interface we need
  curr_st::Int #to keep track of the visible state
end

function n_primes_init!(a::n_primes_struct)
  ccall((:n_primes_init, Nemo.libflint), Cvoid, (Ref{n_primes_struct}, ), a)
end

function n_primes_init()
  return n_primes_struct()
end

function n_primes_init(from::Int, to::Int=-1)
  return n_primes_init!(n_primes_struct(), from, to)
end

function n_primes_init!(r::n_primes_struct, from::Int, to::Int=-1)
  if true || to < from #the sieve range is buggy in flint
    if from > 1
      from -= 1
    end
    if from < 1
      from = 1
    end
    ccall((:n_primes_jump_after, Nemo.libflint), Cvoid, (Ref{n_primes_struct}, UInt), r, from)
  else
    ccall((:n_primes_sieve_range, Nemo.libflint), Cvoid, (Ref{n_primes_struct}, UInt, UInt), r, from, to)
  end
  return r
end

function next_prime(r::n_primes_struct)
  return ccall((:n_primes_next, Nemo.libflint), UInt, (Ref{n_primes_struct}, ), r)
end


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
  r::Union{n_primes_struct, Nothing}

  function PrimesSet{T}(f::T, t::T) where {T}
    z = new{T}(f, t, true, false, T(1), T(0), UInt(1), nothing)
    return z
  end

  function PrimesSet{Int}(f::Int, t::Int)
    if f < 10^10
      #for PrimesSet(10^15, 10^15+10^9) the time is much worse
      #    PrimesSet(1, 10^9) it is FAST
      # ... flint mysteries
      z = new{Int}(f, t, true, false, 1, 0, UInt(1), n_primes_init(f))
    else
      z = new{Int}(f, t, true, false, 1, 0, UInt(1), nothing)
    end
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

@doc raw"""
    PrimesSet(f::Integer, t::Integer) -> PrimesSet
    PrimesSet(f::ZZRingElem, t::ZZRingElem) -> PrimesSet

Returns an iterable object $S$ representing the prime numbers $p$
for $f \le p \le t$. If $t=-1$, then the upper bound is infinite.
"""
function PrimesSet(f::T, t::T) where T
  return PrimesSet{T}(f, t)
end

@doc raw"""
    PrimesSet(f::Integer, t::Integer, mod::Integer, val::Integer)
    PrimesSet(f::ZZRingElem, t::ZZRingElem, mod::ZZRingElem, val::ZZRingElem)

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
    if A.r !== nothing
      n_primes_init!(A.r, A.from, A.to)
      p = Int(next_prime(A.r))
      A.r.last_st = -1
      A.r.curr_st = p
    elseif !is_prime(ZZRingElem(A.from))
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
  while gcd(c_U + i * c_M, A.sv) != UInt(1) || !is_prime(ZZRingElem(curr))
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

function Base.iterate(A::PrimesSet{ZZRingElem})
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
  while !isone(gcd(c_U + i * c_M, A.sv)) || !is_prime(ZZRingElem(curr))
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
    if A.r !== nothing
      if p == A.r.curr_st
        nextp = Int(next_prime(A.r))
        A.r.last_st = A.r.curr_st
        A.r.curr_st = nextp
      elseif p == A.r.last_st
        nextp = A.r.curr_st
      else
        A.r.last_st = -1
        n_primes_init!(A.r, p-1, A.to)
        A.r.curr_st = nextp = Int(next_prime(A.r))
      end
    elseif p == 2
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
  while !isone(gcd(c_U + i * c_M, A.sv)) || !is_prime(ZZRingElem(nextp))
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
#    if !is_prime(ZZRingElem(A.from))
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
#  while gcd(c_U + i * c_M, A.sv) != UInt(1) || !is_prime(ZZRingElem(curr))
#    curr += A.mod
#    i += UIntone
#  end
#  return curr
#end

#function Base.start(A::PrimesSet{ZZRingElem})
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
#  while !isone(gcd(c_U + i * c_M, A.sv)) || !is_prime(ZZRingElem(curr))
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
#  while !isone(gcd(c_U + i * c_M, A.sv)) || !is_prime(ZZRingElem(st))
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
