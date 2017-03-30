export SRowSpace, mod_sym, mod_sym!, change_ring

################################################################################
#
#  Parent constructor
#
################################################################################

function SRowSpace(R::Ring, cached = true)
  T = elem_type(R)
  return SRowSpace{T}(R, cached)
end

(A::SRowSpace)() = SRow(base_ring(A))

base_ring{T}(A::SRowSpace{T}) = A.base_ring::parent_type(T)

base_ring{T}(A::SRow{T}) = parent(A.values[1])::parent_type(T)

################################################################################
#
#  Sparse row creation
#
################################################################################

function SRow(R::Ring)
  return SRow{elem_type(R)}()
end

function SRow{T}(A::Array{Tuple{Int, T}, 1})
  return SRow{T}(A)
end

function SRow{T}(pos::Array{Int, 1}, val::Array{T, 1})
  length(pos) == length(val) || error("Arrays must have same length")
  return SRow{T}(pos, val)
end

function SRow{T <: Ring}(A::SRow{fmpz}, R::T)
  z = SRow{elem_type(R)}()
  for (i, v) in A
    nv = R(v)
    if iszero(nv)
      continue
    else
      push!(z.pos, i)
      push!(z.values, nv)
    end
  end
  return z
end

################################################################################
#
#  Equality
#
################################################################################

=={T}(x::SRow{T}, y::SRow{T}) = (x.pos == y.pos) && (x.values == y.values)

################################################################################
#
#  Hashing
#
################################################################################

function hash(A::SRow, h::UInt)
  return hash(A.pos, hash(A.values, h))
end

################################################################################
#
#  String I/O
#
################################################################################

function show{T}(io::IO, A::SRow{T})
  print(io, "Sparse row with positions $(A.pos) and values $(A.values)\n")
end

################################################################################
#
#  Copy
#
################################################################################

function copy{T}(A::SRow{T})
  sr = SRow{T}()
  for (p, v) = A
    push!(sr.pos, p)
    push!(sr.values, v)
  end
  return sr
end

################################################################################
#
#  Zero row testing
#
################################################################################

function iszero(A::SRow)
  return length(A.pos) == 0
end

################################################################################
#
#  Modular reduction
#
################################################################################

doc"""
***
    mod!(A::SRow{fmpz}, n::Integer)

> Inplace reduction of all entries of $A$ modulo $n$ to the positive residue
> system.
"""
function mod!(A::SRow{fmpz}, n::Integer)
  i=1
  while i<= length(A.pos)
    v = mod(A.values[i], n)
    if v == 0
      deleteat!(A.pos, i)
      deleteat!(A.values, i)
    else
      A.values[i] = v
      i += 1
    end
  end
end

doc"""
***
    mod!(A::SRow{fmpz}, n::fmpz)

> Inplace reduction of all entries of $A$ modulo $n$ to the positive residue
> system.
"""
function mod!(A::SRow{fmpz}, n::fmpz)
  i=1
  while i<= length(A.pos)
    v = mod(A.values[i], n)
    if v == 0
      deleteat!(A.pos, i)
      deleteat!(A.values, i)
    else
      A.values[i] = v
      i += 1
    end
  end
end

function mod(A::SRow{fmpz}, n::Union{fmpz, Integer})
  B = copy(A)
  mod!(B, n)
  return B
end

# Todo: Do not convert to fmpz
doc"""
***
    mod_sym!(A::SRow{fmpz}, n::Integer)

> Inplace reduction of all entries of $A$ modulo $n$ to the symmetric residue
> system.
"""
function mod_sym!(A::SRow{fmpz}, n::Integer)
  mod_sym!(A, fmpz(n))
end

doc"""
***
    mod_sym!(A::SRow{fmpz}, n::fmpz)

> Inplace reduction of all entries of $A$ modulo $n$ to the symmetric residue
> system.
"""
function mod_sym!(A::SRow{fmpz}, n::fmpz)
  i=1
  while i<= length(A.pos)
    v = mod_sym(A.values[i], n)
    if v == 0
      deleteat!(A.pos, i)
      deleteat!(A.values, i)
    else
      A.values[i] = v
      i += 1
    end
  end
end

function mod_sym(A::SRow{fmpz}, n::Union{fmpz, Integer})
  B = copy(A)
  mod_sym!(B, n)
  return B
end

################################################################################
#
#  Change ring
#
################################################################################

function change_ring(A::SRow, R::Ring)
  return SRow(A, R)
end

################################################################################
#
#  Make sparse row iteratable
#
################################################################################

function length(A::SRow)
  return length(A.pos)
end

function endof(A::SRow)
  return length(A.pos)
end

function start(A::SRow)
  return 1
end

function next(A::SRow, st::Int)
  return (A.pos[st], A.values[st]), st + 1
end

function done(A::SRow, st::Int)
  return st > length(A.pos)
end

################################################################################
#
#  Multiplication
#
################################################################################

function mul{T}(A::SRow{T}, B::SRow{T})
  @assert length(A) != 0
  v = 0*A.values[1]
  b = 1
  for a=1:length(A.pos)
    while b<=length(B.values) && B.pos[b] < A.pos[a]
      b += 1
    end
    if b>length(B.values)
      return v
    end
    if B.pos[b] == A.pos[a]
      v += B.values[b] * A.values[a]
    end
  end
  return v
end

#in-place scaling
function scale_row!(a::SRow{fmpz}, b::fmpz)
  @assert !iszero(b)
  if isone(b)
    return
  end
  for i=1:length(a.pos)
    a.values[i] *= b
  end
end

################################################################################
#
#  Addition
#
################################################################################

function +{T}(A::SRow{T}, B::SRow{T})
  if length(A.values) == 0
    return B 
  elseif length(B.values) == 0
    return A
  end
  return add_scaled_row(A, B, base_ring(A)(1))
end

################################################################################
#
#  Scalar multiplication
#
################################################################################

# The following functions runs into an infinite recursion in case T = fmpz
#function *{T}(b::fmpz, A::SRow{T})
#  r = base_ring(A)(b)
#  return r*A
#end

function *{T}(b::T, A::SRow{T})
  B = SRow{T}()
  if iszero(b)
    return B
  end
  for (p,v) = A
    nv = v*b
    if !iszero(nv)  # there are zero divisors - potentially
      push!(B.pos, p)
      push!(B.values, v*b)
    end
  end
  return B
end

function *{T}(b::Integer, A::SRow{T})
  return base_ring(A)(b)*A
end

################################################################################
#
#  Maximum and minimum
#
################################################################################

doc"""
***
    max(A::SRow{fmpz}) -> fmpz

> Finds the largest entry of $A$.
"""
function max(A::SRow{fmpz})
  return maximum(A.values)
end

doc"""
***
    min(A::SRow{Int}) -> Int

> Finds the smallest entry of $A$.
"""
function min(A::SRow{fmpz})
  return minimum(A.values)
end

################################################################################
#
#  Lifting
#
################################################################################

doc"""
    lift(a::SRow{UIntMod}) -> SRow{fmpz}

> Lifts all entries in $a$.
"""
function lift(a::SRow{UIntMod})
  b = SRow{fmpz}()
  for (p,v) = a
    push!(b.pos, p)
    push!(b.values, fmpz(v.m))
  end
  return b
end

