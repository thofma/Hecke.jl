################################################################################
#
#  Parent constructor
#
################################################################################

function SRowSpace(R::Ring; cached = true)
  T = elem_type(R)
  return SRowSpace{T}(R)
end

base_ring(A::SRow) = parent(A.values[1])

==(x::SRow{T}, y::SRow{T}) where {T} = (x.pos == y.pos) && (x.values == y.values)

################################################################################
#
#  Sparse row creation
#
################################################################################

function SRow(R::Ring)
  return SRow{elem_type(R)}()
end

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

function show(io::IO, A::SRow{T}) where T
  print(io, "sparse row with positions $(A.pos) and values $(A.values)\n")
end

################################################################################
#
#  Copy
#
################################################################################

function copy(A::SRow{T}) where T
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

################################################################################
#
#  Change ring
#
################################################################################

function SRow(A::SRow{fmpz}, n::Int)
  R = ZZModUInt(UInt(n))
  return SRow(A, R)
end

function SRow(A::SRow{fmpz}, R::T) where T <: Ring
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

doc"""
    SMat(A::SMat{fmpz}, n::Int) -> SMat{GenRes{fmpz}}
    SRow(A::SMat{fmpz}, n::Int) -> SRow{GenRes{fmpz}}

> Converts $A$ to ba a sparse matrix (row) over $Z/nZ$ 
"""
function SRow(A::SRow{fmpz}, n::fmpz)
  R = ResidueRing(FlintZZ, n)
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

function mul(A::SRow{T}, B::SRow{T}) where T
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

function +(A::SRow{T}, B::SRow{T}) where T
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

function *(b::T, A::SRow{T}) where T
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

function *(b::Integer, A::SRow{T}) where T
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

