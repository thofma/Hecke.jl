import Base.Vector

################################################################################
#
#  Parent constructor
#
################################################################################

function SRowSpace(R::Ring; cached = true)
  T = elem_type(R)
  return SRowSpace{T}(R, cached)
end

base_ring(A::SRow{ZZRingElem}) = ZZ

base_ring(A::SRow{QQFieldElem}) = QQ

function base_ring(A::SRow{T}) where {T}
  if isdefined(A, :base_ring)
    return A.base_ring::parent_type(T)
  elseif length(A.values) > 0
    return parent(A.values[1])
  else
    error("Base ring of empty row not defined")
  end
end

base_ring_type(::Type{SRow{T}}) where {T} = parent_type(T)


@doc raw"""
    sparse_row_type(a)

Return the type of the sparse row type of the given element, element type, parent or parent type $a$.

# Examples
```jldoctest
julia> x = sparse_row(QQ)
Sparse row with positions Int64[] and values QQFieldElem[]

julia> sparse_row_type(QQ) == typeof(x)
true

julia> sparse_row_type(zero(QQ)) == typeof(x)
true

julia> sparse_row_type(typeof(QQ)) == typeof(x)
true

julia> sparse_row_type(typeof(zero(QQ))) == typeof(x)
true
```
"""
sparse_row_type(::T) where {T <: Union{NCRing, NCRingElem}} = sparse_row_type(T)
sparse_row_type(::Type{T}) where {T <: NCRing} = sparse_row_type(elem_type(T))
sparse_row_type(::Type{T}) where {T <: NCRingElem} = SRow{T, sparse_inner_type(T)}


==(x::SRow{T}, y::SRow{T}) where {T} = (x.pos == y.pos) && (x.values == y.values)
ConformanceTests.equality(A::SRow, B::SRow) = A == B

################################################################################
#
#  Sparse row creation
#
################################################################################

@doc raw"""
    sparse_row(R::Ring) -> SRow

Constructs an empty row with base ring $R$.
"""
function sparse_row(R::NCRing)
  return SRow(R)
end

@doc raw"""
    sparse_row(R::Ring, J::Vector{Tuple{Int, T}}) -> SRow{T}

Constructs the sparse row $(a_i)_i$ with $a_{i_j} = x_j$, where $J = (i_j, x_j)_j$.
The elements $x_i$ must belong to the ring $R$.
"""
function sparse_row(R::NCRing, A::Vector{Tuple{Int, T}}; sort::Bool = true) where T
  if sort && length(A) > 1
    A = Base.sort(A, lt=(a,b) -> isless(a[1], b[1]))
  end
  return SRow(R, A)
end

@doc raw"""
    sparse_row(R::Ring, J::Vector{Tuple{Int, Int}}) -> SRow

Constructs the sparse row $(a_i)_i$ over $R$ with $a_{i_j} = x_j$,
where $J = (i_j, x_j)_j$.
"""
function sparse_row(R::NCRing, A::Vector{Tuple{Int, Int}}; sort::Bool = true)
  if sort && length(A) > 1
    A = Base.sort(A, lt=(a,b) -> isless(a[1], b[1]))
  end
  return SRow(R, A)
end

function Base.empty!(A::SRow)
  empty!(A.pos)
  empty!(A.values)
  return A
end

function Base.empty(A::SRow)
  return sparse_row(base_ring(A))
end

function zero(A::SRow)
  return empty(A)
end

function swap!(A::SRow, B::SRow)
  A.pos, B.pos = B.pos, A.pos
  A.values, B.values = B.values, A.values
  nothing
end

@doc raw"""
    sparse_row(R::NCRing, J::Vector{Int}, V::Vector{T}) -> SRow{T}

Constructs the sparse row $(a_i)_i$ over $R$ with $a_{i_j} = x_j$, where
$J = (i_j)_j$ and $V = (x_j)_j$.
"""
function sparse_row(R::NCRing, pos::Vector{Int}, val::AbstractVector{T}; sort::Bool = true) where T
  if sort && length(pos) > 1
    p = sortperm(pos)
    pos = pos[p]
    val = val[p]
  end
  if T === elem_type(R)
    return SRow(R, pos, val)
  else
    mapval = map(R, val)::Vector{elem_type(R)}
    return SRow(R, pos, mapval)
  end
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
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(r::SRow, dict::IdDict)
  s = sparse_row(base_ring(r))
  s.pos = Base.deepcopy_internal(r.pos, dict)
  s.values = Base.deepcopy_internal(r.values, dict)
  return s
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, A::SRow{T}) where T
  print(io, "Sparse row with positions $(A.pos) and values $(A.values)")
end

################################################################################
#
#  Copy
#
################################################################################

function copy(A::SRow{T}) where T
  sr = sparse_row(base_ring(A))
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

@doc raw"""
    mod!(A::SRow{ZZRingElem}, n::Integer) -> SRow{ZZRingElem}

Inplace reduction of all entries of $A$ modulo $n$ to the positive residue
system.
"""
function mod!(A::SRow{ZZRingElem}, n::Integer)
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
  return A
end

@doc raw"""
    mod!(A::SRow{ZZRingElem}, n::ZZRingElem) -> SRow{ZZRingElem}

Inplace reduction of all entries of $A$ modulo $n$ to the positive residue
system.
"""
function mod!(A::SRow{ZZRingElem}, n::ZZRingElem)
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

# Todo: Do not convert to ZZRingElem
@doc raw"""
    mod_sym!(A::SRow{ZZRingElem}, n::Integer) -> SRow{ZZRingElem}

Inplace reduction of all entries of $A$ modulo $n$ to the symmetric residue
system.
"""
function mod_sym!(A::SRow{ZZRingElem}, n::Integer)
  mod_sym!(A, ZZRingElem(n))
end

@doc raw"""
    mod_sym!(A::SRow{ZZRingElem}, n::ZZRingElem) -> SRow{ZZRingElem}

Inplace reduction of all entries of $A$ modulo $n$ to the symmetric residue
system.
"""
function mod_sym!(A::SRow{ZZRingElem}, n::ZZRingElem)
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

function map_entries(f, A::SRow)
  iszero(A) && error("Can change ring only for non-zero rows")
  R = parent(f(A.values[1]))
  z = sparse_row(R)
  for (i, v) in A
    nv = f(v)
    if iszero(nv)
      continue
    else
      push!(z.pos, i)
      push!(z.values, nv)
    end
  end
  return z
end

@doc raw"""
    change_base_ring(R::Ring, A::SRow) -> SRow

Create a new sparse row by coercing all elements into the ring $R$.
"""
function change_base_ring(R::S, A::SRow{T}) where {T <: NCRingElem, S <: NCRing}
  z = sparse_row(R)
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
#  Getting and setting values
#
################################################################################

# TODO:
# The list of positions is ordered, so there should be a faster find function.
@doc raw"""
    getindex(A::SRow, j::Int) -> RingElem

Given a sparse row $(a_i)_{i}$ and an index $j$ return $a_j$.
"""
function Base.getindex(A::SRow{T}, i::Int) where {T <: NCRingElem}
  i < 1 && error("Index must be positive")
  p = findfirst(isequal(i), A.pos)
  if p === nothing
    return zero(base_ring(A))
  else
    return A.values[p]
  end
end

################################################################################
#
#  Make sparse row iterable
#
################################################################################

@doc raw"""
    length(A::SRow)

Returns the number of nonzero entries of $A$.
"""
function length(A::SRow)
  return length(A.pos)
end

function endof(A::SRow)
  return length(A.pos)
end

function Base.iterate(A::SRow, st::Int = 1)
  if st > length(A.pos)
    return nothing
  end

  return (A.pos[st], A.values[st]), st + 1
end

Base.eltype(::Type{<:SRow{T}}) where T = Tuple{Int, T}

Base.IteratorSize(::Type{<:SRow{T}}) where T = Base.HasLength()

################################################################################
#
#  Dot product
#
################################################################################

@doc raw"""
    dot(A::SRow, B::SRow) -> RingElem

Returns the dot product of $A$ and $B$. Note the order matters in non-commutative case.
"""
function dot(A::SRow{T}, B::SRow{T}) where T
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
      v += A.values[a] * B.values[b]
    end
  end
  return v
end

function dot(A::SRow{T}, b::AbstractVector{T}) where {T}
  if length(b) == 0 && length(A.pos) == 0
    error("One of the vectors must have non-zero length")
  end
  if length(b) == 0
    return zero(base_ring(A))
  end
  if length(A.pos) == 0
    return zero(parent(b[1]))
  end
  s = zero(base_ring(A))
  t = zero(base_ring(A))
  for j=1:length(A.pos)
    t = mul_red!(t, A.values[j], b[A.pos[j]], false)
    s = add!(s, s, t)
#    s += A.values[j] * b[A.pos[j]]
  end
  return reduce!(s)
end

function dot(A::SRow{T}, b::AbstractVector{T}, zero::T) where {T}
  s = parent(zero)(0)
  t = parent(zero)(0)
  for j=1:length(A.pos)
    t = mul_red!(t, A.values[j], b[A.pos[j]], false)
    s = add!(s, s, t)
#    s += A.values[j] * b[A.pos[j]]
  end
  return reduce!(s)
end

dot(b::AbstractVector{T}, A::SRow{T}) where {T} = dot(A, b)

dot(b::AbstractVector{T}, A::SRow{T}, zero::T) where {T} = dot(A, b)

function dot(A::SRow{T}, b::MatElem{T}, i::Int) where {T}
  s = zero(base_ring(b))
  for j=1:length(A.pos)
    s += A.values[j] * b[A.pos[j], i]
  end
  return s
end

function dot(A::SRow{T}, i::Int, b::MatElem{T}) where {T}
  s = zero(base_ring(b))
  for j=1:length(A.pos)
    s += A.values[j] * b[i, A.pos[j]]
  end
  return s
end

################################################################################
#
#  Inplace scaling
#
################################################################################

@doc raw"""
    scale_row!(a::SRow, b::NCRingElem) -> SRow

Returns the (left) product of $b \times a$ and reassigns the value of $a$ to this product.
For rows, the standard multiplication is from the left.
"""
function scale_row!(a::SRow{T}, b::T) where T
  if iszero(b)
    return empty!(a)
  elseif isone(b)
    return a
  end
  i = 1
  while i <= length(a)
    a.values[i] = b*a.values[i]
    if iszero(a.values[i])
      deleteat!(a.values, i)
      deleteat!(a.pos, i)
    else
      i += 1
    end
  end
  return a
end

scale_row!(a::SRow, b) = scale_row!(a, base_ring(a)(b))

@doc raw"""
    scale_row_right!(a::SRow, b::NCRingElem) -> SRow

Returns the (right) product of $a \times b$ and modifies $a$ to this product.
"""
function scale_row_right!(a::SRow{T}, b::T) where T
  if iszero(b)
    return empty!(a)
  elseif isone(b)
    return a
  end
  i = 1
  while i <= length(a)
    a.values[i] *= b
    if iszero(a.values[i])
      deleteat!(a.values, i)
      deleteat!(a.pos, i)
    else
      i += 1
    end
  end
  return a
end

scale_row_right!(a::SRow, b) = scale_row_right!(a, base_ring(a)(b))

function scale_row_left!(a::SRow{T}, b::T) where T
  return scale_row!(a,b)
end

scale_row_left!(a::SRow, b) = scale_row_left!(a, base_ring(a)(b))

################################################################################
#
#  Addition
#
################################################################################

function +(A::SRow{T}, B::SRow{T}) where T
  if length(A.values) == 0
    return deepcopy(B)
  elseif length(B.values) == 0
    return deepcopy(A)
  end
  return add_scaled_row(A, B, one(base_ring(A)))
end

function -(A::SRow{T}, B::SRow{T}) where T
  if length(A) == 0
    if length(B) == 0
      return deepcopy(A)
    else
      return add_scaled_row(B, A, -1)
    end
  end
  return add_scaled_row(B, A, -1)
end

function -(A::SRow{T}) where {T}
  B = sparse_row(base_ring(A))
  for (p, v) = A
    push!(B.pos, p)
    push!(B.values, -v)
  end
  return B
end

################################################################################
#
#  Scalar operations
#
################################################################################

function *(b::T, A::SRow{T}) where T
  B = sparse_row(parent(b))
  if iszero(b)
    return B
  end
  for (p,v) in A
    nv = b*v
    if !iszero(nv)  # there are zero divisors - potentially
      push!(B.pos, p)
      push!(B.values, nv)
    end
  end
  return B
end

function *(b, A::SRow)
  if length(A.values) == 0
    return sparse_row(base_ring(A))
  end
  return base_ring(A)(b)*A
end

function *(A::SRow{T}, b::T) where T
  B = sparse_row(parent(b))
  if iszero(b)
    return B
  end
  for (p,v) in A
    nv = v*b
    if !iszero(nv)  # there are zero divisors - potentially
      push!(B.pos, p)
      push!(B.values, nv)
    end
  end
  return B
end

function *(A::SRow, b)
  if length(A.values) == 0
    return sparse_row(base_ring(A))
  end
  return A*base_ring(A)(b)
end

#left and right div not implemented
function div(A::SRow{T}, b::T) where T
  B = sparse_row(base_ring(A))
  if iszero(b)
    return error("Division by zero")
  end
  for (p,v) = A
    nv = div(v, b)
    if !iszero(nv)
      push!(B.pos, p)
      push!(B.values, nv)
    end
  end
  return B
end

function div(A::SRow{T}, b::Integer) where T
  if length(A.values) == 0
    return sparse_row(base_ring(A))
  end
  return div(A, base_ring(A)(b))
end

@doc raw"""
    divexact(A::SRow, b::RingElem; check::Bool = true) -> SRow

Return $C$ such that $a = b \cdot C$. Calls the function `divexact_left(A,b;check)`
"""
divexact(A::SRow{T}, b::T; check::Bool=true) where T <: RingElem = divexact_left(A, b; check)

function divexact_left(A::SRow{T}, b::T; check::Bool=true) where T <: NCRingElem
  B = sparse_row(base_ring(A))
  if iszero(b)
    return error("Division by zero")
  end
  for (p,v) = A
    nv = divexact_left(v, b; check=check)
    @assert !iszero(nv)
    push!(B.pos, p)
    push!(B.values, nv)
  end
  return B
end

function divexact(A::SRow{T}, b::Integer; check::Bool=true) where T
  if length(A.values) == 0
    return deepcopy(A)
  end
  return divexact_left(A, base_ring(A)(b), check=check)
end

@doc raw"""
    divexact_right(A::SRow, b::NCRingElem; check::Bool = true) -> SRow

Return $C$ such that $A = C \cdot b.
"""
function divexact_right(A::SRow{T}, b::T; check::Bool=true) where T
  B = sparse_row(base_ring(A))
  if iszero(b)
    return error("Division by zero")
  end
  for (p,v) = A
    nv = divexact_right(v, b; check=check)
    @assert !iszero(nv)
    push!(B.pos, p)
    push!(B.values, nv)
  end
  return B
end

function divexact_right(A::SRow{T}, b::Integer; check::Bool=true) where T
  if length(A.values) == 0
    return deepcopy(A)
  end
  return divexact_right(A, base_ring(A)(b); check=check)
end

################################################################################
#
#  Permutation of a row
#
################################################################################

function permute_row(n::SRow{ZZRingElem}, p::Nemo.Generic.Perm{Int})
  r = Tuple{Int, ZZRingElem}[(p[i], v) for (i,v) = n]
  sort!(r, lt = (a,b)->a[1]<b[1])
  return sparse_row(ZZ, r)
end

################################################################################
#
#  Elementary row operation
#
################################################################################

@doc raw"""
    add_scaled_row(A::SRow{T}, B::SRow{T}, c::T) -> SRow{T}

Returns the row $c A + B$.
"""
add_scaled_row(a::SRow{T}, b::SRow{T}, c) where {T} = add_scaled_row!(a, deepcopy(b), c)

add_left_scaled_row(a::SRow{T}, b::SRow{T}, c) where {T} = add_left_scaled_row!(a, deepcopy(b), c)
add_right_scaled_row(a::SRow{T}, b::SRow{T}, c) where {T} = add_right_scaled_row!(a, deepcopy(b), c)



@doc raw"""
    add_scaled_row!(A::SRow{T}, B::SRow{T}, c::T) -> SRow{T}

Adds the left scaled row $c A$ to $B$.
"""
function add_scaled_row!(a::SRow{T}, b::SRow{T}, c::T, ::Val{left_side} = Val(true)) where {T, left_side}
  if a === b
    a = deepcopy(a)
  end
  i = 1
  j = 1
  t = base_ring(a)()
  while i <= length(a) && j <= length(b)
    if a.pos[i] < b.pos[j]
      t = left_side ? mul!(t, c, a.values[i]) : mul!(t, a.values[i], c)
      if !iszero(t)
        insert!(b.pos, j, a.pos[i])
        insert!(b.values, j, c*a.values[i])
        j += 1
      end
      i += 1
    elseif a.pos[i] > b.pos[j]
      j += 1
    else
      t = left_side ? mul!(t, c, a.values[i]) : mul!(t, a.values[i], c)
      b.values[j] = add!(b.values[j], t)

      if iszero(b.values[j])
        deleteat!(b.values, j)
        deleteat!(b.pos, j)
      else
        j += 1
      end
      i += 1
    end
  end
  while i <= length(a)
    t = left_side ? mul!(t, c, a.values[i]) : mul!(t, a.values[i], c)
    if !iszero(t)
      push!(b.pos, a.pos[i])
      push!(b.values, c*a.values[i])
    end
    i += 1
  end
  return b
end

add_scaled_row!(a::SRow{T}, b::SRow{T}, c) where {T} = add_scaled_row!(a, b, base_ring(a)(c))

add_scaled_row!(a::SRow{T}, b::SRow{T}, c, side::Val) where {T} = add_scaled_row!(a, b, base_ring(a)(c), side)

# ignore tmp argument
add_scaled_row!(a::SRow{T}, b::SRow{T}, c, tmp::SRow{T}) where T = add_scaled_row!(a, b, c)

add_left_scaled_row!(a::SRow{T}, b::SRow{T}, c) where T = add_scaled_row!(a, b, c)

@doc raw"""
    add_right_scaled_row!(A::SRow{T}, B::SRow{T}, c::T) -> SRow{T}

Return the right scaled row $A c$ to $B$ by changing $B$ in place.
"""
add_right_scaled_row!(a::SRow{T}, b::SRow{T}, c) where T = add_scaled_row!(a, b, c, Val(false))


################################################################################
#
#  Mutating arithmetics
#
################################################################################

function zero!(z::SRow)
  return empty!(z)
end

function neg!(z::SRow{T}, x::SRow{T}) where T
  if z === x
    return neg!(x)
  end
  swap!(z, -x)
  return z
end

function neg!(z::SRow)
  for i in 1:length(z)
    z.values[i] = neg!(z.values[i])
  end
  return z
end

function add!(z::SRow{T}, x::SRow{T}, y::SRow{T}) where T
  if z === x
    return add!(x, y)
  elseif z === y
    return add!(y, x)
  end
  swap!(z, x + y)
  return z
end

function add!(z::SRow{T}, x::SRow{T}) where T
  if z === x
    return scale_row!(z, 2)
  end
  return add_scaled_row!(x, z, one(base_ring(x)))
end

function sub!(z::SRow{T}, x::SRow{T}, y::SRow{T}) where T
  if z === x
    return sub!(x, y)
  elseif z === y
    return neg!(sub!(y, x))
  end
  swap!(z, x - y)
  return z
end

function sub!(z::SRow{T}, x::SRow{T}) where T
  if z === x
    return empty!(z)
  end
  return add_scaled_row!(x, z, -1)
end

function mul!(z::SRow{T}, x::SRow{T}, y::SRow{T}) where T
  error("Not implemented")
end

function mul!(z::SRow{T}, x::SRow{T}, c) where T
  if z === x
    return scale_row_right!(x, c)
  end
  swap!(z, x * c)
  return z
end

function mul!(z::SRow{T}, c, y::SRow{T}) where T
  if z === y
    return scale_row_left!(y, c)
  end
  swap!(z, c * y)
  return z
end

function addmul!(z::SRow{T}, x::SRow{T}, y::SRow{T}) where T
  error("Not implemented")
end

function addmul!(z::SRow{T}, x::SRow{T}, y) where T
  if z === x
    return scale_row_right!(x, y+1)
  end
  return add_right_scaled_row!(x, z, y)
end

function addmul!(z::SRow{T}, x, y::SRow{T}) where T
  if z === x
    return scale_row_left!(y, x+1)
  end
  return add_left_scaled_row!(y, z, x)
end

function submul!(z::SRow{T}, x::SRow{T}, y::SRow{T}) where T
  error("Not implemented")
end

function submul!(z::SRow{T}, x::SRow{T}, y) where T
  if z === x
    return scale_row_right!(x, -y+1)
  end
  return add_right_scaled_row!(x, z, -y)
end

function submul!(z::SRow{T}, x, y::SRow{T}) where T
  if z === x
    return scale_row_left!(y, -x+1)
  end
  return add_left_scaled_row!(y, z, -x)
end


# ignore temp variable
addmul!(z::SRow{T}, x::SRow{T}, y, t) where T = addmul!(z, x, y)
addmul!(z::SRow{T}, x, y::SRow{T}, t) where T = addmul!(z, x, y)
submul!(z::SRow{T}, x::SRow{T}, y, t) where T = submul!(z, x, y)
submul!(z::SRow{T}, x, y::SRow{T}, t) where T = submul!(z, x, y)


################################################################################
#
#  Lifting
#
################################################################################

@doc raw"""
    lift(A::SRow{zzModRingElem}) -> SRow{ZZRingElem}

Return the sparse row obtained by lifting all entries in $A$.
"""
function lift(A::SRow{zzModRingElem})
  b = sparse_row(ZZ)
  for (p,v) = A
    push!(b.pos, p)
    push!(b.values, lift(v))
  end
  return b
end

################################################################################
#
#  2-norm
#
################################################################################

@doc raw"""
    norm2(A::SRow{T} -> T

Returns $A \cdot A^t$.
"""
function norm2(A::SRow{T}) where {T}
  return sum(T[x * x for x in A.values]; init = zero(base_ring(A)))
end

################################################################################
#
#  Maximum/minimum
#
################################################################################

@doc raw"""
    maximum(abs, A::SRow{ZZRingElem}) -> ZZRingElem

Returns the largest, in absolute value, entry of $A$.
"""
function maximum(::typeof(abs), A::SRow{ZZRingElem})
  if iszero(A)
    return zero(ZZ)
  end
  m = abs(A.values[1])
  for j in 2:length(A)
    if cmpabs(m, A.values[j]) < 0
      m = A.values[j]
    end
  end
  return abs(m)
end

@doc raw"""
    maximum(A::SRow{T}) -> T

Returns the largest entry of $A$.
"""
function maximum(A::SRow)
  return maximum(A.values)
end

@doc raw"""
    minimum(A::SRow{T}) -> T

Returns the smallest entry of $A$.
"""
function minimum(A::SRow)
  return minimum(A.values)
end

################################################################################
#
#  Conversion from/to julia and AbstractAlgebra types
#
################################################################################

@doc raw"""
    Vector(a::SMat{T}, n::Int) -> Vector{T}

The first `n` entries of `a`, as a julia vector.
"""
function Vector(r::SRow, n::Int)
  A = elem_type(base_ring(r))[zero(base_ring(r)) for _ in 1:n]
  for i in intersect(r.pos, 1:n)
    A[i] = r[i]
  end
  return A
end

@doc raw"""
    sparse_row(A::MatElem)

Convert `A` to a sparse row.
`nrows(A) == 1` must hold.
"""
function sparse_row(A::MatElem)
  @assert nrows(A) == 1
  if ncols(A) == 0
    return sparse_row(base_ring(A))
  end
  return Hecke.sparse_matrix(A)[1]
end

@doc raw"""
    dense_row(r::SRow, n::Int)

Convert `r[1:n]` to a dense row, that is an AbstractAlgebra matrix.
"""
function dense_row(r::SRow, n::Int)
  A = zero_matrix(base_ring(r), 1, n)
  for i in intersect(r.pos, 1:n)
    A[1,i] = r[i]
  end
  return A
end
