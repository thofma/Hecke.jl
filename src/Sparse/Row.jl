export sparse_row, dot, scale_row!, add_scaled_row, permute_row

################################################################################
#
#  Parent constructor
#
################################################################################

function SRowSpace(R::Ring; cached = true)
  T = elem_type(R)
  return SRowSpace{T}(R)
end

base_ring(A::SRow{ZZRingElem}) = FlintZZ

base_ring(A::SRow{QQFieldElem}) = FlintQQ

function base_ring(A::SRow{T}) where {T}
  if isdefined(A, :base_ring)
    return A.base_ring::parent_type(T)
  elseif length(A.values) > 0
    return parent(A.values[1])
  else
    throw(error("Base ring of empty row not defined"))
  end
end

==(x::SRow{T}, y::SRow{T}) where {T} = (x.pos == y.pos) && (x.values == y.values)

################################################################################
#
#  Sparse row creation
#
################################################################################

@doc Markdown.doc"""
    sparse_row(R::Ring) -> SRow

Constructs an empty row with base ring $R$.
"""
function sparse_row(R::Ring)
  return SRow{elem_type(R)}(R)
end

function SRow(R::Ring)
  return SRow{elem_type(R)}(R)
end

const _sort = sort
@doc Markdown.doc"""
    sparse_row(R::Ring, J::Vector{Tuple{Int, T}}) -> SRow{T}

Constructs the sparse row $(a_i)_i$ with $a_{i_j} = x_j$, where $J = (i_j, x_j)_j$.
The elements $x_i$ must belong to the ring $R$.
"""
function sparse_row(R::Ring, A::Vector{Tuple{Int, T}}; sort::Bool = true) where T
  if sort
    A = _sort(A, lt=(a,b) -> isless(a[1], b[1]))
  end
  return SRow{T}(R, A)
end

@doc Markdown.doc"""
    sparse_row(R::Ring, J::Vector{Tuple{Int, Int}}) -> SRow

Constructs the sparse row $(a_i)_i$ over $R$ with $a_{i_j} = x_j$,
where $J = (i_j, x_j)_j$.
"""
function sparse_row(R::Ring, A::Vector{Tuple{Int, Int}}; sort::Bool = true)
  if sort
    A = _sort(A, lt=(a,b)->isless(a[1], b[1]))
  end
  return SRow{elem_type(R)}(R, A)
end

@doc Markdown.doc"""
    sparse_row(R::Ring, J::Vector{Int}, V::Vector{T}) -> SRow{T}

Constructs the sparse row $(a_i)_i$ over $R$ with $a_{i_j} = x_j$, where
$J = (i_j)_j$ and $V = (x_j)_j$.
"""
function sparse_row(R::Ring, pos::Vector{Int}, val::Vector{T}; sort::Bool = true) where T
  if sort
    p = sortperm(pos)
    pos = pos[p]
    val = val[p]
  end
  if T === elem_type(R)
    return SRow{T}(R, pos, val)
  else
    mapval = map(R, val)::Vector{elem_type(R)}
    return SRow{elem_type(R)}(R, pos, mapval)
  end
end

function sparse_row(M::ZZMatrix)
  pos = Int[]
  vals = ZZRingElem[]
  for i = 1:ncols(M)
    if is_zero_entry(M, 1, i)
      continue
    end
    push!(pos, i)
    push!(vals, M[1, i])
  end
  return SRow{ZZRingElem}(FlintZZ, pos, vals)
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
  print(io, "Sparse row with positions $(A.pos) and values $(A.values)\n")
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

@doc Markdown.doc"""
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

@doc Markdown.doc"""
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
@doc Markdown.doc"""
    mod_sym!(A::SRow{ZZRingElem}, n::Integer) -> SRow{ZZRingElem}

Inplace reduction of all entries of $A$ modulo $n$ to the symmetric residue
system.
"""
function mod_sym!(A::SRow{ZZRingElem}, n::Integer)
  mod_sym!(A, ZZRingElem(n))
end

@doc Markdown.doc"""
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

@doc Markdown.doc"""
    change_base_ring(R::Ring, A::SRow) -> SRow

Create a new sparse row by coercing all elements into the ring $R$.
"""
function change_base_ring(R::S, A::SRow{T}) where {T <: RingElem, S <: Ring}
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
@doc Markdown.doc"""
    getindex(A::SRow, j::Int) -> RingElem

Given a sparse row $(a_i)_{i}$ and an index $j$ return $a_j$.
"""
function Base.getindex(A::SRow{T}, i::Int) where {T <: RingElem}
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

@doc Markdown.doc"""
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

Base.eltype(::Type{SRow{T}}) where T = Tuple{Int, T}

Base.IteratorSize(::SRow{T}) where T = Base.HasLength()

################################################################################
#
#  Dot product
#
################################################################################

@doc Markdown.doc"""
    dot(A::SRow, B::SRow) -> RingElem

Returns the dot product of $A$ and $B$.
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
      v += B.values[b] * A.values[a]
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

function scale_row!(a::SRow{T}, b::T) where T
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
  return add_scaled_row(A, B, one(base_ring(A)))
end

function -(A::SRow{T}, B::SRow{T}) where T
  if length(A) == 0
    if length(B) == 0
      return A
    else
      return add_scaled_row(B, A, base_ring(B)(-1))
    end
  end
  return add_scaled_row(B, A, base_ring(A)(-1))
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
  for (p,v) = A
    nv = v*b
    if !iszero(nv)  # there are zero divisors - potentially
      push!(B.pos, p)
      push!(B.values, nv)
    end
  end
  return B
end

function *(b::Integer, A::SRow{T}) where T
  if length(A.values) == 0
    return sparse_row(base_ring(A))
  end
  return base_ring(A)(b)*A
end

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

function divexact(A::SRow{T}, b::T) where T
  B = sparse_row(base_ring(A))
  if iszero(b)
    return error("Division by zero")
  end
  for (p,v) = A
    nv = divexact(v, b)
    @assert !iszero(nv)
    push!(B.pos, p)
    push!(B.values, nv)
  end
  return B
end

function divexact(A::SRow{T}, b::Integer) where T
  if length(A.values) == 0
    return deepcopy(A)
  end
  return divexact(A, base_ring(A)(b))
end

################################################################################
#
#  Permutation of a row
#
################################################################################

function permute_row(n::SRow{ZZRingElem}, p::Nemo.Generic.Perm{Int})
  r = Tuple{Int, ZZRingElem}[(p[i], v) for (i,v) = n]
  sort!(r, lt = (a,b)->a[1]<b[1])
  return sparse_row(FlintZZ, r)
end

################################################################################
#
#  Elementary row operation
#
################################################################################

@doc Markdown.doc"""
    add_scaled_row(A::SRow{T}, B::SRow{T}, c::T) -> SRow{T}

Returns the row $c A + B$.
"""
add_scaled_row(a::SRow{T}, b::SRow{T}, c::T) where {T} = add_scaled_row!(a, deepcopy(b), c)

@doc Markdown.doc"""
    add_scaled_row!(A::SRow{T}, B::SRow{T}, c::T) -> SRow{T}

Returns the row $c A + B$ by changing $B$ in place.
"""
function add_scaled_row!(a::SRow{T}, b::SRow{T}, c::T) where T
  @assert a !== b
  i = 1
  j = 1
  t = base_ring(a)()
  while i <= length(a) && j <= length(b)
    if a.pos[i] < b.pos[j]
      insert!(b.pos, j, a.pos[i])
      insert!(b.values, j, c*a.values[i])
      i += 1
      j += 1
    elseif a.pos[i] > b.pos[j]
      j += 1
    else
      t = mul!(t, c, a.values[i])
      b.values[j] = addeq!(b.values[j], t)

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
    push!(b.pos, a.pos[i])
    push!(b.values, c*a.values[i])
    i += 1
  end
  return b
end

function add_scaled_row(Ai::SRow{ZZRingElem}, Aj::SRow{ZZRingElem}, c::ZZRingElem)
  sr = sparse_row(FlintZZ)
  pi = 1
  pj = 1
  @assert c != 0
  n = ZZRingElem()
  nb = 0
  while pi <= length(Ai.pos) && pj <= length(Aj.pos)
    if Ai.pos[pi] < Aj.pos[pj]
      push!(sr.pos, Ai.pos[pi])
      push!(sr.values, c*Ai.values[pi])
      pi += 1
    elseif Ai.pos[pi] > Aj.pos[pj]
      push!(sr.pos, Aj.pos[pj])
      push!(sr.values, Aj.values[pj])
      pj += 1
    else
      n = mul!(n, c, Ai.values[pi])
      n = add!(n, n, Aj.values[pj])

#      n = c*Ai.values[pi] + Aj.values[pj]
      if !iszero(n)
        nb = max(nb, nbits(n))
        push!(sr.pos, Ai.pos[pi])
        push!(sr.values, n)
        n = ZZRingElem()
      end
      pi += 1
      pj += 1
    end
  end
  while pi <= length(Ai.pos)
    push!(sr.pos, Ai.pos[pi])
    push!(sr.values, c*Ai.values[pi])
    pi += 1
  end
  while pj <= length(Aj.pos)
    push!(sr.pos, Aj.pos[pj])
    push!(sr.values, Aj.values[pj])
    pj += 1
  end
#  @show nb
  return sr
end

function add_scaled_row!(Ai::SRow{ZZRingElem}, Aj::SRow{ZZRingElem}, c::ZZRingElem)
  sr = sparse_row(FlintZZ)
  pi = 1
  pj = 1
  @assert c != 0
  n = ZZRingElem()
  nb = 0
  while pi <= length(Ai.pos) && pj <= length(Aj.pos)
    if Ai.pos[pi] < Aj.pos[pj]
      push!(sr.pos, Ai.pos[pi])
      push!(sr.values, c*Ai.values[pi])
      pi += 1
    elseif Ai.pos[pi] > Aj.pos[pj]
      push!(sr.pos, Aj.pos[pj])
      push!(sr.values, Aj.values[pj])
      pj += 1
    else
      n = mul!(n, c, Ai.values[pi])
      n = add!(n, n, Aj.values[pj])

#      n = c*Ai.values[pi] + Aj.values[pj]
      if !iszero(n)
        nb = max(nb, nbits(n))
        push!(sr.pos, Ai.pos[pi])
        push!(sr.values, n)
        n = ZZRingElem()
      end
      pi += 1
      pj += 1
    end
  end
  while pi <= length(Ai.pos)
    push!(sr.pos, Ai.pos[pi])
    push!(sr.values, c*Ai.values[pi])
    pi += 1
  end
  while pj <= length(Aj.pos)
    push!(sr.pos, Aj.pos[pj])
    push!(sr.values, Aj.values[pj])
    pj += 1
  end
#  @show nb
  Aj.pos = sr.pos
  Aj.values = sr.values
  return sr
end



################################################################################
#
#  Lifting
#
################################################################################

@doc Markdown.doc"""
    lift(A::SRow{zzModRingElem}) -> SRow{ZZRingElem}

Return the sparse row obtained by lifting all entries in $A$.
"""
function lift(A::SRow{zzModRingElem})
  b = sparse_row(FlintZZ)
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

@doc Markdown.doc"""
    norm2(A::SRow{T} -> T

Returns $A \cdot A^t$.
"""
function norm2(A::SRow{T}) where {T}
  return sum([x * x for x in A.values])
end

################################################################################
#
#  Maximum/minimum
#
################################################################################

@doc Markdown.doc"""
    maximum(abs, A::SRow{ZZRingElem}) -> ZZRingElem

Returns the largest, in absolute value, entry of $A$.
"""
function maximum(::typeof(abs), A::SRow{ZZRingElem})
  if iszero(A)
    return zero(FlintZZ)
  end
  m = abs(A.values[1])
  for j in 2:length(A)
    if cmpabs(m, A.values[j]) < 0
      m = A.values[j]
    end
  end
  return abs(m)
end

@doc Markdown.doc"""
    maximum(A::SRow{T}) -> T

Returns the largest entry of $A$.
"""
function maximum(A::SRow)
  return maximum(A.values)
end

@doc Markdown.doc"""
    minimum(A::SRow{T}) -> T

Returns the smallest entry of $A$.
"""
function minimum(A::SRow)
  return minimum(A.values)
end
