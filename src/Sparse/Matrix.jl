################################################################################
#
#  Parent constructor
#
################################################################################

function SMatSpace(R::Ring, r::Int, c::Int)
  T = elem_type(R)
  return SMatSpace{T}(R, r, c)
end

################################################################################
#
#  Basic functions
#
################################################################################

base_ring(A::SMatSpace{T}) where {T} = A.base_ring::parent_type(T)

base_ring_type(::Type{SMatSpace{T}}) where {T} = parent_type(T)

parent(A::SMat) = SMatSpace(base_ring(A), A.r, A.c)

base_ring(A::SMat{T}) where {T} = A.base_ring::parent_type(T)

base_ring_type(::Type{<:SMat{T}}) where {T} = parent_type(T)


@doc raw"""
    sparse_matrix_type(a)

Return the type of the sparse matrix type of the given element, element type, parent or parent type $a$.

# Examples
```jldoctest
julia> x = sparse_matrix(QQ)
Sparse 0 x 0 matrix with 0 non-zero entries

julia> sparse_matrix_type(QQ) == typeof(x)
true

julia> sparse_matrix_type(zero(QQ)) == typeof(x)
true

julia> sparse_matrix_type(typeof(QQ)) == typeof(x)
true

julia> sparse_matrix_type(typeof(zero(QQ))) == typeof(x)
true
```
"""
sparse_matrix_type(::T) where {T <: Union{Ring, RingElem}} = sparse_matrix_type(T)
sparse_matrix_type(::Type{T}) where {T <: Ring} = sparse_matrix_type(elem_type(T))
sparse_matrix_type(::Type{T}) where {T <: RingElem} = SMat{T, sparse_inner_type(T)}


@doc raw"""
    number_of_rows(A::SMat) -> Int

Return the number of rows of $A$.
"""
function number_of_rows(A::SMat)
  @assert A.r == length(A.rows)
  return A.r
end

@doc raw"""
    number_of_columns(A::SMat) -> Int

Return the number of columns of $A$.
"""
function number_of_columns(A::SMat)
  return A.c
end

#used in HNF.jl:
# sparse_row operations usually involve a temporary intermediate row
# for large matrices, this kills the GC performance, so we allow
# to store up to 10 sparse auxiliaries in the matrix..
# usage:
# sr = get_tmp(A)
# add_scaled_row(..., sr)
# release_tmp(A, sr)
#
# get_tmp_scalar(A, n) similarly gets n temporary values - that should be
# release_tmp_scalar(A, [a_1, ..., a_n]) for resuse
# pattern
# a, b, c = tmp_vals = get_tmp_scalar(A, 3)
# ... using many "!" functions
# release_tmp_scalar(A, tmp_vals)
#
function get_tmp(A::SMat)
  if isdefined(A, :tmp) && length(A.tmp) > 0
    return pop!(A.tmp)
  end
  return sparse_row(base_ring(A))
end

function release_tmp(A::SMat{T}, s::SRow{T}) where T
  if isdefined(A, :tmp)
    if length(A.tmp) < 10
      push!(A.tmp, s)
    end
  else
    A.tmp = [s]
  end
end

function get_tmp_scalar(A::SMat, i::Int)
#  return zeros(base_ring(A), i)
  if !isdefined(A, :tmp_scalar)
    A.tmp_scalar = zeros(base_ring(A), i)
  end
  s = A.tmp_scalar
  if length(s) < i
    append!(s, zeros(base_ring(A), i+1-length(s)))
  end
  @inbounds ret = s[length(s)-i+1:length(s)]
  resize!(s, length(s)-i)
  return ret
end

function release_tmp_scalar(A::SMat{T}, s::Vector{T}) where T
#  return
  if length(A.tmp_scalar) < 10
    append!(A.tmp_scalar, s)
  end
  return nothing
end


@doc raw"""
    nnz(A::SMat) -> Int

Return the number of non-zero entries of $A$.
"""
function nnz(A::SMat)
  return A.nnz
end

size(A::SMat) = (nrows(A), ncols(A))
size(A::SMat, i::Int64) = i <= 2 ? size(A)[i] : 1

################################################################################
#
#  Hashing
#
################################################################################

function hash(A::SMat, h::UInt)
  return hash(A.r, hash(A.c, hash(A.rows, h)))
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(M::SMat, dict::IdDict)
  N = sparse_matrix(base_ring(M))
  N.r = M.r
  N.c = M.c
  N.nnz = M.nnz
  N.rows = Base.deepcopy_internal(M.rows, dict)
  return N
end

################################################################################
#
#  Comparison
#
################################################################################

function ==(x::SMat{T}, y::SMat{T}) where T
  return base_ring(x) == base_ring(y) && x.rows == y.rows && ncols(x) == ncols(y)
end

################################################################################
#
#  Sparsity and density
#
################################################################################

@doc raw"""
    sparsity(A::SMat) -> Float64

Return the sparsity of `A`, that is, the number of zero-valued elements divided
by the number of all elements.
"""
function sparsity(A::SMat)
  return 1.0 - nnz(A)/(nrows(A) * ncols(A))
end

@doc raw"""
    density(A::SMat) -> Float64

Return the density of `A`, that is, the number of nonzero-valued elements
divided by the number of all elements.
"""
density(A::SMat) = 1.0 - sparsity(A)

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, A::SMat{T}) where T
  print(io, "Sparse ", A.r, " x ", A.c, " matrix with ")
  print(io, A.nnz, " non-zero entries")
end

################################################################################
#
#  Empty sparse matrix (given base ring)
#
################################################################################

@doc raw"""
    sparse_matrix(R::Ring) -> SMat

Return an empty sparse matrix with base ring $R$.
"""
function sparse_matrix(R::Ring)
  T = sparse_matrix_type(R)
  r = T()::T
  r.base_ring = R
  return r
end

@doc raw"""
    sparse_matrix(R::Ring, n::Int, m::Int) -> SMat

Return a sparse $n$ times $m$ zero matrix over $R$.
"""
function sparse_matrix(R::Ring, n::Int, m::Int)
  S = sparse_matrix(R)
  S.rows = [sparse_row(R) for i=1:n]
  S.r = n
  S.c = m
  return S
end

################################################################################
#
#  Copy
#
################################################################################

function copy(A::SMat{T}) where T
  return sub(A, 1:nrows(A), 1:ncols(A))
end

################################################################################
#
#  Entry/row access
#
################################################################################

@doc raw"""
    getindex(A::SMat, i::Int, j::Int)

Given a sparse matrix $A = (a_{ij})_{i, j}$, return the entry $a_{ij}$.
"""
function getindex(A::SMat{T}, i::Int, j::Int) where T
  if i in 1:A.r
    ra = A.rows[i]
    p = searchsortedfirst(ra.pos, j)
    if p <= length(ra.pos) && ra.pos[p] == j
      return ra.values[p]
    end
  end
  return zero(base_ring(A))
end

@doc raw"""
    getindex(A::SMat, i::Int) -> SRow

Given a sparse matrix $A$ and an index $i$, return the $i$-th row of $A$.
"""
@inline function getindex(A::SMat{T}, i::Int) where T
   @boundscheck (i < 1 || i > nrows(A)) && error("Index must be between 1 and $(nrows(A))")
  return @inbounds A.rows[i]
end

@doc raw"""
    setindex!(A::SMat, b::SRow, i::Int)

Given a sparse matrix $A$, a sparse row $b$ and an index $i$, set the $i$-th
row of $A$ equal to $b$.
"""
function setindex!(A::SMat{T}, b::SRow{T}, i::Int) where T
  (i < 1 || i > nrows(A)) && error("Index must be between 1 and $(nrows(A))")
  A.nnz = A.nnz - length(A.rows[i].pos) + length(b.pos)
  A.rows[i] = b
  return A
end

################################################################################
#
#  Random row from sparse matrix
#
################################################################################

@doc raw"""
    rand_row(A::SMat) -> SRow

Return a random row of the sparse matrix $A$.
"""
function rand_row(A::SMat{T}) where T
  return rand(A.rows)
end

################################################################################
#
#  Sparse matrix constructors
#
################################################################################

# A dangerous interface for checking whether an entry is zero
#
# fl, t = _is_zero_entry(A, i, j)
# then A[i, j] == _get(t)
#
# This is to avoid the allocation and double "lookup" for flint matrices
#
# WARNING: The function calling _is_zero_entry(A, i, j) must call this inside a
# GC.@preserve A block

@inline function _is_zero_entry(A::ZZMatrix, i, j)
  x = mat_entry_ptr(A, i, j)
  return ccall((:fmpz_is_zero, libflint), Bool, (Ptr{ZZRingElem},), x), x
end

@inline function _is_zero_entry(A::MatElem, i, j)
  t = A[i, j]
  return iszero(t), t
end

@inline function _get(x::Ptr{ZZRingElem})
  z = ZZRingElem()
  set!(z, x)
  return z
end

_get(x::RingElem) = x

@doc raw"""
    sparse_matrix(A::MatElem; keepzrows::Bool = true)

Constructs the sparse matrix corresponding to the dense matrix $A$. If
`keepzrows` is false, then the constructor will drop any zero row of $A$.
"""
function sparse_matrix(A::MatElem; keepzrows::Bool = true)
  R = base_ring(A)
  m = sparse_matrix(R)
  m.c = ncols(A)
  m.r = 0

  GC.@preserve A begin
    for i=1:nrows(A)
      if is_zero_row(A, i)
        if !keepzrows
          continue
        else
          r = sparse_row(R)
        end
      else
        r = sparse_row(R)
        for j = 1:ncols(A)
          t, el = _is_zero_entry(A, i, j)
          if !t
            m.nnz += 1
            push!(r.values, _get(el))
            push!(r.pos, j)
          end
        end
      end
      push!(m.rows, r)
      m.r += 1
    end
  end
  return m
end

@doc raw"""
    sparse_matrix(A::Matrix{T}) -> SMat{T}

Constructs the sparse matrix corresponding to $A$.
"""
function sparse_matrix(A::Matrix{T}) where {T <: RingElement}
  length(A) == 0 && error("Cannot create sparse matrix from empty array")
  m = sparse_matrix(parent(A[1, 1]))
  m.c = Base.size(A, 2)
  m.r = 0
  for i in 1:size(A, 1)
    if is_zero_row(A, i)
      push!(m, sparse_row(parent(A[1, 1])))
      continue
    end
    r = sparse_row(parent(A[1, 1]))
    for j in 1:size(A, 2)
      if !iszero(A[i, j])
        m.nnz += 1
        push!(r.values, A[i, j])
        push!(r.pos, j)
      end
    end
    push!(m.rows, r)
    m.r += 1
  end
  return m
end

@doc raw"""
    sparse_matrix(R::Ring, A::Matrix{T}) -> SMat

Constructs the sparse matrix over $R$ corresponding to $A$.
"""
function sparse_matrix(R::Ring, A::Matrix{T}) where {T}
  B = convert(Matrix{elem_type(R)}, map(R, A))
  return sparse_matrix(B)
end

function (M::SMatSpace)(A::T; R::S = base_ring(A),
                                 keepzrows::Bool = true) where {T <: MatElem, S <: Ring}
  return sparse_matrix(A, R, keepzrows)
end

function (M::SMatSpace)(A::Matrix{T}) where T <: MatElem
  return sparse_matrix(A)
end

################################################################################
#
#  Modular reduction
#
################################################################################

@doc raw"""
    mod_sym!(A::SMat{ZZRingElem}, n::ZZRingElem)

Inplace reduction of all entries of $A$ modulo $n$ to the symmetric residue
system.
"""
function mod_sym!(A::SMat{ZZRingElem}, b::ZZRingElem)
  for r in A
    mod_sym!(r, b)
  end
  return A
end

################################################################################
#
#  Ring change
#
################################################################################

@doc raw"""
    map_entries(f, A::SMat) -> SMat

Given a sparse matrix $A$ and a callable object $f$, this function will
construct a new sparse matrix by applying $f$ to all elements of $A$.
"""
function map_entries(f, A::SMat{T}) where {T}
  x = zero(base_ring(A))
  y = f(x)
  S = parent(y)
  z = sparse_matrix(S)
  z.c = ncols(A)
  z.nnz = 0
  for r in A
    if iszero(r)
      push!(z, sparse_row(S))
    else
      rf = map_entries(f, r)
      push!(z, rf)
    end
  end
  return z
end

@doc raw"""
    change_base_ring(R::Ring, A::SMat)

Create a new sparse matrix by coercing all elements into the ring $R$.
"""
function change_base_ring(R::Ring, A::SMat)
  z = sparse_matrix(R)
  z.c = A.c
  for r in A
    rz = change_base_ring(R, r)
    push!(z, rz)
  end
  return z
end

################################################################################
#
#  Transpose
#
################################################################################

@doc raw"""
    transpose(A::SMat) -> SMat

Returns the transpose of $A$.
"""
function transpose(A::SMat{T}) where {T}
  R = base_ring(A)
  B = sparse_matrix(R)
  n = nrows(A)
  m = ncols(A)
  B.rows = Vector{SRow{T}}(undef, m)
  t = R()
  for i=1:m
    B.rows[i] = sparse_row(R)
  end
  for i = 1:length(A.rows)
    for j = 1:length(A.rows[i].pos)
      r = A.rows[i].pos[j]
      push!(B.rows[r].pos, i)
      t = getindex!(t, A.rows[i].values, j) #this only works if push copies, kind of
      push!(B.rows[r].values, t) #A.rows[i].values[j])
    end
  end
  B.c = n
  B.r = m
  B.nnz = A.nnz
  return B
end

################################################################################
#
#  Make sparse matrices iterable
#
################################################################################

function endof(A::SMat)
  return length(A.rows)
end

function Base.iterate(A::SMat, st::Int = 1)
  if st > nrows(A)
    return nothing
  end

  return A.rows[st], st + 1
end

function length(A::SMat)
  return nrows(A)
end

Base.eltype(::Type{<:SMat{T}}) where {T} = SRow{T}

################################################################################
#
#  Multiplication
#
################################################################################

# SMat{T} * Vector{T} as (dense Vector{T})
# inplace
function mul!(c::Vector{T}, A::SMat{T}, b::AbstractVector{T}) where T
  R = base_ring(A)
  z = zero(R)
  for (i, r) in enumerate(A)
    c[i] = dot(r, b, z)
  end
  return c
end

# (dense Vector{T}) * SMat{T} as (dense Vector{T})
@doc raw"""
    *(A::SMat{T}, b::AbstractVector{T}) -> Vector{T}

Return the product $A \cdot b$ as a dense vector.
"""
function *(A::SMat{T}, b::AbstractVector{T}) where T
  @assert length(b) == ncols(A)
  c = Vector{T}(undef, nrows(A))
  mul!(c, A, b)
  return c
end

function mul!(c::Matrix{T}, A::SMat{T}, b::AbstractMatrix{T}) where T
  sz = size(b)
  @assert sz[1] == ncols(A)
  tz = size(c)
  @assert tz[1] == nrows(A)
  @assert tz[2] == sz[2]
  z = zero(base_ring(A))
  for m in 1:size(b, 2)
    for i in 1:nrows(A)
      c[i, m] = dot(A.rows[i], view(b, :, m), z)
    end
  end
  return c
end

# - SMat{T} * Matrix{T} as Matrix{T}
@doc raw"""
    *(A::SMat{T}, b::AbstractMatrix{T}) -> Matrix{T}

Return the product $A \cdot b$ as a dense array.
"""
function *(A::SMat{T}, b::AbstractMatrix{T}) where T
  sz = size(b)
  @assert sz[1] == ncols(A)
  c = Array{T}(undef, sz[1], sz[2])
  return mul!(c, A, b)
end

# - SMat{T} * MatElem as MatElem
# - Inplace
function mul!(c::MatElem{T}, A::SMat{T}, b::MatElem{T}) where T
  @assert nrows(b) == ncols(A)
  @assert nrows(c) == nrows(A)
  @assert ncols(c) == ncols(b)
  for m = 1:ncols(b)
    for i = 1:nrows(A)
      c[i, m] = dot(A.rows[i], b, m)
    end
  end
  return c
end

# - SMat{T} * MatElem{T} as MatElem{T}
@doc raw"""
    *(A::SMat{T}, b::MatElem{T}) -> MatElem

Return the product $A \cdot b$ as a dense matrix.
"""
function *(A::SMat{T}, b::MatElem{T}) where T
  @assert nrows(b) == ncols(A)
  c = similar(b, nrows(A), ncols(b))
  return mul!(c, A, b)
end

# - SRow{T} * SMat{T} as SRow{T}
@doc raw"""
    *(A::SRow, B::SMat) -> SRow

Return the product $A\cdot B$ as a sparse row.
"""
function *(A::SRow{T}, B::SMat{T}) where T
  C = sparse_row(base_ring(B))
  for (p, v) in A
    if iszero(v)
      continue
    end
    C = add_scaled_row(B[p], C, v)
  end
  return C
end

################################################################################
#
#  Multiplication with reduction
#
################################################################################

# - (dense Vector{S}) * SMat{T} as (dense Vector{S}) modulo mod::S
# - Inplace
# - Reduction as the last step, no intermediate reductions.
function mul_mod!(c::Vector{S}, A::SMat{T}, b::Vector{S}, mod::S) where {S, T}
  @assert length(b) == ncols(A)
  @assert length(c) == nrows(A)

  for i = 1:length(A.rows)
    s = S(0)
    I = A.rows[i]
    for j=1:length(I.pos)
      s += S(I.values[j]) * b[I.pos[j]]
    end
    c[i] = s % mod
  end
  return c
end

# - (dense Vector{S}) * SMat{T} as (dense Vector{S}) modulo mod::S
# - Inplace
# - Intermediate reductions.
function mul_mod_big!(c::Vector{S}, A::SMat{T}, b::Vector{S}, mod::S) where {S, T}
  @assert length(b) == ncols(A)
  @assert length(c) == nrows(A)
  for i = 1:length(A.rows)
    s = 0
    I = A.rows[i]
    for j=1:length(I.pos)
      s += S(I.values[j] *b[I.pos[j]] % mod)
    end
    c[i] = s % mod
  end
  return c
end

################################################################################
#
#  Arithmetics
#
################################################################################

function -(A::SMat)
  return map_entries(-, A)
end

function +(A::SMat{T}, B::SMat{T}) where T
  nrows(A) != nrows(B) && error("Matrices must have same number of rows")
  ncols(A) != ncols(B) && error("Matrices must have same number of columns")
  C = sparse_matrix(base_ring(A), 0, ncols(A))
  m = min(nrows(A), nrows(B))
  for i=1:m
    push!(C, A[i] + B[i])
  end
  for i=m+1:nrows(A)
    push!(C, A[i])
  end
  for i=m+1:nrows(B)
    push!(C, B[i])
  end
  return C
end

function -(A::SMat{T}, B::SMat{T}) where T
  nrows(A) != nrows(B) && error("Matrices must have same number of rows")
  ncols(A) != ncols(B) && error("Matrices must have same number of columns")
  C = sparse_matrix(base_ring(A), 0, ncols(A))
  m = min(nrows(A), nrows(B))
  for i=1:m
    push!(C, A[i]-B[i])
  end
  for i=m+1:nrows(A)
    push!(C, A[i])
  end
  if m < nrows(B)
    n = base_ring(B)(-1)
    for i=m+1:nrows(B)
      push!(C, n*B[i])
    end
  end
  return C
end

#TODO: this is a problem in anther ops as well: a length zero row does not have a base_ring
################################################################################
#
#  Scalar multiplication
#
################################################################################

function *(b::T, A::SMat{T}) where {T}
  if iszero(b)
    return sparse_matrix(base_ring(A), nrows(A), ncols(A))
  end
  B = sparse_matrix(base_ring(A), 0, ncols(A))
  for a in A
    push!(B, b * a)
  end
  return B
end

function *(b, A::SMat)
  return base_ring(A)(b) * A
end

function *(A::SMat{T}, b::T) where {T}
  if iszero(b)
    return sparse_matrix(base_ring(A), nrows(A), ncols(A))
  end
  B = sparse_matrix(base_ring(A), 0, ncols(A))
  for a in A
    push!(B, a * b)
  end
  return B
end

function *(A::SMat, b)
  return A * base_ring(A)(b)
end

################################################################################
#
#  Dot product
#
################################################################################

@doc raw"""
    dot(x::SRow{T}, A::SMat{T}, y::SRow{T}) where T -> T

Return the generalized dot product `dot(x, A*y)`.
"""
function dot(x::SRow{T}, A::SMat{T}, y::SRow{T}) where T
  v = zero(T)
  px = 1
  for i in 1:length(A.rows)
    while px <= length(x.pos) && x.pos[px] < i
      px += 1
    end
    if px > length(x.pos)
      break
    elseif x.pos[px] > i
      continue
    end

    s = zero(T)
    py = 1
    for j in 1:length(A[i].pos)
      while py <= length(y.pos) && y.pos[py] < A[i].pos[j]
        py += 1
      end
      if py > length(y.pos)
        break
      elseif y.pos[py] > A[i].pos[j]
        continue
      end

      s += A[i].values[j] * y.values[py]
    end

    v += x.values[px] * s
  end

  return v
end

@doc raw"""
    dot(x::AbstractVector{T}, A::SMat{T}, y::AbstractVector{T}) where T -> T

Return the generalized dot product `dot(x, A*y)`.
"""
function dot(x::AbstractVector{T}, A::SMat{T}, y::AbstractVector{T}) where T
  @req length(x) == nrows(A) && ncols(A) <= length(y) "incompatible matrix dimensions"

  v = zero(T)
  for i in 1:length(A.rows)
    s = T(0)
    for j in 1:length(A[i].pos)
      s += A[i].values[j] * y[A[i].pos[j]]
    end
    v += x[i] * s
  end

  return v
end

@doc raw"""
    dot(x::MatrixElem{T}, A::SMat{T}, y::MatrixElem{T}) where T -> T

Return the generalized dot product `dot(x, A*y)`.
"""
function dot(x::MatrixElem{T}, A::SMat{T}, y::MatrixElem{T}) where T
  @req length(x) == nrows(A) && ncols(A) <= length(y) "incompatible matrix dimensions"

  v = zero(T)
  for i in 1:length(A.rows)
    s = zero(T)
    for j in 1:length(A[i].pos)
      s += A[i].values[j] * y[A[i].pos[j]]
    end
    v += x[i] * s
  end

  return v
end

################################################################################
#
#  Submatrix
#
################################################################################

@doc raw"""
    sub(A::SMat, r::AbstractUnitRange, c::AbstractUnitRange) -> SMat

Return the submatrix of $A$, where the rows correspond to $r$ and the columns
correspond to $c$.
"""
function sub(A::SMat{T}, r::AbstractUnitRange, c::AbstractUnitRange) where T
  B = sparse_matrix(base_ring(A))
  B.nnz = 0
  B.c = length(c)
  t = base_ring(A)()
  for i in r
    rw = sparse_row(base_ring(A))
    ra = A.rows[i]
    for j=1:length(ra.values)
      if ra.pos[j] in c
        push!(rw.values, getindex!(t, ra.values, j))
        push!(rw.pos, ra.pos[j]-first(c)+1)
      end
    end
    push!(B, rw)
  end
  return B
end

#TODO: map to getindex with ranges and slices

################################################################################
#
#  Valence
#
################################################################################

@doc raw"""
    valence_mc{T}(A::SMat{T}; extra_prime = 2, trans = Vector{SMatSLP_add_row{T}}()) -> T

Uses a Monte-Carlo algorithm to compute the valence of $A$. The valence is the
valence of the minimal polynomial $f$ of $transpose(A)*A$, thus the last non-zero
coefficient, typically $f(0)$.

The valence is computed modulo various primes until the computation stabilises
for `extra_prime` many.

`trans`, if given, is  a SLP (straight-line-program) in GL(n, Z). Then the
valence of `trans` * $A$  is computed instead.
"""
function valence_mc(A::SMat{T}; extra_prime = 2, trans = Vector{SMatSLP_add_row{T}}()) where T
  # we work in At * A (or A * At) where we choose the smaller of the 2
  # matrices
  if false && ncols(A) > nrows(A)
    At = A
    A = transpose(A)
  else
    At = transpose(A)
  end
  if maximum(abs, A) > 2^20
    mm = mul_mod_big!
    println("mul big case")
  else
    mm = mul_mod!
    println("mul small case")
  end
  c1 = Array{Int}(undef, ncols(A))
  c2 = Array{Int}(undef, nrows(A))

  for i=1:ncols(A)
    c1[i] = Int(rand(-10:10))
  end

  c = copy(c1) ## need the starting value for the other primes as well

  p = next_prime(2^30)
  k = GF(p)
  d = 10
  v = Vector{typeof(k(1))}()
  push!(v, k(c1[1]))
  while true
    while length(v) <= d
      mm(c2, A, c1, p)
      if length(trans) >0
        apply_t!(c2, trans)
        apply!(c2, trans)
      end
      mm(c1, At, c2, p)
      push!(v, k(c1[1]))
    end
    f = berlekamp_massey(v)
    fl = true
    if !fl || degree(f) > div(d, 2)-1
      d += 10
      continue
    end
    df = degree(f)
    println("Poly degree is $df, dims $(nrows(A)) x $(ncols(A))")

    V = ZZRingElem(leading_coefficient(f))
    pp = ZZRingElem(p)

    v = Array{typeof(k(1))}(undef, 2*degree(f)+1)
    while true
      p = next_prime(p)
      println(p)
      k = GF(p)
      copy!(c1, c)
      v[1] = k(c1[1])
      for i=1:2*degree(f)
        mm(c2, A, c1, p)
        if length(trans) >0
          apply_t!(c2, trans)
          apply!(c2, trans)
        end
        mm(c1, At, c2, p)
        v[i+1] = k(c1[1])
      end
      f = berlekamp_massey(v)
      fl = true
      if !fl || degree(f) > df
        println("initial guess was wrong...")
        d += 10
        return -1
      end

      Vn = crt(V, pp, ZZRingElem(leading_coefficient(f)), ZZRingElem(p))
      pp *= p
      if 2*Vn > pp
        Vn = Vn - pp
      end
      if Vn == V
        extra_prime -= 1
        if extra_prime == 0
          return V
        end
      end
      V = Vn
    end
  end
end

function valence_mc(A::SMat{T}, p::Int) where T
  # we work in At * A (or A * At) where we choose the smaller of the 2
  # matrices
  if false && ncols(A) > nrows(A)
    At = A
    A = transpose(A)
  else
    At = transpose(A)
  end
  if maximum(abs, A) > 2^20
    mm = mul_mod_big!
    println("mul big case")
  else
    mm = mul_mod!
    println("mul small case")
  end
  c1 = zeros{Int}(ncols(A))
  c2 = zeros{Int}(nrows(A))

  for i=1:ncols(A)
    c1[i] = Int(rand(-10:10))
  end

  c = copy(c1) ## need the starting value for the other primes as well

  k = GF(p)
  d = 10
  v = Vector{elem_type(k)}()
  push!(v, k(c1[1]))
  while true
    while length(v) <= d
      mm(c2, A, c1, p)
      mm(c1, At, c2, p)
      push!(v, k(c1[1]))
    end
    f = berlekamp_massey(v)
    fl = true
    if !fl || degree(f) > div(d, 2)-1
      d += 10
      continue
    end
    df = degree(f)
    return f
  end
end

################################################################################
#
#  Vertical concatenation
#
################################################################################

@doc raw"""
    vcat!(A::SMat, B::SMat) -> SMat

Vertically joins $A$ and $B$ inplace, that is, the rows of $B$ are
appended to $A$.
"""
function vcat!(A::SMat{T}, B::SMat{T}) where T
  @assert length(A.rows) == A.r
  @assert length(B.rows) == B.r
  A.r += B.r
  A.c = max(A.c, B.c)
  A.nnz += B.nnz
  A.rows = vcat(A.rows, B.rows)
  @assert length(A.rows) == A.r
end

@doc raw"""
    vcat(A::SMat, B::SMat) -> SMat

Vertically joins $A$ and $B$.
"""
function vcat(A::SMat{T}, B::SMat{T}) where T
  @assert length(A.rows) == A.r
  @assert length(B.rows) == B.r
  C = copy(A)
  vcat!(C, B)
  return C
end

################################################################################
#
#  Horizontal concatenation
#
################################################################################

@doc raw"""
    hcat!(A::SMat, B::SMat) -> SMat

Horizontally concatenates $A$ and $B$, inplace, changing $A$.
"""
function hcat!(A::SMat{T}, B::SMat{T}) where T
  o = A.c
  A.c += B.c
  nnz = A.nnz
  for i=1:min(nrows(A), nrows(B))
    for (p,v) in B[i]
      push!(A[i].pos, p+o)
      push!(A[i].values, v)
    end
  end
  for i=min(nrows(A), nrows(B))+1:nrows(B)
    sr = sparse_row(base_ring(A))
    for (p,v) in B[i]
      push!(sr.pos, p+o)
      push!(sr.values, v)
    end
    push!(A, sr)
  end
  A.nnz = nnz + B.nnz #A.nnz may have changed - if B is longer
end

@doc raw"""
    hcat(A::SMat, B::SMat) -> SMat

Horizontally concatenates $A$ and $B$.
"""
function hcat(A::SMat{T}, B::SMat{T}) where T
  C = copy(A)
  hcat!(C, B)
  return C
end

################################################################################
#
#  Append sparse row to sparse matrix
#
################################################################################

@doc raw"""
    push!(A::SMat{T}, B::SRow{T}) where T

Appends the sparse row ```B``` to ```A```.
"""
function push!(A::SMat{T}, B::SRow{T}) where T
  push!(A.rows, B)
  A.r += 1
  @assert length(A.rows) == A.r
  A.nnz += length(B.pos)
  if length(B.pos) > 0
    A.c = max(A.c, B.pos[end])
  end
  return A
end

@doc raw"""
    insert!(A::SMat{T}, i::Integer, B::SRow{T}) where T

Insert the sparse row ```B``` at position ```i``` of the rows of ```A```.
"""
function Base.insert!(A::SMat{T}, i::Integer, B::SRow{T}) where T
  insert!(A.rows, i, B)
  A.r += 1
  @assert length(A.rows) == A.r
  A.nnz += length(B.pos)
  if length(B.pos) > 0
    A.c = max(A.c, B.pos[end])
  end
  return A
end

################################################################################
#
#  Conversion to ZZMatrix
#
################################################################################

@doc raw"""
    ZZMatrix(A::SMat{T}) where {T <: Integer}

The same matrix $A$, but as an `ZZMatrix`.
Requires a conversion from the base ring of $A$ to $\mathbb ZZ$.
"""
function ZZMatrix(A::SMat{T}) where T <: Integer
  B = zero_matrix(ZZ, A.r, A.c)
  for i = 1:length(A.rows)
    ra = A.rows[i]
    for j = 1:length(ra.pos)
      B[i, ra.pos[j]] = ra.values[j]
    end
  end
  return B
end

@doc raw"""
    ZZMatrix(A::SMat{ZZRingElem})

The same matrix $A$, but as an `ZZMatrix`.
"""
function ZZMatrix(A::SMat{ZZRingElem})
  B = zero_matrix(ZZ, A.r, A.c)
  for i = 1:length(A.rows)
    ra = A.rows[i]
    for j = 1:length(ra.pos)
      B[i, ra.pos[j]] = ra.values[j]
    end
  end
  return B
end

################################################################################
#
#  Maximum, minimum and norms
#
################################################################################

@doc raw"""
    hadamard_bound2(A::SMat{T}) -> T

The square of the product of the norms of the rows of $A$.
"""
function hadamard_bound2(A::SMat)
  return prod([norm2(x) for x=A])
end

@doc raw"""
    maximum(abs, A::SMat{ZZRingElem}) -> ZZRingElem

  Finds the largest, in absolute value, entry of $A$.
"""
function maximum(::typeof(abs), A::SMat{ZZRingElem})
  if length(A.rows) == 0
    return zero(ZZ)
  end
  m = ZZ()
  first = true
  for i in A.rows
    if first
      m = maximum(abs, i)
      first = false
    else
      m = max(m, maximum(abs, i))
    end
  end
  return abs(m)
end

@doc raw"""
    maximum(A::SMat{T}) -> T

Finds the largest entry of $A$.
"""
function maximum(A::SMat)
  m = base_ring(A)()
  first = true
  for i in A
    if first
      m = maximum(i)
      first = false
    else
      m = max(m, maximum(i))
    end
  end
  return m
end

@doc raw"""
    minimum(A::SMat{T}) -> T

Finds the smallest entry of $A$.
"""
function minimum(A::SMat)
  m = base_ring(A)()
  first = true
  for i in A.rows
    if first
      m = minimum(i)
      first = false
    else
      m = min(m, minimum(i))
    end
  end
  return m
end

function maximum(::typeof(nbits), A::SMat{ZZRingElem})
  if length(A.rows) == 0
    return zero(ZZ)
  end
  m = nbits(A.rows[1].values[1])
  for i in A.rows
    m = max(m, maximum(nbits, i))
  end
  return m
end


################################################################################
#
#  Test upper triangular shape
#
################################################################################

@doc raw"""
    is_upper_triangular(A::SMat)

Returns true if and only if $A$ is upper (right) triangular.
"""
function is_upper_triangular(A::SMat)
  for i=2:A.r
    if iszero(A[i - 1])
      if iszero(A[i])
        continue
      else
        return false
      end
    else
      if iszero(A[i])
        continue
      else
        if A[i - 1].pos[1] >= A[i].pos[1]
          return false
        else
          continue
        end
      end
    end
  end
  return true
end

################################################################################
#
#  Sparse to dense
#
################################################################################

function Nemo.matrix(A::SMat)
  R = base_ring(A)
  M = zero_matrix(R, nrows(A), ncols(A))
  for i=1:nrows(A)
    for j=1:length(A.rows[i].pos)
      M[i, A.rows[i].pos[j]] = A.rows[i].values[j]
    end
  end
  return M
end

################################################################################
#
#  Identity matrices
#
################################################################################

@doc raw"""
    identity_matrix(::Type{SMat}, R::Ring, n::Int)

Return a sparse $n$ times $n$ identity matrix over $R$.
"""
function identity_matrix(::Type{SMat}, R::Ring, n::Int)
  A = sparse_matrix(R)
  A.c = n
  for i in 1:n
    push!(A, sparse_row(R, [i], [one(R)]))
  end
  return A
end

@doc raw"""
    zero_matrix(::Type{SMat}, R::Ring, n::Int)

Return a sparse $n$ times $n$ zero matrix over $R$.
"""
zero_matrix(::Type{SMat}, R::Ring, n::Int) = sparse_matrix(R, n, n)

@doc raw"""
    zero_matrix(::Type{SMat}, R::Ring, n::Int, m::Int)

Return a sparse $n$ times $m$ zero matrix over $R$.
"""
zero_matrix(::Type{SMat}, R::Ring, n::Int, m::Int) = sparse_matrix(R, n, m)

similar(A::SMat) = sparse_matrix(base_ring(A), nrows(A), ncols(A))

similar(A::SMat, m::Int, n::Int) = sparse_matrix(base_ring(A), m, n)

################################################################################
#
#  Block diagonal matrices
#
################################################################################

function diagonal_matrix(V::Vector{<:SMat{T}}) where {T}
  return block_diagonal_matrix(V)
end

function diagonal_matrix(x::SMat{T}, xs::SMat{T}...) where {T}
  return block_diagonal_matrix([x, xs...])
end

@doc raw"""
    block_diagonal_matrix(xs::Vector{SMat})

Return the block diagonal matrix with the matrices in `xs` on the diagonal.
Requires all blocks to have the same base ring.
"""
function block_diagonal_matrix(xs::Vector{<:SMat{T}}) where {T}
  @req length(xs) > 0 "At least one matrix is required"
  R = base_ring(xs[1])
  @req all(x -> base_ring(x) == R, xs) "All matrices must have the same base ring"
  rows = sum(nrows(N) for N in xs)
  cols = sum(ncols(N) for N in xs)
  M = similar(xs[1], rows, cols)
  i_offset = 0
  j_offset = 0
  for x in xs
    for (i, x_row) in enumerate(x)
      M_row = sparse_row(R, x_row.pos .+ j_offset, x_row.values)
      setindex!(M, M_row, i_offset + i)
    end
    i_offset += nrows(x)
    j_offset += ncols(x)
  end

  return M
end

################################################################################
#
#  Julias concatenation syntax
#
################################################################################

function Base.cat(n::Int, A::SMat...)
  if n == 1
    return vcat(A...)
  elseif n == 2
    return hcat(A...)
  else
    error("dims must be 1 or 2")
  end
end

function Base.vcat(A::SMat...)
  B = copy(A[1])
  for i=2:length(A)
    for r = A[i].rows
      push!(B, copy(r))
    end
  end
  return B
end

#base case
function Base.hcat(A::SMat)
  return A
end

function Base.hcat(A::SMat, B::SMat, C::SMat...)
  return hcat(hcat(A, B), C...)
end

function Base.cat(dims::Tuple{Int, Int}, A::SMat...)
  if dims != (1,2)
    error("dims must be (1, 2)")
  end
  B = copy(A[1])
  c = B.c
  for i=2:length(A)
    for j=1:nrows(A[i])
      R = SRow(base_ring(B))
      for (k,v) = A[i].rows[j]
        push!(R.pos, k+c)
        push!(R.values, v)
      end
      push!(B, R)
    end
    c += A[i].c
  end
  return B
end

################################################################################
#
#  Is one/zero?
#
################################################################################

@doc raw"""
    isone(A::SMat)

Tests if $A$ is an identity matrix.
"""
function isone(A::SMat)
  if ncols(A) != nrows(A)
    return false
  end
  for (i, r) in enumerate(A)
    if length(r.pos) != 1
      return false
    end
    if r.pos[1] != i || !isone(r.values[1])
      return false
    end
  end
  return true
end

@doc raw"""
    iszero(A::SMat)

Tests if $A$ is a zero matrix.
"""
function iszero(A::SMat)
  for r in A
    if !iszero(r)
      return false
    end
  end
  return true
end

################################################################################
#
#  File Serialization
#
################################################################################

@doc raw"""
    to_hecke(io::IOStream, A::SMat; name = "A")

  Prints the SMat as a julia-program into the file corresponding to `io`.
  The file can be included to get the matrix.
  `name` controls the variable name of the matrix.
"""
function to_hecke(io::IOStream, A::SMat; name = "A")
  # hard code the allowed rings
  R = base_ring(A)
  println(io, "K = ", R == ZZ ? "ZZ" :
                      R == QQ ? "QQ" :
                      R isa FqField && absolute_degree(R) == 1 ? "GF($(characteristic(R)))" :
                      error("cannot save this base")
                     )
  T = typeof(A.rows[1].values[1])
  println(io, name, " = sparse_matrix(K)")
  for i=A.rows
    print(io, "push!($(name), sparse_row(K, Tuple{Int, $T}[");
    for j=1:length(i.pos)-1
      print(io, "($(i.pos[j]), $(i.values[j])), ")
    end
    println(io, "($(i.pos[end]), K($(i.values[end])))]))")
  end
end

@doc raw"""
    to_hecke(io::String, A::SMat; name = "A")

  Prints the SMat as a julia-program into the file named `io`.
  The file can be included to get the matrix.
  `name` controls the variable name of the matrix.
"""
function to_hecke(f::String, A::SMat; name = "A")
  io = open(f, "w")
  to_hecke(io, A, name=name)
  close(io)
end

################################################################################
#
#  Conversion to julia types
#
################################################################################

@doc raw"""
    sparse(A::SMat) -> SparseMatrixCSC

The same matrix, but as a sparse matrix of julia type `SparseMatrixCSC`.
"""
function SparseArrays.sparse(A::SMat{T}) where T
  I = zeros(Int, A.nnz)
  J = zeros(Int, A.nnz)
  V = Vector{T}(undef, A.nnz)
  i = 1
  for r = 1:nrows(A)
    for j=1:length(A.rows[r].pos)
      I[i] = r
      J[i] = A.rows[r].pos[j]
      V[i] = A.rows[r].values[j]
      i += 1
    end
  end
  return SparseArrays.sparse(I, J, V)
end

@doc raw"""
    Matrix(A::SMat{T}) -> Matrix{T}

The same matrix, but as a julia matrix.
"""
function Matrix(A::SMat)
  M = elem_type(base_ring(A))[zero(base_ring(A)) for _ in 1:nrows(A), _ in 1:ncols(A)]
  for i in 1:nrows(A)
    for (k, c) in A[i]
      M[i, k] = c
    end
  end
  return M
end

@doc raw"""
    Array(A::SMat{T}) -> Matrix{T}

The same matrix, but as a two-dimensional julia array.
"""
function Array(A::SMat)
  M = elem_type(base_ring(A))[zero(base_ring(A)) for _ in 1:nrows(A), _ in 1:ncols(A)]
  for i in 1:nrows(A)
    for (k, c) in A[i]
      M[i, k] = c
    end
  end
  return M
end

#TODO: write a kronnecker-row-product, this is THE
# Kronecker product corresponding to the matrix of a tensor
# product of homs represented as column vectors
#in Oscar, we should be doing row vectors...
function kronecker_product(A::SMat{T}, B::SMat{T}) where {T}
  C = sparse_matrix(base_ring(A))

  for rA = A.rows
    for rB = B.rows
      p = Int[]
      v = T[]
      if !iszero(rA)
        for (pp, vv) = rA
          o = (pp-1)*ncols(B)
          for (qq, ww) = rB
            push!(p, o+qq)
            push!(v, vv*ww)
          end
        end
      end
      push!(C, sparse_row(base_ring(A), p, v))
    end
  end
  @assert nrows(C) == nrows(A)*nrows(B)
  @assert ncols(C) <= ncols(A)*ncols(B)
  C.c = ncols(A)*ncols(B)
  return C
end
