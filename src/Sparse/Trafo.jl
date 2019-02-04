# Everything related to transformation on sparse matrices

export sparse_trafo_scale, sparse_trafo_swap, sparse_trafo_add_scaled,
       sparse_trafo_para_add_scaled, sparse_trafo_partial_dense,
       sparse_trafo_move_row

################################################################################
#
#  Constructors
#
################################################################################

function sparse_trafo_scale(i::Int, c::T) where {T}
  z = SparseTrafoElem{T, dense_matrix_type(T)}()
  z.type = 1
  z.i = i
  z.a = c
  return z
end

function sparse_trafo_swap(::Type{T}, i::Int, j::Int) where {T}
  z = SparseTrafoElem{T, dense_matrix_type(T)}()
  z.type = 2
  z.i = i
  z.j = j
  return z
end

function sparse_trafo_add_scaled(i::Int, j::Int, s::T) where {T}
  z = SparseTrafoElem{T, dense_matrix_type(T)}()
  z.type = 3
  z.i = i
  z.j = j
  z.a = s
  return z
end

function sparse_trafo_para_add_scaled(i::Int, j::Int, a::T, b::T, c::T, d::T) where {T}
  z = SparseTrafoElem{T, dense_matrix_type(T)}()
  z.type = 4
  z.i = i
  z.j = j
  z.a = a
  z.b = b
  z.c = c
  z.d = d
  return z
end

function sparse_trafo_partial_dense(i::Int, rows::UnitRange{Int}, cols::UnitRange{Int}, U::S) where {S}
  z = SparseTrafoElem{coefficient_type(S), S}()
  z.type = 5
  z.i = i
  z.rows = rows
  z.cols = cols
  z.U = U
  return z
end

# this is shorthand for the permutation matrix corresponding to
# (i i+1)(i+1 i+2)...(rows-1 rows)
function sparse_trafo_id(::Type{T}) where {T}
  z = SparseTrafoElem{T, dense_matrix_type(T)}()
  z.type = 7
  return z
end

function sparse_trafo_move_row(::Type{T}, i::Int, j::Int) where {T}
  @assert i <= j
  z = SparseTrafoElem{T, dense_matrix_type(T)}()
  z.type = 6
  z.i = i
  z.j = j
  return z
end

function change_indices!(T::Array{SparseTrafoElem{S, SS}, 1}, st::Int, off::Int) where {S, SS}
  for t in T
    if t.type == 7
        continue
    end
    if t.i > st
      t.i += off
    end
    if t.type == 1 || t.type == 5
      continue
    end
    if t.j > st
      t.j += off
    end
  end
end

function max_index(T::Array{SparseTrafoElem{S, SS}, 1}) where {S, SS}
  i = 0
  for t in T
    if t.type == 7
        continue
    end
    i = max(i, t.i)
    if t.type == 1 || t.type == 5
      continue
    end
    i = max(i, t.j)
  end
  return i
end

################################################################################
#
#  Row scaling
#
################################################################################

@doc Markdown.doc"""
    scale_row!(A::SMat{T}, i::Int, c::T)

Multiply the $i$-th row of $A$ by $c$ inplace.
"""
function scale_row!(A::SMat{T}, i::Int, c::T) where T
  scale_row!(A[i], c)
  return A
end

################################################################################
#
#  Row swapping
#
################################################################################

@doc Markdown.doc"""
  swap_rows!(A::SMat{T}, i::Int, j::Int)

Swap the $i$-th and $j$-th row of $A$ inplace.
"""
function swap_rows!(A::SMat{T}, i::Int, j::Int) where T
  A[i], A[j] = A[j], A[i]
  return A
end

################################################################################
#
#  Row inversion
#
################################################################################

@doc Markdown.doc"""
    invert_rows!(A::SMat)

Inplace inversion of the rows of $A$.
"""
function invert_rows!(A::SMat{T}) where T
  for i = 1:div(A.r, 2)
    A[i], A[A.r+1-i] = A[A.r+1-i], A[i]
  end
  return A
end

################################################################################
#
#  Column swapping
#
################################################################################

@doc Markdown.doc"""
    swap_cols!(A::SMat, i::Int, j::Int)

Swap the $i$-th and $j$-th column of $A$ inplace.
"""
function swap_cols!(A::SMat{T}, i::Int, j::Int) where T
  @assert 1 <= i <= ncols(A) && 1 <= j <= ncols(A)

  if i == j
    return A
  end

  for r in A.rows
    if i in r.pos
      i_i = findfirst(r.pos, i)
      val_i = r.values[i_i]
      if j in r.pos
        i_j = findfirst(r.pos, j)
        val_j = r.values[i_j]

        r.values[i_i], r.values[i_j] = r.values[i_j], r.values[i_i]
      else
        t = r.values[i_i]
        deleteat!(r.pos, i_i)
        deleteat!(r.values, i_i)
        k = searchsortedfirst(r.pos, j)
        insert!(r.pos, k, j)
        insert!(r.values, k, t)
      end
    else
      if j in r.pos
        i_j = findfirst(r.pos, j)
        val_j = r.values[i_j]

        t = r.values[i_j]
        deleteat!(r.pos, i_j)
        deleteat!(r.values, i_j)
        k = searchsortedfirst(r.pos, i)
        insert!(r.pos, k, i)
        insert!(r.values, k, t)
      end
    end
  end
  return A
end

################################################################################
#
#  Addition of scaled rows
#
################################################################################
# rows j -> row i*c + row j
@doc Markdown.doc"""
    add_scaled_row(A::SMat{T}, i::Int, j::Int, c::T)

Add $c$ times the $i$-th row to the $j$-th row of $A$ inplace, that is,
$A_j \rightarrow A_j + c \cdot A_i$, where $(A_i)_i$ denote the rows of $A$.
"""
function add_scaled_row!(A::SMat{T}, i::Int, j::Int, c::T) where T
  A.nnz = A.nnz - length(A[j])
  A.rows[j] = add_scaled_row(A[i], A[j], c)
  A.nnz = A.nnz + length(A[j])
  return A
end

################################################################################
#
#  Addition of scaled cols
#
################################################################################

@doc Markdown.doc"""
    add_scaled_col!(A::SMat{T}, i::Int, j::Int, c::T)

Add $c$ times the $i$-th column to the $j$-th column of $A$ inplace, that is,
$A_j \rightarrow A_j + c \cdot A_i$, where $(A_i)_i$ denote the columns of $A$.
"""
function add_scaled_col!(A::SMat{T}, i::Int, j::Int, c::T) where T
  @assert c != 0

  @assert 1 <= i <= ncols(A) && 1 <= j <= ncols(A)

  for r in A.rows
    if i in r.pos
      i_i = findfirst(r.pos, i)
      val_i = r.values[i_i]
      if j in r.pos
        i_j = findfirst(r.pos, j)
        val_j = r.values[i_j]

        r.values[i_j] += c*r.values[i_i]
      else
        k = searchsortedfirst(r.pos, j)
        insert!(r.pos, k, j)
        insert!(r.values, k, c*r.values[i_i])
      end
    end
  end
  return A
end

################################################################################
#
#  Elementary row transformation
#
################################################################################

@doc Markdown.doc"""
    transform_row(A::SMat{T}, i::Int, j::Int, a::T, b::T, c::T, d::T)

Applies the transformation $(A_i, A_j) \rightarrow (aA_i + bA_j, cA_i + dA_j)$
to $A$, where $(A_i)_i$ are the rows of $A$.
"""
function transform_row!(A::SMat{T}, i::Int, j::Int, a::T, b::T, c::T, d::T) where T
  A.nnz = A.nnz - length(A[i]) - length(A[j])
  A.rows[i], A.rows[j] = transform_row(A[i], A[j], a, b, c, d)
  A.nnz = A.nnz + length(A[i]) + length(A[j])
  return A
end

@doc Markdown.doc"""
    transform_row(A::SRow{T}, B::SRow{T}, i::Int, j::Int, a::T, b::T, c::T, d::T)

Returns the tuple $(aA + bB, cA + dB)$.
"""
function transform_row(Ai::SRow{T}, Aj::SRow{T}, a::T, b::T, c::T, d::T) where T
  sr = SRow{T}()
  tr = SRow{T}()
  pi = 1
  pj = 1
  while pi <= length(Ai) && pj <= length(Aj)
    if Ai.pos[pi] < Aj.pos[pj]
      if a != 0
        push!(sr.pos, Ai.pos[pi])
        push!(sr.values, a*Ai.values[pi])
      end
      if c != 0
        push!(tr.pos, Ai.pos[pi])
        push!(tr.values, c*Ai.values[pi])
      end
      pi += 1
    elseif Ai.pos[pi] > Aj.pos[pj]
      if b != 0
        push!(sr.pos, Aj.pos[pj])
        push!(sr.values, b*Aj.values[pj])
      end
      if d != 0
        push!(tr.pos, Aj.pos[pj])
        push!(tr.values, d*Aj.values[pj])
      end
      pj += 1
    else
      m = a*Ai.values[pi] + b*Aj.values[pj]
      n = c*Ai.values[pi] + d*Aj.values[pj]
      if m != 0
        push!(sr.pos, Ai.pos[pi])
        push!(sr.values, m)
      end
      if n != 0
        push!(tr.pos, Ai.pos[pi])
        push!(tr.values, n)
      end
      pi += 1
      pj += 1
    end
  end
  while pi <= length(Ai.pos)
    if a != 0
      push!(sr.pos, Ai.pos[pi])
      push!(sr.values, a*Ai.values[pi])
    end
    if c != 0
      push!(tr.pos, Ai.pos[pi])
      push!(tr.values, c*Ai.values[pi])
    end
    pi += 1
  end
  while pj <= length(Aj.pos)
    if b != 0
      push!(sr.pos, Aj.pos[pj])
      push!(sr.values, b*Aj.values[pj])
    end
    if d != 0
      push!(tr.pos, Aj.pos[pj])
      push!(tr.values, d*Aj.values[pj])
    end
    pj += 1
  end
  
  return sr, tr
end

################################################################################
#
#  Inverses of elementary matrices
#
################################################################################

function inv(t::TrafoSwap)
  return T
end

function inv(t::TrafoAddScaled)
  return TrafoAddScaled(t.i, t.j, -t.s)
end

function inv(t::TrafoPartialDense)
  return TrafoPartialDense(t.i, t.rows, t.cols, inv(t.U))
end

# TrafoParaAddScaled is missing

################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, t::SparseTrafoElem)
  print(io, "Sparse transformation: ")
  i = t.type
  if i == 1
    print(io, "Scale ", t.i, " by ", t.a)
  elseif i == 2
    print(io, "Swap ", t.i, " and ", t.j)
  elseif i == 3
    print(io, "Scale ", t.i, " by ", t.a, " and add to ", t.j)
  elseif i == 4
    print(io, "Transform", t.i, ", ", t.j, " by [", t.a, " ", t.b, " ", t.c, " ", t.d, "]")
  elseif i == 5
    print(io, "Dense ", nrows(t.U), "x", nrows(t.U), " at ", t.i)
  elseif i == 6
    print(io, "Move ", t.i, " to ", t.j)
  end
end

################################################################################
#
#  Application of a transformation on the left side of a sparse matrix
#
################################################################################

# The following function do not update the number of nonzero entries
# properly

function apply_left!(A::SMat{T}, t::SparseTrafoElem{T, S}) where {T, S}
  i = t.type
  if i == 1
    scale_row!(A, t.i, t.a)
  elseif i == 2
    swap_rows!(A, t.i, t.j)
  elseif i == 3
    add_scaled_row!(A, t.i, t.j, t.a)
  elseif i == 4
    transform_row!(A, t.i, t.j, t.a, t.b, t.c, t.d)
  elseif i == 5
    R = base_ring(A)
    k = t.i
    h = sub(A, t.rows, t.cols)
    deleteat!(A.rows, t.rows)
    A.r -= length(t.rows)
    @assert length(A.rows) == A.r
    # make dense matrix
    hdense = matrix(h)
    hdense = t.U * hdense

    htransformed = sparse_matrix(hdense)
    for r in htransformed
      for j in 1:length(r.pos)
        r.pos[j] = r.pos[j] + (k - 1)
      end
      push!(A, r)
    end
  elseif i == 6
    @assert t.i <= t.j
    x = A.rows
    for j in t.i:t.j-1
      r = x[j]
      x[j] = x[j + 1]
      x[j + 1] = r
    end
    #deleteat!(A.rows, t.i)
    #push!(A.rows, sparse_row(base_ring(A)))
  else
    error("Wrong type")
  end
  return A
end

################################################################################
#
#  Application of a transformation on the right hand side of a row
#
################################################################################

function apply_right!(x::Vector{T}, t::SparseTrafoElem{T, S}) where {T, S}
  i = t.type
  if i == 1
    x[t.i] = x[t.i] * t.a
  elseif i == 2
    r = x[t.i]
    x[t.i] = x[t.j]
    x[t.j] = r
  elseif i == 3
    x[t.i] = x[t.i] + x[t.j]*t.a
  elseif i == 4
    r = t.a * x[t.i] + t.c * x[t.j]
    s = t.b * x[t.i] + t.d * x[t.j]
    x[t.i] = r
    x[t.j] = s
  elseif i == 5
    s = matrix(parent(x[1]), 1, nrows(t.U), x[t.rows])
    #println("s :$s")
    s = s*t.U
    for (i, j) in zip(t.rows,1:nrows(t.U))
      x[i] = s[1, j]
    end
  elseif i == 6
    for j in t.j:-1:t.i+1
      r = x[j]
      x[j] = x[j - 1]
      x[j - 1] = r
    end
  end
  return x
end

################################################################################
#
#  Application to the left of an Array of ideals
#
################################################################################

#function apply_left!(x::Vector{NfOrdFracIdl}, y::TrafoSwap)
#  x[y.i], x[y.j] = x[y.j], x[y.i]
#end
#
#function apply_left!(x::Vector{NfOrdFracIdl}, y::TrafoAddScaled)
#  x[y.j] = x[y.j] * x[y.i]^Int(y.s)
#end
#
#function apply_left!(x::Vector{NfOrdFracIdl}, y::TrafoPartialDense)
#  z = view(deepcopy(x), y.cols)
#  xx = view(x, y.cols)
#  for i in 1:nrows(y.U)  ## use power product instead
#    xx[i] = z[1]^Int(y.U[i, 1])
#    for j in 2:ncols(y.U)
#      xx[i] *= z[j]^Int(y.U[i, j])
#    end
#  end
#end


