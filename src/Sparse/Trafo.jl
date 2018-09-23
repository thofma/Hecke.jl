# Everything related to transformation on sparse matrices

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
  @assert 1 <= i <= cols(A) && 1 <= j <= cols(A)

  if i == j
    return nothing
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
  return nothing
end

################################################################################
#
#  Addition of scaled rows
#
################################################################################
# rows j -> row i*c + row j
@doc Markdown.doc"""
    add_scaled_row!{T}(A::SMat{T}, i::Int, j::Int, c::T)

Add $c$ times the $i$-th row to the $j$-th row of $A$ inplace.
"""
function add_scaled_row!(A::SMat{T}, i::Int, j::Int, c::T) where T
  A.nnz = A.nnz - length(A[j])
  A.rows[j] = add_scaled_row(A[i], A[j], c)
  A.nnz = A.nnz + length(A[j])
end

################################################################################
#
#  Addition of scaled cols
#
################################################################################

@doc Markdown.doc"""
    add_scaled_col!{T}(A::SMat{T}, i::Int, j::Int, c::T)

Add $c$ times the $i$-th column to the $j$-th column of $A$ inplace, that is,
$A_j \rightarrow A_j + c \cdot A_i$.
"""
function add_scaled_col!(A::SMat{T}, i::Int, j::Int, c::T) where T
  @assert c != 0

  @assert 1 <= i <= cols(A) && 1 <= j <= cols(A)

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
  return nothing
end

################################################################################
#
#  Elementary row transformation
#
################################################################################

@doc Markdown.doc"""
    transform_row(A::SMat{T}, i::Int, j::Int, a::T, b::T, c::T, d::T)

Applies the transformation $(A_i, A_j) \rightarrow (aA_i + bA_j, cA_i + dA_j)$
to $A$.
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
#  Application of a transformation on the left side of a sparse matrix
#
################################################################################

# The following function do not update the number of nonzero entries
# properly

function apply_left!(A::SMat{T}, t::TrafoScale{T}) where T
  scale_row!(A, t.i, t.c)
  return nothing
end

function apply_left!(A::SMat{T}, t::TrafoSwap{T}) where T
  swap_rows!(A, t.i, t.j)
  return nothing
end

function apply_left!(A::SMat{T}, t::TrafoAddScaled{T}) where T
  add_scaled_row!(A, t.i, t.j, t.s)
  return nothing
end

function apply_left!(A::SMat{T}, t::TrafoParaAddScaled{T}) where T
  transform_row!(A, t.i, t.j, t.a, t.b, t.c, t.d)
  return nothing
end

function apply_left!(A::SMat{T}, t::TrafoDeleteZero{T}) where T
  deleteat!(A.rows, t.i)
  A.r -= 1
end

function apply_left!(A::SMat{T}, t::TrafoPartialDense{S}) where {T, S}
  R = parent(A.rows[1].values[1])
  i = t.i
  h = sub(A, t.rows, t.cols)
  deleteat!(A.rows, t.rows)
  A.r -= length(t.rows)
  @assert length(A.rows) == A.r
  # make dense matrix
  hdense = typeof(t.U)(h)

  #println(t.U)

  hdense = t.U * hdense

  h = _sparse_matrix(hdense, R = R, zerorows = true)

  for k in 1:length(h.rows)
    j = h.rows[k]
    rw = SRow{T}()
    for e in 1:length(j.pos)
      push!(rw.pos, j.pos[e] + i-1)
      push!(rw.values, j.values[e])
    end
    insert!(A.rows, i + k - 1, rw)
    A.r += 1
  end
  return nothing
end

################################################################################
#
#  Application of a transformation on the right side of a sparse matrix
#
################################################################################

# The following function do not update the number of nonzero entries
# properly
function apply_right!(A::SMat{T}, t::TrafoSwap{T}) where T
  swap_cols!(A, t.i, t.j)
  return nothing
end

function apply_right!(A::SMat{T}, t::TrafoAddScaled{T}) where T
  add_scaled_col!(A, t.j, t.i, t.s)
  return nothing
end

function apply_right!(A::SMat{T}, t::TrafoPartialDense{S}) where {T, S}
  # this works only if there are zeros left of the block to which we apply t
  i = t.i
  h = sub(A, t.rows, t.cols)
  deleteat!(A.rows, t.rows)
  A.r -= length(t.rows)
  @assert length(A.rows) == A.r
  # make dense matrix
  hdense = typeof(t.U)(h)

  #println(t.U)

  hdense = hdense * t.U

  h = _sparse_matrix(hdense, R = parent(A.rows[1].values[1]), zerorows = true)

  for k in 1:length(h.rows)
    j = h.rows[k]
    rw = SRow{T}()
    for e in 1:length(j.pos)
      push!(rw.pos, j.pos[e] + i-1)
      push!(rw.values, j.values[e])
    end
    insert!(A.rows, i + k - 1, rw)
    A.r += 1
  end
  return nothing
end

################################################################################
#
#  Application of a transformation on the right hand side of a row
#
################################################################################

function apply_right!(x::Array{T, 1}, t::TrafoAddScaled{T}) where T
  x[t.i] = x[t.i] + x[t.j]*t.s
  return nothing
end

function apply_right!(x::Array{T, 1}, t::TrafoScale{T}) where T
  x[t.i] = x[t.i] * t.c
end

function apply_right!(x::Array{T, 1}, t::TrafoSwap{T}) where T
  r = x[t.i]
  x[t.i] = x[t.j]
  x[t.j] = r
  return nothing
end

function apply_right!(x::Array{T, 1}, t::TrafoParaAddScaled{T}) where T
  r = t.a * x[t.i] + t.c * x[t.j]
  s = t.b * x[t.i] + t.d * x[t.j]
  x[t.i] = r
  x[t.j] = s
  return nothing
end

function apply_right!(x::Array{T, 1}, t::TrafoDeleteZero{T}) where T
  # move ith position to the back
  for j in length(x):-1:t.i+1
    r = x[j]
    x[j] = x[j - 1]
    x[j - 1] = r
  end
end

function apply_right!(x::Array{T, 1}, t::TrafoPartialDense) where T
  s = matrix(parent(x[1]), 1, rows(t.U), x[t.rows])
  #println("s :$s")
  s = s*t.U
  for (i, j) in zip(t.rows,1:rows(t.U))
    x[i] = s[1, j]
  end
  return nothing
end

################################################################################
#
#  Application to the left of an Array of ideals
#
################################################################################

function apply_left!(x::Vector{NfOrdFracIdl}, y::TrafoSwap)
  x[y.i], x[y.j] = x[y.j], x[y.i]
end

function apply_left!(x::Vector{NfOrdFracIdl}, y::TrafoAddScaled)
  x[y.j] = x[y.j] * x[y.i]^Int(y.s)
end

function apply_left!(x::Vector{NfOrdFracIdl}, y::TrafoPartialDense)
  z = view(deepcopy(x), y.cols)
  xx = view(x, y.cols)
  for i in 1:rows(y.U)  ## use power product instead
    xx[i] = z[1]^Int(y.U[i, 1])
    for j in 2:cols(y.U)
      xx[i] *= z[j]^Int(y.U[i, j])
    end
  end
end


