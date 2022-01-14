function insert_row!(A::SMat{T}, i::Int, r::SRow{T}) where T
  insert!(A.rows, i, r)
  A.r += 1
  A.nnz += length(r)
  A.c = max(A.c, r.pos[end])
  return A
end

# Computed x*a + b and writes it to b
function my_add_scaled_row!(a::SRow{T}, b::SRow{T}, x::T) where T
  @assert a !== b
  i = 1
  j = 1
  t = base_ring(a)()
  while i <= length(a) && j <= length(b)
    if a.pos[i] < b.pos[j]
      insert!(b.pos, j, a.pos[i])
      insert!(b.values, j, x*a.values[i])
      i += 1
      j += 1
    elseif a.pos[i] > b.pos[j]
      j += 1
    else
      t = mul!(t, x, a.values[i])
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
    push!(b.values, x*a.values[i])
    i += 1
  end
  return b
end

function _add_row_to_rref!(M::SMat{T}, v::SRow{T}) where { T <: FieldElem }
  if iszero(v)
    return false
  end

  pivot_found = false
  s = one(base_ring(M))
  i = 1
  new_row = 1
  while i <= length(v)
    c = v.pos[i]
    r = find_row_starting_with(M, c)
    if r > nrows(M) || M.rows[r].pos[1] > c
      i += 1
      if pivot_found
        # We already found a pivot
        continue
      end

      @assert i == 2 # after incrementing
      pivot_found = true
      new_row = r
      continue
    end

    # Reduce columns v by M.rows[r]
    t = -v.values[i] # we assume M.rows[r].pos[1] == 1 (it is the pivot)
    v = my_add_scaled_row!(M.rows[r], v, t)
    # Don't increase i, we deleted the entry
  end
  if !pivot_found
    return false
  end

  # Multiply v by inv(v.values[1])
  t = inv(v.values[1])
  for j = 2:length(v)
    v.values[j] = mul!(v.values[j], v.values[j], t)
  end
  v.values[1] = one(base_ring(M))
  insert_row!(M, new_row, v)

  # Reduce the rows above the newly inserted one
  for i = 1:new_row - 1
    c = M.rows[new_row].pos[1]
    j = searchsortedfirst(M.rows[i].pos, c)
    if j > length(M.rows[i].pos) || M.rows[i].pos[j] != c
      continue
    end

    t = -M.rows[i].values[j]
    l = length(M.rows[i])
    M.rows[i] = my_add_scaled_row!(M.rows[new_row], M.rows[i], t)
    while j <= length(M.rows[i])
      r = find_row_starting_with(M, M.rows[i].pos[j])
      if r > nrows(M) || M.rows[r].pos[1] > M.rows[i].pos[j]
        j += 1
        continue
      end
      t = -M.rows[i].values[j]
      M.rows[i] = my_add_scaled_row!(M.rows[r], M.rows[i], t)
      j += 1
    end
    if length(M.rows[i]) != l
      M.nnz += length(M.rows[i]) - l
    end
  end
  return true
end

function Base.deepcopy_internal(r::SRow, dict::IdDict)
  s = sparse_row(base_ring(r))
  s.pos = Base.deepcopy_internal(r.pos, dict)
  s.values = Base.deepcopy_internal(r.values, dict)
  return s
end

function Base.deepcopy_internal(M::SMat, dict::IdDict)
  N = sparse_matrix(base_ring(M))
  N.r = M.r
  N.c = M.c
  N.nnz = M.nnz
  N.rows = Base.deepcopy_internal(M.rows, dict)
  return N
end

function rref!(A::SMat{T}) where {T <: FieldElement}
  B = sparse_matrix(base_ring(A))
  B.c = A.c
  rows = sort!(A.rows, lt = (x, y) -> length(x) < length(y))
  for r in rows
    b = _add_row_to_rref!(B, r)
    if nrows(B) == ncols(B)
      break
    end
  end
  A.r = B.r
  A.nnz = B.nnz
  A.rows = B.rows
  return A.r, A
end

rref(A::SMat{T}) where {T <: FieldElement} = rref!(deepcopy(A))
