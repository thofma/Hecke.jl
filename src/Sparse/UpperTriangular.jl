################################################################################
#
#   Smith normal form
#
################################################################################

function diagonal_form_with_transform(A::SMat, left=false, right=false)
  n = 1
  if left == true
    C = sparse_matrix(ZZ, 0, nrows(A))
    for i in 1:nrows(A)
      push!(C, sparse_row(ZZ, [(i, ZZ(1))]))
    end
  end
  if right == true
    D = sparse_matrix(ZZ, 0, ncols(A))
    for i in 1:ncols(A)
      push!(D, sparse_row(ZZ, [(i, ZZ(1))]))
    end
  end
  while(!is_diagonal(A))
    if n % 2 == 1
      if left == false
        hnf!(A, truncate=false, full_hnf=true, auto=false)
      else
 	I = sparse_matrix(ZZ, 0, nrows(A))
        for i in 1:nrows(A)
          push!(I, sparse_row(ZZ, [(i, ZZ(1))]))
        end
        hnf_with_trafo!(A, I, truncate=false, full_hnf=true, auto=false)
      	R = sparse_matrix(base_ring(C), nrows(I), ncols(C))
        for (i, row) in enumerate(I.rows)
          rR = row * C
          R[i] = rR
        end
        C = R
      end
      A = transpose(A)
      n = n + 1
    else
      if right == false
        hnf!(A, truncate=false, full_hnf=true, auto=false)
      else
        I = sparse_matrix(ZZ, 0, ncols(A))
        for i in 1:ncols(A)
          push!(I, sparse_row(ZZ, [(i, ZZ(1))]))
        end
        hnf_with_trafo!(A, I, truncate=false, full_hnf=true, auto=false)
        R = sparse_matrix(base_ring(D), nrows(I), ncols(D))
        for (i, row) in enumerate(I.rows)
          rR = row * D
          R[i] = rR
        end
        D = R
      end
      A = transpose(A)
      n = n + 1
    end
  end
  if n % 2 == 0
    A = transpose(A)
  end
  if left == true && right == true
    return C, A, transpose(D)
  end
  if left == true
    return C, A
  end
  if right == true
    return A, transpose(D)
  else
    return A
  end
end    

@doc raw"""
    diagonal(A::SMat) -> ZZRingElem[]

The diagonal elements of $A$ in an array.
"""
function diagonal(A::SMat)
  return [A[i,i] for i=1:min(nrows(A), ncols(A))]
end

@doc raw"""
    is_diagonal(A::SMat) -> Bool

True iff only the i-th entry in the i-th row is non-zero.
"""
function is_diagonal(A::SMat)
  i = 1
  while i<= nrows(A) && length(A.rows[i].pos)>0
    if length(A.rows[i].pos) > 1
      return false
    end
    if A.rows[i].pos[1] != i
      return false
    end
    i += 1
  end
  if i > nrows(A)
    return true
  end
  return all(i -> length(A.rows[i].pos) == 0, i:nrows(A))
end

@doc raw"""
    snf(A::SMat{ZZRingElem})

The Smith normal form (snf) of $A$.
"""
function snf(A::SMat{ZZRingElem})
  A = diagonal_form(A)
  e = elementary_divisors(A)
  for i=1:length(e)
    if iszero(e[i])
      return A
    end
    A.rows[i].values[1] = e[i]
  end
  return A
end

@doc raw"""
    elementary_divisors(A::SMat{ZZRingElem}) -> Vector{ZZRingElem}

The elementary divisors of $A$, i.e. the diagonal elements of the Smith normal
form of $A$.
"""
function elementary_divisors(A::SMat{ZZRingElem})
  A = diagonal_form(A)
  b = [x for x in diagonal(A) if !iszero(x)]
  c = coprime_base(b)
  e = [ZZRingElem(1) for x = b]
  for p = c
    if isone(p)
      continue
    end
    v = [valuation(x, p) for x = b]
    sort!(v)
    for i=1:length(v)
      e[i] *= p^v[i]
    end
  end
  for i = length(e)+1:min(nrows(A), ncols(A))
    push!(e, ZZRingElem(0))
  end
  return e
end
