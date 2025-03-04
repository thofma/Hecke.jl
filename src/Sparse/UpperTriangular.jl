################################################################################
#
#   Smith normal form
#
################################################################################

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
