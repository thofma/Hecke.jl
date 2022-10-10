################################################################################
#
#   Smith normal form
#
################################################################################

@doc Markdown.doc"""
    diagonal_form(A::SMat{fmpz}) -> SMat{fmpz}

A matrix $D$ that is diagonal and obtained via unimodular row and column operations.
Like a snf without the divisibility condition.
"""
function diagonal_form(A::SMat{fmpz})
  s = 0
  while !is_diagonal(A)
    s += 1
    A = hnf(transpose(A))
  end
  if isodd(s)
    return transpose(A)
  else
    return A
  end
end

@doc Markdown.doc"""
    diagonal(A::SMat) -> fmpz[]

The diagonal elements of $A$ in an array.
"""
function diagonal(A::SMat)
  return [A[i,i] for i=1:min(nrows(A), ncols(A))]
end

@doc Markdown.doc"""
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

@doc Markdown.doc"""
    snf(A::SMat{fmpz})

The Smith normal form (snf) of $A$.
"""
function snf(A::SMat{fmpz})
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

@doc Markdown.doc"""
    elementary_divisors(A::SMat{fmpz}) -> Vector{fmpz}

The elementary divisors of $A$, i.e. the diagonal elements of the Smith normal
form of $A$.
"""
function elementary_divisors(A::SMat{fmpz})
  A = diagonal_form(A)
  b = [x for x in diagonal(A) if !iszero(x)]
  c = coprime_base(b)
  e = [fmpz(1) for x = b]
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
  for i = length(e):min(nrows(A), ncols(A))
    push!(e, fmpz(0))
  end
  return e
end
