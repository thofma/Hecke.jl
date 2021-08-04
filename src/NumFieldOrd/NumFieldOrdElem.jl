################################################################################
#
#  Discriminant
#
################################################################################

@doc Markdown.doc"""
    discriminant(B::Array{NumFieldOrdElem, 1})

Returns the discriminant of the family $B$ of algebraic numbers,
i.e. $det((tr(B[i]*B[j]))_{i, j})^2$.
"""
function discriminant(B::Vector{T}) where T <: NumFieldOrdElem
  O = parent(B[1])
  n = degree(O)
  length(B) == 0 && error("Number of elements must be non-zero")
  length(B) != n && error("Number of elements must be $(n)")
  A = zero_matrix(base_ring(O), n, n)
  for i in 1:n
    el = tr(B[i]^2)
    A[i, i] = el
    for j in 1:n
      el = tr(B[i] * B[j])
      A[i, j] = el
      A[j, i] = el
    end
  end
  return det(A)
end

################################################################################
#
#  Hashing
#
################################################################################

Base.hash(x::NumFieldOrdElem, h::UInt) = Base.hash(x.elem_in_nf, h)

################################################################################
#
#  Equality
#
################################################################################

@doc Markdown.doc"""
    ==(x::NumFieldOrdElem, y::NumFieldOrdElem) -> Bool

Returns whether $x$ and $y$ are equal.
"""
==(x::NumFieldOrdElem, y::NumFieldOrdElem) = parent(x) === parent(y) &&
                                            x.elem_in_nf == y.elem_in_nf