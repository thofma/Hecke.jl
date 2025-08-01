################################################################################
#
#  Representation matrix
#
################################################################################

function elem_to_mat_row!(M::MatElem{T}, i::Int, a::AbstractCentralSimpleAlgebraElem{T}) where {T}
  ca = coefficients(a, copy=false)
  for c = 1:ncols(M)
    if M isa QQMatrix
      M[i, c] = ca[c]
    else
      M[i, c] = deepcopy(ca[c])
    end
  end
  return nothing
end

function elem_from_mat_row(A::AbstractCentralSimpleAlgebra{T}, M::MatElem{T}, i::Int) where {T}
  a = A()
  for c = 1:ncols(M)
    a.coeffs[c] = deepcopy(M[i, c])
  end
  return a
end

function elem_to_mat_row!(x::ZZMatrix, i::Int, d::ZZRingElem, a::AbstractCentralSimpleAlgebraElem{QQFieldElem})
  z = zero_matrix(QQ, 1, ncols(x))
  elem_to_mat_row!(z, 1, a)
  z_q = FakeFmpqMat(z)

  for j in 1:ncols(x)
    x[i, j] = z_q.num[1, j]
  end

  set!(d, z_q.den)
  return nothing
end

function elem_from_mat_row(A::AbstractCentralSimpleAlgebra{QQFieldElem}, M::ZZMatrix, i::Int, d::ZZRingElem=ZZRingElem(1))
  a = A()
  for j in 1:ncols(M)
    a.coeffs[j] = QQFieldElem(M[i, j], d)
  end
  return a
end

@doc raw"""
    representation_matrix(a::AbstractCentralSimpleAlgebraElem, action::Symbol = :left) -> MatElem

Returns a matrix over `base_ring(algebra(a))` representing multiplication with
$a$ with respect to the basis of `algebra(a)`.
The multiplication is from the left if `action == :left` and from the right if
`action == :right`.
"""

function representation_matrix!(a::CentralSimpleAlgebraElem, M::MatElem, action::Symbol=:left)
  A = parent(a)
  acoeff = coefficients(a, copy=false)
  mt = multiplication_table(A, copy=false)
  if base_ring(A) isa QQField
    temp = nothing
  else
    temp = base_ring(A)()
  end
  GC.@preserve M begin
    if action == :left
      for i = 1:dim(A)
        if iszero(acoeff[i])
          continue
        end
        for j = 1:dim(A)
          for k = 1:dim(A)
            _addmul!(M, j, k, acoeff[i], mt[i, j, k], temp)
            #M[j, k] += acoeff[i] * mt[i, j, k]
          end
        end
      end
    elseif action == :right
      for i = 1:dim(A)
        if iszero(coefficients(a, copy=false)[i])
          continue
        end
        for j = 1:dim(A)
          for k = 1:dim(A)
            _addmul!(M, j, k, acoeff[i], mt[j, i, k]) # M[j, k] += acoeff[i] * mt[j, i, k]
          end
        end
      end
    else
      error("Not yet implemented")
    end
  end
  return M
end

function representation_matrix(a::CentralSimpleAlgebraElem, action::Symbol=:left)
  A = parent(a)
  M = zero_matrix(base_ring(A), dim(A), dim(A))
  representation_matrix!(a, M, action)
  return M
end
