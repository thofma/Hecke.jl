parent_type(::Type{AlgMatElem{T, S, Mat}}) where {T, S, Mat} = S

function matrix(a::AlgMatElem; copy::Bool = true)
  if copy
    return deepcopy(a.matrix)
  else
    return a.matrix
  end
end

################################################################################
#
#  Coefficients
#
################################################################################

function assure_has_coeffs(a::AlgMatElem)
  if a.has_coeffs
    return nothing
  end

  A = parent(a)
  Ma = matrix(a)
  b, c = _check_matrix_in_algebra(Ma, A)
  @assert b "The element is not in the algebra."
  a.coeffs = c
  a.has_coeffs = true
  return nothing
end

function coeffs(a::AlgMatElem; copy::Bool = true)
  assure_has_coeffs(a)
  if copy
    return deepcopy(a.coeffs)
  else
    return a.coeffs
  end
end

function show(io::IO, a::AlgMatElem)
  show(IOContext(io, :compact => true), matrix(a, copy = false))
end

################################################################################
#
#  Unary operations
#
################################################################################

function -(a::AlgMatElem)
  b = parent(a)(-matrix(a, copy = false))
  if a.has_coeffs
    b.coeffs = [ -coeffs(a, copy = false)[i] for i = 1:dim(parent(a)) ]
    b.has_coeffs = true
  end
  return b
end

################################################################################
#
#  Binary operations
#
################################################################################

function +(a::AlgMatElem{T, S, V}, b::AlgMatElem{T, S, V}) where {T, S, V}
  parent(a) != parent(b) && error("Parents don't match.")
  c = parent(a)(matrix(a, copy = false) + matrix(b, copy = false))
  if a.has_coeffs && b.has_coeffs
    c.coeffs = [ coeffs(a, copy = false)[i] + coeffs(b, copy = false)[i] for i = 1:dim(parent(a)) ]
    c.has_coeffs = true
  end
  return c
end

function -(a::AlgMatElem{T, S, V}, b::AlgMatElem{T, S, V}) where {T, S, V}
  parent(a) != parent(b) && error("Parents don't match.")
  c = parent(a)(matrix(a, copy = false) - matrix(b, copy = false))
  if a.has_coeffs && b.has_coeffs
    c.coeffs = [ coeffs(a, copy = false)[i] - coeffs(b, copy = false)[i] for i = 1:dim(parent(a)) ]
    c.has_coeffs = true
  end
  return c
end

function *(a::AlgMatElem{T, S, V}, b::AlgMatElem{T, S, V}) where {T, S, V}
  parent(a) != parent(b) && error("Parents don't match.")
  return parent(a)(matrix(a, copy = false)*matrix(b, copy = false))
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function zero!(a::AlgMatElem)
  a.matrix = zero!(a.matrix)
  return a
end

function add!(c::AlgMatElem{T, S, V}, a::AlgMatElem{T, S, V}, b::AlgMatElem{T, S, V}) where {T, S, V}
  parent(a) != parent(b) && error("Parents don't match.")
  parent(c) != parent(b) && error("Parents don't match.")
  A = parent(a)

  if c === a || c === b
    d = A()
    d = add!(d, a, b)
    return d
  end

  c.matrix = add!(c.matrix, a.matrix, b.matrix)
  c.has_coeffs = false

  return c
end

function mul!(c::AlgMatElem{T, S, V}, a::AlgMatElem{T, S, V}, b::AlgMatElem{T, S, V}) where {T, S, V}
  parent(a) != parent(b) && error("Parents don't match.")
  A = parent(a)

  if c === a || c === b
    d = parent(a)()
    mul!(d, a, b)
    return d
  end

  c.matrix = mul!(c.matrix, a.matrix, b.matrix)
  c.has_coeffs = false

  return c
end

################################################################################
#
#  Ad hoc operations
#
################################################################################

function *(a::AlgMatElem, b::T) where {T <: RingElem}
  A = parent(a)
  if parent(b) == base_ring(A)
    b = coefficient_ring(A)(b)
  end
  return A(matrix(a, copy = false)*b)
end

function *(b::T, a::AlgMatElem) where {T <: RingElem}
  A = parent(a)
  if parent(b) == base_ring(A)
    b = coefficient_ring(A)(b)
  end
  return A(b*matrix(a, copy = false))
end

function *(a::AlgMatElem{S, T, U}, b::U) where { S, T, U }
  A = parent(a)
  return A(matrix(a, copy = false)*b)
end

function *(b::U, a::AlgMatElem{S, T, U}) where { S, T, U }
  A = parent(a)
  return A(b*matrix(a, copy = false))
end

################################################################################
#
#  Inverse
#
################################################################################

function inv(a::AlgMatElem)
  return parent(a)(inv(matrix(a, copy = false)))
end

################################################################################
#
#  Exponentiation
#
################################################################################

function ^(a::AlgMatElem, b::Int)
  return parent(a)(matrix(a, copy = false)^b)
end

################################################################################
#
#  Parent object overloading
#
################################################################################

function (A::AlgMat)()
  n = degree(A)
  return A(zero_matrix(coefficient_ring(A), n, n))
end

function (A::AlgMat{T, S})(M::S) where { T, S }
  return AlgMatElem{T, typeof(A), S}(A, M)
end

function (A::AlgMat{T, S})(a::T) where { T, S }
  return a*one(A)
end

function (A::AlgMat{T, S})(v::Vector{T}) where { T, S }
  @assert length(v) == dim(A)
  R = coefficient_ring(A)
  M = zero_matrix(R, degree(A), degree(A))
  for i = 1:dim(A)
    #M = add!(M, M, matrix(basis(A)[i], copy = false)*v[i])
    M += matrix(basis(A)[i], copy = false)*R(v[i])
  end
  a = A(M)
  a.coeffs = v
  a.has_coeffs = true
  return a
end

################################################################################
#
#  Equality
#
################################################################################

function ==(a::AlgMatElem{T, S, V}, b::AlgMatElem{T, S, V}) where {T, S, V}
  parent(a) != parent(b) && return false
  return matrix(a, copy = false) == matrix(b, copy = false)
end

################################################################################
#
#  isone/iszero
#
################################################################################

isone(a::AlgMatElem) = isone(matrix(a, copy = false))

iszero(a::AlgMatElem) = iszero(matrix(a, copy = false))

################################################################################
#
#  elem_from_mat_row
#
################################################################################

function elem_from_mat_row(A::AlgMat{T, S}, M::MatElem{T}, i::Int) where { T, S }
  v = Vector{T}(undef, dim(A))
  for c = 1:ncols(M)
    v[c] = deepcopy(M[i, c])
  end
  return A(v)
end

function elem_from_mat_row(A::AlgMat, M::fmpz_mat, i::Int, d::fmpz = fmpz(1))
  v = Vector{fmpq}(undef, dim(A))
  for j in 1:ncols(M)
    v[j] = fmpq(M[i, j], d)
  end
  return A(v)
end
