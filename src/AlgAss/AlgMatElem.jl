parent_type(::Type{MatAlgebraElem{T, S}}) where {T, S} = MatAlgebra{T, S}

@doc raw"""
    matrix(a::MatAlgebraElem; copy::Bool = true) -> MatElem

Returns the matrix which defines $a$.
"""
function matrix(a::MatAlgebraElem; copy::Bool = true)
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

function assure_has_coeffs(a::MatAlgebraElem)
  if !a.has_coeffs
    a.coeffs = _matrix_in_algebra(matrix(a), parent(a))
    a.has_coeffs = true
  end
  @hassert :StructureConstantAlgebra 1 begin B = basis(parent(a));
                           sum(B[i] * a.coeffs[i] for i in 1:length(a.coeffs)) == a
                     end
  return nothing
end

@doc raw"""
    coefficients(a::MatAlgebraElem; copy::Bool = true) -> Vector{RingElem}

Returns the coefficients of $a$ in the basis of `algebra(a)`.
"""
function coefficients(a::MatAlgebraElem; copy::Bool = true)
  assure_has_coeffs(a)
  if copy
    return deepcopy(a.coeffs)
  else
    return a.coeffs
  end
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::MatAlgebraElem)
  show(IOContext(io, :compact => true), matrix(a, copy = false))
end

################################################################################
#
#  Unary operations
#
################################################################################

@doc raw"""
    -(a::MatAlgebraElem) -> MatAlgebraElem

Returns $-a$.
"""
function -(a::MatAlgebraElem)
  b = parent(a)(-matrix(a, copy = false))
  if a.has_coeffs
    b.coeffs = [ -coefficients(a, copy = false)[i] for i = 1:dim(parent(a)) ]
    b.has_coeffs = true
  end
  return b
end

################################################################################
#
#  Binary operations
#
################################################################################

function +(a::T, b::T) where {T <: MatAlgebraElem}
  parent(a) != parent(b) && error("Parents don't match.")
  c = parent(a)(matrix(a, copy = false) + matrix(b, copy = false), check = false)
  if a.has_coeffs && b.has_coeffs
    c.coeffs = [ coefficients(a, copy = false)[i] + coefficients(b, copy = false)[i] for i = 1:dim(parent(a)) ]
    c.has_coeffs = true
  end
  return c
end

function -(a::T, b::T) where {T <: MatAlgebraElem}
  parent(a) != parent(b) && error("Parents don't match.")
  c = parent(a)(matrix(a, copy = false) - matrix(b, copy = false))
  if a.has_coeffs && b.has_coeffs
    c.coeffs = [ coefficients(a, copy = false)[i] - coefficients(b, copy = false)[i] for i = 1:dim(parent(a)) ]
    c.has_coeffs = true
  end
  return c
end

function *(a::T, b::T) where {T <: MatAlgebraElem}
  parent(a) != parent(b) && error("Parents don't match.")
  return parent(a)(matrix(a, copy = false)*matrix(b, copy = false); check = get_assertion_level(:StructureConstantAlgebra)>1)
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function zero!(a::MatAlgebraElem)
  a.matrix = zero!(a.matrix)
  return a
end

function add!(c::T, a::T, b::T) where {T <: MatAlgebraElem}
  parent(a) != parent(b) && error("Parents don't match.")
  parent(c) != parent(b) && error("Parents don't match.")
  A = parent(a)

  c.matrix = add!(c.matrix, a.matrix, b.matrix)
  c.has_coeffs = false

  return c
end

function mul!(c::T, a::T, b::T) where {T <: MatAlgebraElem}
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

function mul!(c::MatAlgebraElem{T}, a::MatAlgebraElem{T}, b::T) where {T}
  parent(c) !== parent(a) && error("Parents don't match.")
  A = parent(a)

  c.matrix = mul!(c.matrix, a.matrix, b)
  c.has_coeffs = false
  return c
end

################################################################################
#
#  Ad hoc operations
#
################################################################################

function *(a::MatAlgebraElem, b::T) where {T <: RingElem}
  A = parent(a)
  if parent(b) == base_ring(A)
    b = coefficient_ring(A)(b)
  end
  return A(matrix(a, copy = false)*b, check = false)::elem_type(A)
end

function *(b::T, a::MatAlgebraElem) where {T <: RingElem}
  A = parent(a)
  if parent(b) == base_ring(A)
    b = coefficient_ring(A)(b)
  end
  return A(b*matrix(a, copy = false), check = false)::elem_type(A)
end

function *(a::MatAlgebraElem{T,S}, b::S) where { T, S <: MatElem }
  A = parent(a)
  return A(matrix(a, copy = false)*b, check = false)
end

function *(b::S, a::MatAlgebraElem{T,S}) where { T, S <: MatElem }
  A = parent(a)
  return A(b*matrix(a, copy = false), check = false)
end

################################################################################
#
#  Inverse
#
################################################################################

@doc raw"""
    inv(a::MatAlgebraElem) -> MatAlgebraElem

Returns $a^{-1}$.
"""
function inv(a::MatAlgebraElem)
  if coefficient_ring(parent(a)) isa Field
    return parent(a)(inv(matrix(a, copy = false)))
  else # we cannot invert the matrix
    t, b = is_invertible(a)
    if !t
      error("Element is not invertible")
    end
    return b
  end
end

################################################################################
#
#  Exponentiation
#
################################################################################

@doc raw"""
    ^(a::MatAlgebraElem, b::Int) -> MatAlgebraElem

Returns $a^b$.
"""
function ^(a::MatAlgebraElem, b::Int)
  return parent(a)(matrix(a, copy = false)^b, check = false)
end

################################################################################
#
#  Parent object overloading
#
################################################################################

function one(A::MatAlgebra)
  if !has_one(A)
    error("Algebra does not have a one")
  end
  return A(identity_matrix(coefficient_ring(A), degree(A)), check = false) # deepcopy needed by mul!
end

function (A::MatAlgebra)()
  n = degree(A)
  return A(zero_matrix(coefficient_ring(A), n, n), check = false)
end

function (A::MatAlgebra{T, S})(M::S; check::Bool = true, deepcopy::Bool = true) where {T, S}
  @assert base_ring(M) === coefficient_ring(A)
  if check
    b, c = _check_matrix_in_algebra(M, A)
    @req b "Matrix not an element of the matrix algebra"
    z = MatAlgebraElem{T, S}(A, deepcopy ? Base.deepcopy(M) : M)
    z.coeffs = c
    z.has_coeffs = true
    return z
  else
    return MatAlgebraElem{T, S}(A, deepcopy ? Base.deepcopy(M) : M)
  end
end

#function (A::MatAlgebra{T, S})(a::T) where { T, S }
#  return a*one(A)
#end
#
#function (A::MatAlgebra)(x::ZZRingElem)
#  return x * one(A)
#end
#
#function (A::MatAlgebra)(x::Integer)
#  return x * one(A)
#end

function (A::MatAlgebra{T, S})(v::Vector{T}; copy::Bool = true) where { T, S }
  @assert length(v) == dim(A)
  R = coefficient_ring(A)
  M = zero_matrix(R, degree(A), degree(A))
  temp = zero_matrix(R, degree(A), degree(A))
  B = basis(A)
  for i = 1:dim(A)
    temp = mul!(temp, matrix(B[i], copy = false), R(v[i]))
    M = add!(M, M, temp)
  end
  a = A(M; check = false, deepcopy = false)
  if copy
    a.coeffs = Base.copy(v)
  else
    a.coeffs = v
  end
  a.has_coeffs = true
  return a
end

################################################################################
#
#  Equality
#
################################################################################

@doc raw"""
    ==(a::MatAlgebraElem, b::MatAlgebraElem) -> Bool

Returns `true` if $a$ and $b$ are equal and `false` otherwise.
"""
function ==(a::T, b::T) where {T <: MatAlgebraElem}
  parent(a) != parent(b) && return false
  return matrix(a, copy = false) == matrix(b, copy = false)
end

################################################################################
#
#  isone/iszero
#
################################################################################

isone(a::MatAlgebraElem) = isone(matrix(a, copy = false))

iszero(a::MatAlgebraElem) = iszero(matrix(a, copy = false))

################################################################################
#
#  elem_from_mat_row
#
################################################################################

function elem_from_mat_row(A::MatAlgebra{T, S}, M::MatElem{T}, i::Int) where { T, S }
  v = Vector{T}(undef, dim(A))
  for c = 1:ncols(M)
    v[c] = deepcopy(M[i, c])
  end
  return A(v)
end

function elem_from_mat_row(A::MatAlgebra, M::ZZMatrix, i::Int, d::ZZRingElem = ZZRingElem(1))
  v = Vector{QQFieldElem}(undef, dim(A))
  for j in 1:ncols(M)
    v[j] = QQFieldElem(M[i, j], d)
  end
  return A(v)
end

################################################################################
#
#  Hashing
#
################################################################################

function Base.hash(a::MatAlgebraElem, h::UInt)
  return Base.hash(matrix(a, copy = false), h)
end

################################################################################
#
#  getindex / setindex
#
################################################################################

function getindex(a::MatAlgebraElem, r::Int, c::Int)
  return matrix(a, copy = false)[r, c]
end

function setindex!(a::MatAlgebraElem, d::T, r::Int, c::Int) where T <: Union{ RingElem, Int }
  a.matrix[r, c] = coefficient_ring(parent(a))(d)
  a.has_coeffs = false
  return nothing
end
