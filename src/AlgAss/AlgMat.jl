################################################################################
#
#  Basic field access
#
################################################################################

degree(A::AlgMat) = A.degree

dim(A::AlgMat) = A.dim

base_ring(A::AlgMat) = A.base_ring

function coefficient_ring(A::AlgMat)
  if isdefined(A, :coefficient_ring)
    return A.coefficient_ring
  end
  return base_ring(A)
end

basis(A::AlgMat) = A.basis

has_one(A::AlgMat) = A.has_one

one(A::AlgMat) = deepcopy(A.one)

elem_type(A::AlgMat{T, S}) where { T, S } = AlgMatElem{T, AlgMat{T, S}, S}

elem_type(::Type{AlgMat{T, S}}) where { T, S } = AlgMatElem{T, AlgMat{T, S}, S}

################################################################################
#
#  Basis matrix
#
################################################################################

function assure_has_basis_mat(A::AlgMat)
  if isdefined(A, :basis_mat)
    return nothing
  end

  d2 = degree(A)^2
  if !isdefined(A, :coefficient_ring)
    M = zero_matrix(base_ring(A), dim(A), d2)
    for i = 1:dim(A)
      N = matrix(A[i])
      for j = 1:d2
        M[i, j] = N[j]
      end
    end
    A.basis_mat = M
  else
    dcr = dim(coefficient_ring(A))
    M = zero_matrix(base_ring(A), dim(A), d2*dcr)
    for i = 1:dim(A)
      N = matrix(A[i])
      for j = 1:d2
        jj = (j - 1)*dcr
        for k = 1:dcr
          M[i, jj + k] = coeffs(N[j], copy = false)[k]
        end
      end
    end
    A.basis_mat = M
  end
  return nothing
end

function assure_has_basis_mat_trp(A::AlgMat)
  if isdefined(A, :basis_mat_trp)
    return nothing
  end

  M = basis_mat(A, copy = false)
  N = transpose(M)
  A.basis_mat_trp = N
  return nothing
end

function basis_mat(A::AlgMat; copy::Bool = true)
  assure_has_basis_mat(A)
  if copy
    return deepcopy(A.basis_mat)
  else
    return A.basis_mat
  end
end

function basis_mat_trp(A::AlgMat; copy::Bool = true)
  assure_has_basis_mat_trp(A)
  if copy
    return deepcopy(A.basis_mat_trp)
  else
    return A.basis_mat_trp
  end
end

################################################################################
#
#  Construction
#
################################################################################

function AlgMat(R::Ring, n::Int)
  A = AlgMat{elem_type(R), dense_matrix_type(elem_type(R))}(R)
  n2 = n^2
  A.dim = n2
  A.degree = n
  B = Vector{elem_type(A)}(undef, n2)
  for i = 1:n
    ni = n*(i - 1)
    for j = 1:n
      M = zero_matrix(R, n, n)
      M[j, i] = one(R)
      B[ni + j] = A(M)
    end
  end
  A.basis = B
  A.one = A(identity_matrix(R, n))
  A.has_one = true
  return A
end

# Constructs Mat_n(S) as an R-algebra
function AlgMat(R::Ring, S::AbsAlgAss, n::Int)
  A = AlgMat{elem_type(R), dense_matrix_type(elem_type(S))}(R)
  n2 = n^2
  A.dim = n2*dim(S)
  A.degree = n
  A.coefficient_ring = S
  B = Vector{elem_type(A)}(undef, dim(A))
  for k = 1:dim(S)
    n2k = n2*(k - 1)
    for i = 1:n
      ni = n2k + n*(i - 1)
      for j = 1:n
        M = zero_matrix(S, n, n)
        M[j, i] = S[k]
        B[ni + j] = A(M)
      end
    end
  end
  A.basis = B
  A.one = A(identity_matrix(S, n))
  A.has_one = true
  return A
end

function AlgMat(R::Ring, basis::Vector{<:MatElem})
  @assert length(basis) > 0
  A = AlgMat{elem_type(R), dense_matrix_type(elem_type(R))}(R)
  A.dim = length(basis)
  A.degree = nrows(basis[1])
  basis2 = Vector{elem_type(A)}(undef, dim(A))
  for i = 1:dim(A)
    basis2[i] = A(basis[i])
  end
  A.basis = basis2
  return A
end

function AlgMat(R::Ring, S::Ring, basis::Vector{<:MatElem})
  @assert length(basis) > 0
  A = AlgMat{elem_type(R), dense_matrix_type(elem_type(S))}(R)
  A.coefficient_ring = S
  A.dim = length(basis)
  A.degree = nrows(basis[1])
  basis2 = Vector{elem_type(A)}(undef, dim(A))
  for i = 1:dim(A)
    basis2[i] = A(basis[i])
  end
  A.basis = basis2
  return A
end

###############################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, A::AlgMat)
  print(io, "Matrix algebra of dimension ", dim(A), " over ", base_ring(A))
end

################################################################################
#
#  Deepcopy
#
################################################################################

function deepcopy_internal(A::AlgMat{T, S}, dict::IdDict) where { T, S }
  B = AlgMat{T, S}(base_ring(A))
  for x in fieldnames(typeof(A))
    if x != :base_ring x != :coefficient_ring && isdefined(A, x)
      setfield!(B, x, deepcopy_internal(getfield(A, x), dict))
    end
  end
  B.base_ring = A.base_ring
  if isdefined(A, :coefficient_ring)
    B.coefficient_ring = A.coefficient_ring
  end
  return B
end

################################################################################
#
#  Equality
#
################################################################################

# So far we don't have a canonical basis
==(A::AlgMat, B::AlgMat) = A === B

################################################################################
#
#  Conversion to AlgAss
#
################################################################################

function AlgAss(A::AlgMat{T, S}) where {T, S}
  K = base_ring(A)
  B = basis(A)
  d = dim(A)
  mt = Array{T, 3}(undef, d, d, d)
  for i in 1:d
    for j in 1:d
      mt[i, j, :] = coeffs(B[i]*B[j], copy = false)
    end
  end
  B = AlgAss(K, mt)
  return B, hom(B, A, identity_matrix(K, dim(A)), identity_matrix(K, dim(A)))
end
