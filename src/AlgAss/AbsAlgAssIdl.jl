algebra(a::AbsAlgAssIdl) = a.algebra

iszero(a::AbsAlgAssIdl) = (a.iszero == 1)

###############################################################################
#
#  String I/O
#
###############################################################################

function show(io::IO, a::AbsAlgAssIdl)
  print(io, "Ideal of ")
  print(io, algebra(a))
  println(io, " with basis matrix")
  print(io, basis_mat(a, false))
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(a::AbsAlgAssIdl, dict::IdDict)
  b = typeof(a)(algebra(a))
  for i in fieldnames(typeof(a))
    if isdefined(a, i)
      if i != :algebra
        setfield!(b, i, Base.deepcopy_internal(getfield(a, i), dict))
      end
    end
  end
  return b
end

################################################################################
#
#  Basis (matrices)
#
################################################################################

function assure_has_basis(a::AbsAlgAssIdl)
  if isdefined(a, :basis)
    return nothing
  end

  A = algebra(a)
  M = basis_mat(a, false)
  a.basis = Vector{elem_type(A)}(undef, rows(M))
  for i = 1:rows(M)
    a.basis[i] = elem_from_mat_row(A, M, i)
  end
  return nothing
end

function basis(a::AbsAlgAssIdl, copy::Bool = true)
  assure_has_basis(a)
  if copy
    return deepcopy(a.basis)
  else
    return a.basis
  end
end

function basis_mat(a::AbsAlgAssIdl, copy::Bool = true)
  if copy
    return deepcopy(a.basis_mat)
  else
    return a.basis_mat
  end
end

################################################################################
#
#  Inclusion of elements in ideals
#
################################################################################

function in(x::T, a::AbsAlgAssIdl{S, T, U}) where {S, T, U}
  A = algebra(a)
  M = matrix(base_ring(A), 1, dim(A), coeffs(x, false))
  return rank(vcat(basis_mat(a, false), M)) == rows(basis_mat(a, false)) # so far we assume rows(basis_mat) == rank(basis_mat)
end

################################################################################
#
#  Test right/left
#
################################################################################

function _test_ideal_sidedness(a::AbsAlgAssIdl, side::Symbol)
  A = algebra(a)
  ba = basis(a, false)
  t = A()
  for i = 1:dim(A)
    for j = 1:length(ba)
      if side == :left
        t = mul!(t, A[i], ba[j])
      elseif side == :right
        t = mul!(t, ba[j], A[i])
      end
      if !(t in a)
        return false
      end
    end
  end
  return true
end

function isright_ideal(a::AbsAlgAssIdl)
  if a.isright == 1
    return true
  elseif a.isright == 2
    return false
  end

  if _test_ideal_sidedness(a, :right)
    a.isright = 1
    return true
  end

  a.isright = 2
  return false
end

function isleft_ideal(a::AbsAlgAssIdl)
  if a.isleft == 1
    return true
  elseif a.isleft == 2
    return false
  end

  if _test_ideal_sidedness(a, :left)
    a.isleft = 1
    return true
  end

  a.isleft = 2
  return false
end

################################################################################
#
#  Arithmetic
#
################################################################################

function +(a::AbsAlgAssIdl{S, T, U}, b::AbsAlgAssIdl{S, T, U}) where {S, T, U}
  if iszero(a)
    return deepcopy(b)
  elseif iszero(b)
    return deepcopy(a)
  end

  M = vcat(basis_mat(a), basis_mat(b))
  r = rref!(M)
  if r != rows(M)
    M = sub(M, 1:r, 1:cols(M))
  end
  return ideal(algebra(a), M, :nothing, true)
end

function *(a::AbsAlgAssIdl{S, T, U}, b::AbsAlgAssIdl{S, T, U}) where {S, T, U}
  if iszero(a)
    return deepcopy(a)
  elseif iszero(b)
    return deepcopy(b)
  end

  if !isright_ideal(a)
    error("First argument is not a right ideal")
  end
  if !isleft_ideal(b)
    error("Second argument is not a left ideal")
  end

  A = algebra(a)
  ba = basis(a, false)
  bb = basis(b, false)
  M = zero_matrix(base_ring(A), length(ba)*length(bb), dim(A))
  for i = 1:length(ba)
    ii = (i - 1)*length(bb)
    for j = 1:length(bb)
      elem_to_mat_row!(M, ii + j, ba[i]*bb[j])
    end
  end
  return ideal(algebra(a), M, :nothing)
end

^(A::AbsAlgAssIdl, e::Int) = Base.power_by_squaring(A, e)
^(A::AbsAlgAssIdl, e::fmpz) = Base.power_by_squaring(A, BigInt(e))

function one(a::AbsAlgAssIdl)
  return ideal(algebra(a), identity_matrix(base_ring(A), dim(A)), :twosided, true)
end

function Base.copy(a::AbsAlgAssIdl)
  return a
end

################################################################################
#
#  Equality
#
################################################################################

function ==(a::AbsAlgAssIdl, b::AbsAlgAssIdl)
  algebra(a) != algebra(b) && return false
  return basis_mat(a, false) == basis_mat(b, false)
end

################################################################################
#
#  Construction
#
################################################################################

function ideal_from_gens(A::AbsAlgAss, b::Vector{T}, side::Symbol = :nothing) where { T <: AbsAlgAssElem }
  @assert length(b) > 0
  @assert parent(b[1]) == A

  M = zero_matrix(base_ring(A), length(b), dim(A))
  for i = 1:length(b)
    elem_to_mat_row!(M, i, b[i])
  end
  return ideal(A, M, side)
end

function ideal(A::AbsAlgAss, x::AbsAlgAssElem)
  t = A()
  M = zero_matrix(base_ring(A), 2*dim(A), dim(A))
  for i = 1:dim(A)
    t = mul!(t, A[i], x)
    elem_to_mat_row!(M, i, t)
    t = mul!(t, x, A[i])
    elem_to_mat_row!(M, dim(A) + i, t)
  end

  return ideal(A, M, :twosided)
end

function ideal(A::AbsAlgAss, x::AbsAlgAssElem, action::Symbol)
  t = A()
  M = zero_matrix(base_ring(A), dim(A), dim(A))
  for i = 1:dim(A)
    if action == :left
      t = mul!(t, x, A[i])
      elem_to_mat_row!(M, i, t)
    elseif action == :right
      t = mul!(t, A[i], x)
      elem_to_mat_row!(M, i, t)
    else
      error("action must be :left or :right")
    end
  end

  a = ideal(A, M)
  if action == :left
    a.isright = 1
  elseif action == :right
    a.isleft = 1
  end

  return a
end

function ideal(A::AbsAlgAss, M::MatElem, side::Symbol = :nothing, M_in_rref::Bool = false)
  @assert base_ring(M) == base_ring(A)
  @assert cols(M) == dim(A)
  if !M_in_rref
    r, N = rref(M)
    if r == 0
      a = AbsAlgAssIdl{typeof(A), typeof(M)}(A, zero_matrix(base_ring(A), 0, dim(A)))
      a.iszero = 1
      return a
    end
    if r != rows(N)
      M = sub(N, 1:r, 1:cols(N))
    else
      M = N
    end
  end
  a = AbsAlgAssIdl{typeof(A), typeof(M)}(A, M)
  _set_sidedness(a, side)
  a.iszero = 2
  return a
end

# Helper function to set the side-flags
# side can be :right, :left or :twosided
function _set_sidedness(a::AbsAlgAssIdl, side::Symbol)
  if side == :right
    a.isleft = 2
    a.isright = 1
  elseif side == :left
    a.isleft = 1
    a.isright = 2
  elseif side == :twosided
    a.isleft = 1
    a.isright = 1
  else
    a.isleft = 0
    a.isright = 0
  end
  return nothing
end
