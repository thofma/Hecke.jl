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
  a.basis = Vector{elem_type(A)}(undef, nrows(M))
  for i = 1:nrows(M)
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
  return rank(vcat(basis_mat(a, false), M)) == nrows(basis_mat(a, false)) # so far we assume nrows(basis_mat) == rank(basis_mat)
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
  if r != nrows(M)
    M = sub(M, 1:r, 1:ncols(M))
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
  if length(b) == 0
    M = zero_matrix(base_ring(A), 0, dim(A))
    return ideal(A, M, side, true)
  end

  @assert parent(b[1]) == A

  M = zero_matrix(base_ring(A), length(b), dim(A))
  for i = 1:length(b)
    elem_to_mat_row!(M, i, b[i])
  end
  return ideal(A, M, side)
end

function ideal(A::AbsAlgAss, x::AbsAlgAssElem)
  t1 = A()
  t2 = A()
  M = zero_matrix(base_ring(A), dim(A)^2, dim(A))
  for i = 1:dim(A)
    t1 = mul!(t1, A[i], x)
    ii = (i - 1)*dim(A)
    for j = 1:dim(A)
      t2 = mul!(t2, t1, A[j])
      elem_to_mat_row!(M, ii + j, t2)
    end
  end

  return ideal(A, M, :twosided)
end

function ideal(A::AbsAlgAss, x::AbsAlgAssElem, action::Symbol)
  M = representation_matrix(x, action)
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
  @assert ncols(M) == dim(A)
  if !M_in_rref
    r, N = rref(M)
    if r == 0
      a = AbsAlgAssIdl{typeof(A), typeof(M)}(A, zero_matrix(base_ring(A), 0, dim(A)))
      a.iszero = 1
      return a
    end
    if r != nrows(N)
      M = sub(N, 1:r, 1:ncols(N))
    else
      M = N
    end
  end
  if M_in_rref && nrows(M) == 0
    a = AbsAlgAssIdl{typeof(A), typeof(M)}(A, M)
    a.iszero = 1
    return a
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
    a.isleft = 0
    a.isright = 1
  elseif side == :left
    a.isleft = 1
    a.isright = 0
  elseif side == :twosided
    a.isleft = 1
    a.isright = 1
  else
    a.isleft = 0
    a.isright = 0
  end
  return nothing
end

################################################################################
#
#  Quotient rings
#
################################################################################

function quo(A::S, a::AbsAlgAssIdl{S, T, U}) where { S, T, U }
  @assert A == algebra(a)
  K = base_ring(A)

  # First compute the vector space quotient
  Ma = basis_mat(a, false)
  M = hcat(transpose(Ma), identity_matrix(K, dim(A)))
  r = rref!(M)
  pivot_cols = Vector{Int}()
  j = 1
  for i = 1:ncols(M)
    if !iszero(M[j, i])
      if i > nrows(Ma)
        push!(pivot_cols, i - nrows(Ma))
      end
      j += 1
      if j > nrows(M)
        break
      end
    end
  end

  # We now have the basis (basis of the quotient, basis of the ideal)
  n = dim(A) - nrows(Ma)
  M = vcat(zero_matrix(K, n, dim(A)), Ma)
  oneK = K(1)
  zeroK = K()
  for i = 1:n
    M[i, pivot_cols[i]] = oneK
  end
  iM = inv(M)

  N = sub(M, 1:n, 1:dim(A))
  NN = sub(iM, 1:dim(A), 1:n)

  # Lift a basis of the quotient to A
  quotient_basis = Vector{elem_type(A)}(undef, n)
  b = zero_matrix(K, 1, n)
  for i = 1:n
    b[1, i] = oneK
    bN = b*N
    quotient_basis[i] = A([ bN[1, i] for i = 1:dim(A) ])
    b[1, i] = zeroK
  end

  # Build the multiplication table
  t = A()
  s = zero_matrix(K, 1, dim(A))
  mult_table = Array{elem_type(K), 3}(undef, n, n, n)
  for i = 1:n
    for j = 1:n
      t = mul!(t, quotient_basis[i], quotient_basis[j])
      elem_to_mat_row!(s, 1, t)
      sNN = s*NN
      mult_table[i, j, :] = [ sNN[1, k] for k  = 1:n ]
    end
  end

  B = AlgAss(K, mult_table)
  AtoB = hom(A, B, NN, N)
  return B, AtoB
end

# Assumes b \subseteq a
function quo(a::AbsAlgAssIdl{S, T, U}, b::AbsAlgAssIdl{S, T, U}) where { S, T, U }
  @assert algebra(a) == algebra(b)
  A = algebra(a)
  K = base_ring(A)

  # First compute the vector space quotient
  Ma = basis_mat(a, false)
  Mb = basis_mat(b, false)
  M = hcat(transpose(Mb), transpose(Ma))
  r = rref!(M)
  pivot_cols = Vector{Int}()
  j = 1
  for i = 1:ncols(M)
    if !iszero(M[j, i])
      if i > nrows(Mb)
        push!(pivot_cols, i - nrows(Mb))
      end
      j += 1
      if j > nrows(M)
        break
      end
    end
  end

  # Build the basis matrix for the quotient
  M = zero_matrix(K, dim(A), dim(A))
  n = nrows(Ma) - nrows(Mb)
  for i = 1:n
    for j = 1:dim(A)
      M[i, j] = deepcopy(Ma[pivot_cols[i], j])
    end
  end

  mult_table = _build_subalgebra_mult_table!(A, M)
  # M is now in rref

  B = AlgAss(K, mult_table)
  MM = sub(M, 1:dim(B), 1:dim(A))

  AtoB = AbsAlgAssMor{typeof(A), typeof(B), typeof(MM)}(A, B)

  N = transpose(vcat(MM, Mb)) # Another basis matrix for a
  function _image(x::AbsAlgAssElem)
    t, y = cansolve(N, matrix(K, dim(A), 1, coeffs(x, false)))
    if t
      return B([ y[i, 1] for i = 1:dim(B) ])
    else
      error("Element is not in the domain")
    end
  end

  function _preimage(x::AbsAlgAssElem)
    t = zero_matrix(K, 1, dim(B))
    for i = 1:dim(B)
      t[1, i] = x.coeffs[i]
    end
    tt = t*MM
    return A([ tt[1, i] for i = 1:dim(A) ])
  end

  AtoB.header.image = _image
  AtoB.header.preimage = _preimage
  return B, AtoB
end
