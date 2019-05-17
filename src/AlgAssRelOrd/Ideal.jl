@inline order(I::AlgAssRelOrdIdl) = I.order

iszero(I::AlgAssRelOrdIdl) = (I.iszero == 1)

###############################################################################
#
#  String I/O
#
###############################################################################

function show(io::IO, a::AlgAssRelOrdIdl)
  print(io, "Ideal of ")
  show(IOContext(io, :compact => true), order(a))
  print(io, " with basis pseudo-matrix\n")
  show(IOContext(io, :compact => true), basis_pmat(a, copy = false))
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(a::AlgAssRelOrdIdl, dict::IdDict)
  b = typeof(a)(order(a))
  for i in fieldnames(typeof(a))
    if isdefined(a, i)
      if i != :order
        setfield!(b, i, Base.deepcopy_internal(getfield(a, i), dict))
      end
    end
  end
  return b
end

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_basis_pmat(a::AlgAssRelOrdIdl)
  if isdefined(a, :basis_pmat)
    return nothing
  end
  if !isdefined(a, :pseudo_basis)
    error("No pseudo_basis and no basis_pmat defined.")
  end
  pb = pseudo_basis(a, copy = false)
  A = algebra(order(a))
  M = zero_matrix(base_ring(A), dim(A), dim(A))
  C = Vector{frac_ideal_type(order_type(base_ring(A)))}()
  for i = 1:degree(L)
    elem_to_mat_row!(M, i, pb[i][1])
    push!(C, deepcopy(pb[i][2]))
  end
  M = M*basis_mat_inv(order(a), copy = false)
  a.basis_pmat = pseudo_hnf(PseudoMatrix(M, C), :lowerleft, true)
  return nothing
end

function assure_has_pseudo_basis(a::AlgAssRelOrdIdl)
  if isdefined(a, :pseudo_basis)
    return nothing
  end
  if !isdefined(a, :basis_pmat)
    error("No pseudo_basis and no basis_pmat defined.")
  end
  P = basis_pmat(a, copy = false)
  B = basis_alg(order(a), copy = false)
  A = algebra(order(a))
  K = base_ring(A)
  pseudo_basis = Vector{Tuple{elem_type(A), frac_ideal_type(order_type(K))}}()
  for i = 1:dim(A)
    t = A()
    for j = 1:dim(A)
      t += P.matrix[i, j]*B[j]
    end
    push!(pseudo_basis, (t, deepcopy(P.coeffs[i])))
  end
  a.pseudo_basis = pseudo_basis
  return nothing
end

function assure_has_basis_mat(a::AlgAssRelOrdIdl)
  if isdefined(a, :basis_mat)
    return nothing
  end
  a.basis_mat = basis_pmat(a).matrix
  return nothing
end

function assure_has_basis_mat_inv(a::AlgAssRelOrdIdl)
  if isdefined(a, :basis_mat_inv)
    return nothing
  end
  a.basis_mat_inv = inv(basis_mat(a, copy = false))
  return nothing
end

################################################################################
#
#  Pseudo basis / basis pseudo-matrix
#
################################################################################

function pseudo_basis(a::AlgAssRelOrdIdl; copy::Bool = true)
  assure_has_pseudo_basis(a)
  if copy
    return deepcopy(a.pseudo_basis)
  else
    return a.pseudo_basis
  end
end

function basis_pmat(a::AlgAssRelOrdIdl; copy::Bool = true)
  assure_has_basis_pmat(a)
  if copy
    return deepcopy(a.basis_pmat)
  else
    return a.basis_pmat
  end
end

################################################################################
#
#  (Inverse) basis matrix
#
################################################################################

function basis_mat(a::AlgAssRelOrdIdl; copy::Bool = true)
  assure_has_basis_mat(a)
  if copy
    return deepcopy(a.basis_mat)
  else
    return a.basis_mat
  end
end

function basis_mat_inv(a::AlgAssRelOrdIdl; copy::Bool = true)
  assure_has_basis_mat_inv(a)
  if copy
    return deepcopy(a.basis_mat_inv)
  else
    return a.basis_mat_inv
  end
end

################################################################################
#
#  Arithmetic
#
################################################################################

function +(a::AlgAssRelOrdIdl{S, T}, b::AlgAssRelOrdIdl{S, T}) where {S, T}
  if iszero(a)
    return deepcopy(b)
  elseif iszero(b)
    return deepcopy(a)
  end

  d = degree(order(a))
  M = vcat(basis_pmat(a), basis_pmat(b))
  M = sub(pseudo_hnf(M, :lowerleft), (d + 1):2*d, 1:d)
  return ideal(order(a), M, :nothing, false, true)
end

function *(a::AlgAssRelOrdIdl{S, T}, b::AlgAssRelOrdIdl{S, T}) where {S, T}
  if iszero(a)
    return deepcopy(a)
  elseif iszero(b)
    return deepcopy(b)
  end

  d = degree(order(a))
  pba = pseudo_basis(a, copy = false)
  pbb = pseudo_basis(b, copy = false)
  d2 = d^2
  A = algebra(order(a))

  M = zero_matrix(base_ring(A), d2, d)
  C = Array{frac_ideal_type(order_type(base_ring(A))), 1}(undef, d2)
  t = one(A)
  for i = 1:d
    i1d = (i - 1)*d
    for j = 1:d
      t = mul!(t, pba[i][1], pbb[j][1])
      elem_to_mat_row!(M, i1d + j, t)
      C[i1d + j] = simplify(pba[i][2]*pbb[j][2])
    end
  end

  H = pseudo_hnf(PseudoMatrix(M, C), :lowerleft)
  H = sub(H, (d2 - d + 1):d2, 1:d)
  H.matrix = H.matrix*basis_mat_inv(order(a), copy = false)
  H = pseudo_hnf(H, :lowerleft)
  return ideal(order(a), H, :nothing, false, true)
end

^(A::AlgAssRelOrdIdl, e::Int) = Base.power_by_squaring(A, e)
^(A::AlgAssRelOrdIdl, e::fmpz) = Base.power_by_squaring(A, BigInt(e))

function intersect(a::AlgAssRelOrdIdl{S, T}, b::AlgAssRelOrdIdl{S, T}) where {S, T}
  d = degree(order(a))
  Ma = basis_pmat(a)
  Mb = basis_pmat(b)
  M1 = hcat(Ma, deepcopy(Ma))
  z = zero_matrix(base_ring(Ma.matrix), d, d)
  M2 = hcat(PseudoMatrix(z, Mb.coeffs), Mb)
  M = vcat(M1, M2)
  H = sub(pseudo_hnf(M, :lowerleft), 1:d, 1:d)
  return ideal(order(a), H, :nothing, false, true)
end

################################################################################
#
#  Construction
#
################################################################################

function defines_ideal(O::AlgAssRelOrd{S, T}, M::PMat{S, T}) where {S, T}
  K = base_ring(algebra(O))
  coeffs = basis_pmat(O, copy = false).coeffs
  I = PseudoMatrix(identity_matrix(K, degree(O)), deepcopy(coeffs))
  return _spans_subset_of_pseudohnf(M, I, :lowerleft)
end

function ideal(O::AlgAssRelOrd{S, T}, M::PMat{S, T}, side::Symbol = :nothing, check::Bool = true, M_in_hnf::Bool = false) where {S, T}
  if check
    !defines_ideal(O, M) && error("The pseudo-matrix does not define an ideal.")
  end
  !M_in_hnf ? M = pseudo_hnf(M, :lowerleft, true) : nothing
  a = AlgAssRelOrdIdl{S, T}(O, M)
  _set_sidedness(a, side)
  return a
end

function ideal(O::AlgAssRelOrd{S, T}, M::Generic.Mat{S}, side::Symbol = :nothing, check::Bool = true) where {S, T}
  coeffs = deepcopy(basis_pmat(O, copy = false).coeffs)
  return ideal(O, PseudoMatrix(M, coeffs), side, check)
end

function ideal(O::AlgAssRelOrd{S, T}, x::AlgAssRelOrdElem{S, T}) where {S, T}
  @assert parent(x) == O

  if iscommutative(O)
    a = ideal(O, x, :left)
    a.isright = 1
    return a
  end

  A = algebra(O)
  t1 = A()
  t2 = A()
  M = zero_matrix(base_ring(A), degree(O)^2, degree(O))
  pb = pseudo_basis(O, copy = false)
  C = Vector{T}(undef, degree(O)^2)
  for i = 1:degree(O)
    i1d = (i - 1)*degree(O)
    C[i1d + i] = pb[i][2]^2
    for j = (i + 1):degree(O)
      C[i1d + j] = simplify(pb[i][2]*pb[j][2])
      C[(j - 1)*degree(O) + i] = deepcopy(C[i1d + j])
    end
  end

  for i = 1:degree(O)
    t1 = mul!(t1, pb[i][1], elem_in_algebra(x, copy = false))
    ii = (i - 1)*degree(O)
    for j = 1:degree(O)
      t2 = mul!(t2, t1, pb[j][1])
      elem_to_mat_row!(M, ii + j, t2)
    end
  end
  M = sub(pseudo_hnf(PseudoMatrix(M, C), :lowerleft), nrows(M) - degree(O) + 1:nrows(M), 1:ncols(M))
  M.matrix = M.matrix*basis_mat_inv(O, copy = false)
  M = pseudo_hnf(M, :lowerleft)

  return ideal(O, M, :twosided, false, true)
end

function ideal(O::AlgAssRelOrd{S, T}, x::AlgAssRelOrdElem{S, T}, action::Symbol) where {S, T}
  @assert parent(x) == O
  M = representation_matrix(x, action)
  if action == :left
    a = ideal(O, M, :right, false)
  elseif action == :right
    a = ideal(O, M, :left, false)
  end
  if iszero(x)
    a.iszero = 1
  end
  return a
end

*(O::AlgAssRelOrd{S, T}, x::AlgAssRelOrdElem{S, T}) where {S, T} = ideal(O, x, :right)
*(x::AlgAssRelOrdElem{S, T}, O::AlgAssRelOrd{S, T}) where {S, T} = ideal(O, x, :left)

################################################################################
#
#  Inclusion of elements in ideals
#
################################################################################

function in(x::AlgAssRelOrdElem, y::AlgAssRelOrdIdl)
  parent(x) !== order(y) && error("Order of element and ideal must be equal")
  O = order(y)
  b_pmat = basis_pmat(y, copy = false)
  t = matrix(base_ring(algebra(O)), 1, degree(O), coordinates(x))
  t = t*basis_mat_inv(y, copy = false)
  for i = 1:degree(O)
    if !(t[1, i] in b_pmat.coeffs[i])
      return false
    end
  end
  return true
end

################################################################################
#
#  Equality
#
################################################################################

function ==(A::AlgAssRelOrdIdl, B::AlgAssRelOrdIdl)
  order(A) !== order(B) && return false
  return basis_pmat(A, copy = false) == basis_pmat(B, copy = false)
end

################################################################################
#
#  isleft/isright
#
################################################################################

# functions isright_ideal and isleft_ideal are in AlgAss/Ideal.jl

function _test_ideal_sidedness(a::AlgAssRelOrdIdl, side::Symbol)
  O = order(a)
  b = ideal(O, one(O))

  if side == :right
    c = a*b
  elseif side == :left
    c = b*a
  else
    error("side must be either :left or :right")
  end

  return _spans_subset_of_pseudohnf(basis_pmat(c, copy = false), basis_pmat(a, copy = false), :lowerleft)
end
