@inline order(I::AlgAssAbsOrdIdl) = I.order

function Base.one(S::AlgAssAbsOrdIdlSet)
  O = order(S)
  M = identity_matrix(FlintZZ, degree(O))
  return ideal(O, M, true)
end

function Base.copy(I::AlgAssAbsOrdIdl)
  return I
end

###############################################################################
#
#  String I/O
#
###############################################################################

function show(io::IO, a::AlgAssAbsOrdIdl)
  print(io, "Ideal of ")
  show(IOContext(io, :compact => true), order(a))
  println(io, " with basis matrix")
  print(io, a.basis_mat)
end

################################################################################
#
#  Ideal Set
#
################################################################################

function show(io::IO, a::AlgAssAbsOrdIdlSet)
  print(io, "Set of ideals of $(order(a))\n")
end

order(a::AlgAssAbsOrdIdlSet) = a.order

parent(I::AlgAssAbsOrdIdl) = AlgAssAbsOrdIdlSet(order(I))

function IdealSet(O::AlgAssAbsOrd)
   return AlgAssAbsOrdIdlSet(O)
end

elem_type(::Type{AlgAssAbsOrdIdlSet{S, T}}) where {S, T} = AlgAssAbsOrdIdl{S, T}

elem_type(::AlgAssAbsOrdIdlSet{S, T}) where {S, T} = AlgAssAbsOrdIdl{S, T}

parent_type(::Type{AlgAssAbsOrdIdl{S, T}}) where {S, T} = AlgAssAbsOrdIdlSet{S, T}

################################################################################
#
#  Basis (matrices)
#
################################################################################

function assure_has_basis(a::AlgAssAbsOrdIdl{S, T}) where {S, T}
  if isdefined(a, :basis)
    return nothing
  end

  O = order(a)
  a.basis = Vector{AlgAssAbsOrdElem{S, T}}(undef, degree(O))
  for i = 1:degree(O)
    a.basis[i] = elem_from_mat_row(O, basis_mat(a, Val{false}), i)
  end
  return nothing
end

function assure_has_basis_mat(a::AlgAssAbsOrdIdl{S, T}) where {S, T}
  if isdefined(a, :basis_mat)
    return nothing
  end

  O = order(a)
  d = degree(O)
  a.basis_mat = zero_matrix(FlintZZ, d, d)
  for i = 1:d
    for j = 1:d
      a.basis_mat[i, j] = elem_in_basis(basis[i])[j]
    end
  end
  a.basis_mat = _hnf(a.basis_mat, :lowerleft)
  return nothing
end

function assure_has_basis_mat_inv(a::AlgAssAbsOrdIdl)
  if isdefined(a, :basis_mat_inv)
    return nothing
  else
    a.basis_mat_inv = FakeFmpqMat(pseudo_inv(basis_mat(a, Val{false})))
    return nothing
  end
end

function basis(a::AlgAssAbsOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis(a)
  if copy == Val{true}
    return deepcopy(a.basis)
  else
    return a.basis
  end
end

function basis_mat(a::AlgAssAbsOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_mat(a)
  if copy == Val{true}
    return deepcopy(a.basis_mat)
  else
    return a.basis_mat
  end
end

function basis_mat_inv(a::AlgAssAbsOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_mat_inv(a)
  if copy == Val{true}
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

function +(a::AlgAssAbsOrdIdl{S, T}, b::AlgAssAbsOrdIdl{S, T}) where {S, T}
  d = degree(order(a))
  M = vcat(basis_mat(a), basis_mat(b))
  M = view(_hnf(M, :lowerleft), (d + 1):2*d, 1:d)
  return ideal(order(a), M, true)
end

function *(a::AlgAssAbsOrdIdl{S, T}, b::AlgAssAbsOrdIdl{S, T}) where {S, T}
  d = degree(order(a))
  ba = basis(a, Val{false})
  bb = basis(b, Val{false})
  M = zero_matrix(FlintZZ, d^2, d)
  for i = 1:d
    for j = 1:d
      t = ba[i]*bb[j]
      for k = 1:d
        M[(i - 1)*d + j, k] = elem_in_basis(t)[k]
      end
    end
  end
  M = view(_hnf(M, :lowerleft), (d^2 - d + 1):d^2, 1:d)
  return ideal(order(a), M, true)
end

Base.:(^)(A::AlgAssAbsOrdIdl, e::Int) = Base.power_by_squaring(A, e)

function intersection(a::AlgAssAbsOrdIdl{S, T}, b::AlgAssAbsOrdIdl{S, T}) where {S, T}
  d = degree(order(a))
  H = vcat(basis_mat(a), basis_mat(b))
  K = _kernel(H)
  return ideal(order(a), _hnf(view(K, 1:d, 1:d)*basis_mat(a, Val{false}), :lowerleft), true)
end

################################################################################
#
#  Construction
#
################################################################################

function ideal(O::AlgAssAbsOrd{S, T}, M::fmpz_mat, M_in_hnf::Bool = false) where {S, T}
  !M_in_hnf ? M = _hnf(M, :lowerleft) : nothing
  return AlgAssAbsOrdIdl{S, T}(O, M)
end

function ideal(O::AlgAssAbsOrd{S, T}, a::AlgAssAbsOrdElem{S, T}) where {S, T}
  @assert parent(a) == O
  M = representation_matrix(a)
  return ideal(O, M)
end

function ideal_from_z_gens(O::AlgAssAbsOrd, b::Vector{T}) where { T <: AlgAssAbsOrdElem }
  d = degree(O)
  @assert length(b) >= d

  M = zero_matrix(FlintZZ, length(b), d)
  for i = 1:length(b)
    for j = 1:d
      M[i, j] = elem_in_basis(b[i])[j]
    end
  end
  M = _hnf(M, :lowerleft)
  if d < length(b)
    M = sub(M, (length(b) - d + 1):length(b), 1:d)
  end
  return ideal(O, M, true)
end

################################################################################
#
#  Extend/contract
#
################################################################################

#THIS IS WRONG! The ideal generated by one element need to consider multiplication on both sides
function extend(A::AlgAssAbsOrdIdl, O::AlgAssAbsOrd)
  # Assumes order(A) \subseteq O

  d = degree(O)
  M = zero_matrix(FlintZZ, d^2, d)
  X = map(O, basis(A, Val{false}))
  Y = basis(O, Val{false})
  t = O()
  for i = 1:d
    for j = 1:d
      t = X[i]*Y[j]
      for k = 1:d
        M[(i - 1)*d + j, k] = elem_in_basis(t, Val{false})[k]
      end
    end
  end
  M = sub(_hnf(M, :lowerleft), d*(d - 1) + 1:d^2, 1:d)
  return ideal(O, M, true)
end

*(A::AlgAssAbsOrdIdl, O::AlgAssAbsOrd) = extend(A, O)

function contract(A::AlgAssAbsOrdIdl, O::AlgAssAbsOrd)
  # Assumes O \subseteq order(A)

  d = degree(O)
  M = basis_mat(O, Val{false})*basis_mat_inv(order(A), Val{false})
  @assert M.den == 1
  H = vcat(basis_mat(A), M.num)
  K = _kernel(H)
  M = sub(K, 1:d, 1:d)*basis_mat(A, Val{false})
  M = M*basis_mat(order(A), Val{false})*basis_mat_inv(O, Val{false})
  @assert M.den == 1
  M = _hnf(M.num, :lowerleft)
  return ideal(O, M, true)
end

intersection(O::AlgAssAbsOrd, A::AlgAssAbsOrdIdl) = contract(A, O)
intersection(A::AlgAssAbsOrdIdl, O::AlgAssAbsOrd) = contract(A, O)

################################################################################
#
#  Inclusion of elements in ideals
#
################################################################################

function in(x::AlgAssAbsOrdElem, I::AlgAssAbsOrdIdl)
  el = elem_in_basis(x)
  y = matrix(FlintZZ, 1, length(el), el)
  M1, d =pseudo_inv(I.basis_mat)
  if FakeFmpqMat(y*M1, d).den==1
    return true
  else
    return false
  end
end

################################################################################
#
#  Equality
#
################################################################################

function ==(A::AlgAssAbsOrdIdl, B::AlgAssAbsOrdIdl)
  order(A) != order(B) && return false
  return basis_mat(A, Val{false}) == basis_mat(B, Val{false})
end

################################################################################
#
#  Hashing
#
################################################################################

function Base.hash(A::AlgAssAbsOrdIdl, h::UInt)
  return Base.hash(basis_mat(A, Val{false}), h)
end

################################################################################
#
#  Idempotents
#
################################################################################

# Algorithm 1.3.2 in Cohen "Advanced Topics in Computational Number Theory"
function idempotents(a::AlgAssAbsOrdIdl, b::AlgAssAbsOrdIdl)
  !(order(a) === order(b)) && error("Parent mismatch")
  O = order(a)
  d = degree(O)
  A = basis_mat(a, Val{false})
  B = basis_mat(b, Val{false})

  C = vcat(A, B)
  H, U = hnf_with_transform(C)

  if H != vcat(identity_matrix(FlintZZ, d), zero_matrix(FlintZZ, d, d))
    error("Ideals are not coprime")
  end

  X = sub(U, 1:1, 1:d)
  XA = X*A
  x = O([ XA[1, i] for i = 1:d ])
  @assert x in a
  y = one(O) - x
  @assert y in b
  return x, y
end
