mutable struct NfRelOrdIdl{T, S}
  order::NfRelOrd{T, S}
  basis_pmat::PMat{T, S}
  pseudo_basis::Vector{Tuple{NfRelOrdElem{T}, S}}
  basis_mat::GenMat{T}
  basis_mat_inv::GenMat{T}

  norm
  has_norm::Bool

  function NfRelOrdIdl{T, S}(O::NfRelOrd{T, S}) where {T, S}
    z = new{T, S}()
    z.order = O
    z.has_norm = false
    return z
  end

  function NfRelOrdIdl{T, S}(O::NfRelOrd{T, S}, M::PMat{T, S}) where {T, S}
    z = new{T, S}()
    z.order = O
    z.basis_pmat = M
    z.basis_mat = M.matrix
    z.has_norm = false
    return z
  end

  function NfRelOrdIdl{T, S}(O::NfRelOrd{T, S}, M::GenMat{T}) where {T, S}
    z = new{T, S}()
    z.order = O
    z.basis_pmat = pseudo_matrix(M)
    z.basis_mat = M
    z.has_norm = false
    return z
  end
end

order(a::NfRelOrdIdl) = a.order

nf(a::NfRelOrdIdl) = nf(order(a))

function assure_has_basis_pmat(a::NfRelOrdIdl{T, S}) where {T, S}
  if isdefined(a, :basis_pmat)
    return nothing
  end
  if !isdefined(a, :pseudo_basis)
    error("No pseudo_basis and no basis_pmat defined.")
  end
  pb = pseudo_basis(a)
  L = nf(order(a))
  M = MatrixSpace(base_ring(L), degree(L), degree(L))()
  C = Vector{S}()
  for i = 1:degree(L)
    elem_to_mat_row!(M, i, L(pb[i][1]))
    push!(C, pb[i][2])
  end
  a.basis_pmat = PseudoMatrix(M, C)
  return nothing
end

function assure_has_pseudo_basis(a::NfRelOrdIdl{T, S}) where {T, S}
  if isdefined(a, :pseudo_basis)
    return nothing
  end
  if !isdefined(a, :basis_pmat)
    error("No pseudo_basis and no basis_pmat defined.")
  end
  P = basis_pmat(a)
  L = nf(order(a))
  pseudo_basis = Vector{Tuple{NfRelOrdElem{T}, S}}()
  for i = 1:degree(L)
    x = elem_from_mat_row(L, P.matrix, i)
    push!(pseudo_basis, (order(a)(x), P.coeffs[i]))
  end
  a.pseudo_basis = pseudo_basis
  return nothing
end

function assure_has_basis_mat(a::NfRelOrdIdl)
  if isdefined(a, :basis_mat)
    return nothing
  end
  a.basis_mat = basis_pmat(a).matrix
  return nothing
end

function assure_has_basis_mat_inv(a::NfRelOrdIdl)
  if isdefined(a, :basis_mat_inv)
    return nothing
  end
  a.basis_mat_inv = inv(basis_mat(a))
  return nothing
end

function pseudo_basis(a::NfRelOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_pseudo_basis(a)
  if copy == Val{true}
    return deepcopy(a.pseudo_basis)
  else
    return a.pseudo_basis
  end
end

function basis_pmat(a::NfRelOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_pmat(a)
  if copy == Val{true}
    return deepcopy(a.basis_pmat)
  else
    return a.basis_pmat
  end
end

function basis_mat(a::NfRelOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_mat(a)
  if copy == Val{true}
    return deepcopy(a.basis_mat)
  else
    return a.basis_mat
  end
end

function basis_mat_inv(a::NfRelOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_mat_inv(a)
  if copy == Val{true}
    return deepcopy(a.basis_mat_inv)
  else
    return a.basis_mat_inv
  end
end

function show(io::IO, a::NfRelOrdIdl)
  print(io, "Ideal of (")
  print(io, order(a), ")\n")
  print(io, "with basis pseudo-matrix\n")
  print(io, basis_pmat(a))
end

function ideal(O::NfRelOrd{T, S}, M::PMat{T, S}) where {T, S}
  # checks
  return NfRelOrdIdl{T, S}(O, deepcopy(M))
end

function ideal(O::NfRelOrd{T, S}, M::GenMat{T}) where {T, S}
  # checks
  return NfRelOrdIdl{T, S}(O, deepcopy(M))
end

function Base.deepcopy_internal(a::NfRelOrdIdl{T, S}, dict::ObjectIdDict) where {T, S}
  z = NfRelOrdIdl{T, S}(a.order)
  for x in fieldnames(a)
    if x != :order && isdefined(a, x)
      setfield!(z, x, Base.deepcopy_internal(getfield(a, x), dict))
    end
  end
  z.order = a.order
  return z
end

function ==(a::NfRelOrdIdl, b::NfRelOrdIdl)
  order(a) != order(b) && return false
  return basis_pmat(a) == basis_pmat(b)
end

mutable struct NfRelOrdFracIdl{T, S}
  order::NfRelOrd{T, S}
  num::NfRelOrdIdl{T, S}
  den_abs::NfOrdElem # used if T == nf_elem
  den_rel::NfRelOrdElem # used otherwise

  function NfRelOrdFracIdl{T, S}(O::NfRelOrd{T, S}) where {T, S}
    z = new{T, S}()
    z.order = O
    return z
  end

  function NfRelOrdFracIdl{nf_elem, S}(O::NfRelOrd{nf_elem, S}, a::NfRelOrdIdl{nf_elem, S}, d::NfOrdElem) where S
    z = new{nf_elem, S}()
    z.order = O
    z.num = a
    z.den_abs = d
    return z
  end

  function NfRelOrdFracIdl{T, S}(O::NfRelOrd{T, S}, a::NfRelOrdIdl{T, S}, d::NfRelOrdElem) where {T, S}
    z = new{T, S}()
    z.order = O
    z.num = a
    z.den_rel = d
    return z
  end
end

order(a::NfRelOrdFracIdl) = a.order

nf(a::NfRelOrdFracIdl) = nf(order(a))

num(a::NfRelOrdFracIdl) = a.num

den(a::NfRelOrdFracIdl{nf_elem, S}) where {S} = a.den_abs
den(a::NfRelOrdFracIdl{T, S}) where {S, T} = a.den_rel

function Base.show(io::IO, a::NfRelOrdFracIdl)
  print(io, "Fractional ideal of (")
  print(io, order(a), ")\n")
  print(io, "with basis pseudo-matrix\n")
  print(io, Hecke.basis_pmat(num(a)), "\n")
  print(io, "and denominator ", den(a))
end

function frac_ideal(O::NfRelOrd{nf_elem, S}, a::NfRelOrdIdl{nf_elem, S}, d::NfOrdElem) where S
  return NfRelOrdFracIdl{nf_elem, S}(O, a, d)
end

function frac_ideal(O::NfRelOrd{T, S}, a::NfRelOrdIdl{T, S}, d::NfRelOrdElem{T}) where {T, S}
  return NfRelOrdFracIdl{T, S}(O, a, d)
end

function Base.deepcopy_internal(a::NfRelOrdFracIdl{T, S}, dict::ObjectIdDict) where {T, S}
  z = NfRelOrdFracIdl{T, S}(a.order)
  for x in fieldnames(a)
    if x != :order && isdefined(a, x)
      setfield!(z, x, Base.deepcopy_internal(getfield(a, x), dict))
    end
  end
  z.order = a.order
  return z
end

function ==(a::NfRelOrdFracIdl, b::NfRelOrdFracIdl)
  order(a) != order(b) && return false
  return den(a) == den(b) && num(a) == num(b)
end
