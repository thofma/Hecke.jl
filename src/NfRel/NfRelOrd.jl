# I don't like that we have to drag S around
# Still hoping for julia/#18466

type NfRelOrd{T, S} <: Ring
  nf::NfRel{T}
  basis_nf::Vector{NfRelElem{T}}
  basis_mat::GenMat{T}
  basis_mat_inv::GenMat{T}
  basis_pmat::PMat{T, S}
  pseudo_basis#::Vector{Tuple{NfRelOrdElem{T}, S}} # julia does not like
                                                   # forward declarations (yet)

  function NfRelOrd(K::NfRel{T}, M::PMat{T, S})
    z = new()
    z.nf = K
    z.basis_pmat = M
    return z
  end
  
  function NfRelOrd(K::NfRel{T}, M::GenMat{T})
    z = new()
    z.nf = K
    z.basis_mat = M
    z.basis_pmat = pseudo_matrix(M)
    return z
  end

  function NfRelOrd(K::NfRel{T})
    z = new()
    z.nf = K
    return z
  end
end

################################################################################
#
#  Basic field access
#
################################################################################

nf(O::NfRelOrd) = O.nf

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_basis_pmat{T, S}(O::NfRelOrd{T, S})
  if isdefined(O, :basis_pmat)
    return nothing
  end
  if !isdefined(O, :pseudo_basis)
    error("No pseudo_basis and no basis_pmat defined.")
  end
  pb = pseudo_basis(O)
  L = nf(O)
  M = MatrixSpace(base_ring(L), degree(O), degree(O))()
  C = Vector{S}()
  for i = 1:degree(O)
    elem_to_mat_row!(M, i, L(pb[i][1]))
    push!(C, pb[i][2])
  end
  O.basis_pmat = PseudoMatrix(M, C)
  return nothing
end

function assure_has_pseudo_basis{T, S}(O::NfRelOrd{T, S})
  if isdefined(O, :pseudo_basis)
    return nothing
  end
  if !isdefined(O, :basis_pmat)
    error("No pseudo_basis and no basis_pmat defined.")
  end
  P = basis_pmat(O)
  L = nf(O)
  pseudo_basis = Vector{Tuple{NfRelOrdElem{T}, S}}()
  for i = 1:degree(O)
    a = elem_from_mat_row(L, P.matrix, i)
    push!(pseudo_basis, (O(a), P.coeffs[i]))
  end
  O.pseudo_basis = pseudo_basis
  return nothing
end

function assure_has_basis_nf{T, S}(O::NfRelOrd{T, S})
  if isdefined(O, :basis_nf)
    return nothing
  end
  L = nf(O)
  pb = pseudo_basis(O)
  basis_nf = Vector{NfRelElem{T}}()
  for i = 1:degree(O)
    push!(basis_nf, L(pb[i][1]))
  end
  O.basis_nf = basis_nf
  return nothing
end

function assure_has_basis_mat(O::NfRelOrd)
  if isdefined(O, :basis_mat)
    return nothing
  end
  O.basis_mat = basis_pmat(O).matrix
  return nothing
end

function assure_has_basis_mat_inv(O::NfRelOrd)
  if isdefined(O, :basis_mat_inv)
    return nothing
  end
  O.basis_mat_inv = inv(basis_mat(O))
  return nothing
end

################################################################################
#
#  Pseudo basis / basis pseudo-matrix
#
################################################################################

function pseudo_basis{T}(O::NfRelOrd, copy::Type{Val{T}} = Val{true})
  assure_has_pseudo_basis(O)
  if copy == Val{true}
    return deepcopy(O.pseudo_basis)
  else
    return O.pseudo_basis
  end
end

function basis_pmat{T}(O::NfRelOrd, copy::Type{Val{T}} = Val{true})
  assure_has_basis_pmat(O)
  if copy == Val{true}
    return deepcopy(O.basis_pmat)
  else
    return O.basis_pmat
  end
end

################################################################################
#
#  Basis / (inverse) basis matrix
#
################################################################################

function basis_nf{T}(O::NfRelOrd, copy::Type{Val{T}} = Val{true})
  assure_has_basis_nf(O)
  if copy == Val{true}
    return deepcopy(O.basis_nf)
  else
    return O.basis_nf
  end
end

function basis_mat{T}(O::NfRelOrd, copy::Type{Val{T}} = Val{true})
  assure_has_basis_mat(O)
  if copy == Val{true}
    return deepcopy(O.basis_mat)
  else
    return O.basis_mat
  end
end

function basis_mat_inv{T}(O::NfRelOrd, copy::Type{Val{T}} = Val{true})
  assure_has_basis_mat_inv(O)
  if copy == Val{true}
    return deepcopy(O.basis_mat_inv)
  else
    return O.basis_mat_inv
  end
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, O::NfRelOrd)
  print(io, "Relative order of ")
  println(io, nf(O))
  print(io, "with pseudo-basis ")
  for i = 1:degree(O)
    print(io, "\n")
    print(io, pseudo_basis(O)[i])
  end
end

################################################################################
#
#  Degree
#
################################################################################

degree(O::NfRelOrd) = degree(nf(O))

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal{T, S}(O::NfRelOrd{T, S}, dict::ObjectIdDict)
  z = NfRelOrd{T, S}(O.nf)
  for x in fieldnames(O)
    if x != :nf && isdefined(O, x)
      setfield!(z, x, Base.deepcopy_internal(getfield(O, x), dict))
    end
  end
  z.nf = O.nf
  return z
end

################################################################################
#
#  Construction
#
################################################################################

function Order(L::NfRel{nf_elem}, M::GenMat{nf_elem})
  # checks
  return NfRelOrd{nf_elem, NfOrdFracIdl}(L, M)
end

function Order{T}(L::NfRel{NfRelElem{T}}, M::GenMat{NfRelElem{T}})
  # checks
  return NfRelOrd{NfRelElem{T}, NfRelOrdFracIdl{T}}(L, M)
end

function Order{T, S}(L::NfRel{T}, M::PMat{T, S})
  # checks
  return NfRelOrd{T, S}(L, M)
end

################################################################################
#
#  Equality
#
################################################################################

function ==(R::NfRelOrd, S::NfRelOrd)
  nf(R) != nf(S) && return false
  return basis_pmat(R) == basis_pmat(S)
end


# discriminant

type NfRelOrdIdl{T} end

type NfRelOrdFracIdl{T} end
