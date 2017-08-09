# I don't like that we have to drag S around
# Still hoping for julia/#18466

type NfRelOrd{T, S} <: Ring
  nf::NfRel{T}
  basis_nf::Vector{NfRel{T}}
  basis_mat::GenMat{T}
  basis_mat_inv::GenMat{T}
  basis_pmat::PMat{T, S}
  pseudo_basis#::Vector{Tuple{NfRelOrdElem{T}, S}} # julia does not like
                                                   # forward declarations (yet)

  function NfRelOrd(K::NfRel{T}, M::PMat{T, S})
    z = new()
    z.nf = K
    z.basis_pmat = M
    z.basis_mat = M.matrix
    z.basis_mat_inv = inv(M.matrix)
    return z
  end
  
  function NfRelOrd(K::NfRel{T}, M::GenMat{T})
    z = new()
    z.nf = K
    z.basis_mat = M
    z.basis_mat_inv = inv(M)
    z.basis_pmat = pseudo_matrix(M)
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

function assure_has_pseudo_basis(O::NfRelOrd)
  if isdefined(O, :pseudo_basis)
    return nothing
  end
  pseudo_basis = Vector{Tuple{NfRelOrdElem, NfOrdFracIdl}}()
  for i = 1:degree(O)
    a = elem_from_mat_row(nf(O), basis_mat(O), i)
    push!(pseudo_basis, (O(a), basis_pmat(O).coeffs[i]))
  end
  O.pseudo_basis = pseudo_basis
  return nothing
end

################################################################################
#
#  Pseudo basis
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

################################################################################
#
#  (Inverse) basis matrix
#
################################################################################

function basis_pmat{T}(O::NfRelOrd, copy::Type{Val{T}} = Val{true})
  if copy == Val{true}
    return deepcopy(O.basis_pmat)
  else
    return O.basis_pmat
  end
end

function basis_mat{T}(O::NfRelOrd, copy::Type{Val{T}} = Val{true})
  if copy == Val{true}
    return deepcopy(O.basis_mat)
  else
    return O.basis_mat
  end
end

function basis_mat_inv{T}(O::NfRelOrd, copy::Type{Val{T}} = Val{true})
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
#  Construction
#
################################################################################

function Order{T}(L::NfRel{T}, M::GenMat{T})
  # checks
  return NfRelOrd{T, NfOrdFracIdl}(L, M)
end

function Order{T, S}(L::NfRel{T}, M::PMat{T, S})
  # checks
  return NfRelOrd{T, S}(L, M)
end

# discriminant

type NfRelOrdIdl{T} end

type NfRelOrdFracIdl{T} end
