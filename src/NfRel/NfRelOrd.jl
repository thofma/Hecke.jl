# I don't like that we have to drag S around
# Still hoping for julia/#18466

type NfOrdRel{T, S} <: Ring
  nf::NfRel{T}
  basis_nf::T
  basis_mat::GenMat{T}
  basis_mat_inv::GenMat{T}
  basis_pmat::PMat{T, S}
  pseudo_basis#::Vector{Tuple{NfRelOrdElem{T}, S}} # julia does not like
                                                   # forward declarations (yet)

  function NfOrdRel(K::NfRel{T}, M::PMat{T, S})
    z = new()
    z.nf = K
    z.basis_pmat = M
    z.basis_mat = M.matrix
    z.basis_mat_inv = inv(M.matrix)
    return z
  end
  
  function NfOrdRel(K::NfRel{T}, M::GenMat{T})
    z = new()
    z.nf = K
    z.basis_mat = M
    z.basis_mat_inv = inv(M)
    z.basis_pmat = pseudo_matrix(M)
    return z
  end
end

# show, discriminant, nf, basis_mat, basis_mat_inv, basis_pmat, pseudo_basis

type NfRelOrdElem{T} <: RingElem
  parent#::NfOrdRel{T, S} # I don't want to drag the S around
  elem_in_nf::NfRelElem{T}
  elem_in_basis::Vector{T}
  has_coord::Bool

  function NfRelOrdElem(O::NfOrdRel{T})
    z = new()
    z.parent = O
    z.elem_in_nf = zero(nf(O))
    return z
  end
end

type NfRelOrdIdl{T} end

type NfRelOrdFracIdl{T} end


# show, one, zero, isone, iszero, +, -, *, in, elem_in_basis

# help inference
parent{T}(x::NfRelOrdElem{NfRelElem{T}}) = x.parent::NfRelOrd{NfRelElem{T}, NfRelOrdFracIdl{T}}

parent(x::NfRelOrdElem{nf_elem}) = x.parent::NfRelOrd{nf_elem, NfOrdFracIdl}
