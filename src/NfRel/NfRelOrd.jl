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

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, O::NfOrdRel)
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

degree(O::NfOrdRel) = degree(nf(O))

################################################################################
#
#  Basic field access
#
################################################################################

nf(O::NfOrdRel) = O.nf

################################################################################
#
#  Construction
#
################################################################################

function RelativeOrder{T}(L::NfRel{T}, M::GenMat{T})
  # checks
  return NfOrdRel{T, NfOrdFracIdl}(L, M)
end

function RelativeOrder{T, S}(L::NfRel{T}, M::PMat{T, S})
  # checks
  return NfOrdRel{T, S}(L, M)
end

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_pseudo_basis(O::NfOrdRel)
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

function pseudo_basis{T}(O::NfOrdRel, copy::Type{Val{T}} = Val{true})
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

function basis_pmat{T}(O::NfOrdRel, copy::Type{Val{T}} = Val{true})
  if copy == Val{true}
    return deepcopy(O.basis_pmat)
  else
    return O.basis_pmat
  end
end

function basis_mat{T}(O::NfOrdRel, copy::Type{Val{T}} = Val{true})
  if copy == Val{true}
    return deepcopy(O.basis_mat)
  else
    return O.basis_mat
  end
end

function basis_mat_inv{T}(O::NfOrdRel, copy::Type{Val{T}} = Val{true})
  if copy == Val{true}
    return deepcopy(O.basis_mat_inv)
  else
    return O.basis_mat_inv
  end
end

# discriminant

type NfRelOrdElem{T} <: RingElem
  parent#::NfOrdRel{T, S} # I don't want to drag the S around
  elem_in_nf::NfRelElem{T}
  elem_in_basis::Vector{T}
  has_coord::Bool

  function NfRelOrdElem(O::NfOrdRel{T})
    z = new()
    z.parent = O
    z.elem_in_nf = zero(nf(O))
    z.elem_in_basis = Vector{T}(degree(O))
    z.has_coord = false
    return z
  end

  function NfRelOrdElem(O::NfOrdRel{T}, a::NfRelElem{T})
    z = new()
    z.parent = O
    z.elem_in_nf = a
    z.elem_in_basis = Vector{T}(degree(O))
    z.has_coord = false
    return z
  end
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::NfRelOrdElem)
  print(io, a.elem_in_nf)
end

################################################################################
#
#  Parent object overloading
#
################################################################################

function (O::NfOrdRel){T}(a::NfRelElem{T})
  # checks
  return NfRelOrdElem{T}(O, deepcopy(a))
end

(O::NfOrdRel)(a::Union{fmpz, Integer}) = O(nf(O)(a))

(O::NfOrdRel)() = O(nf(O)(0))

################################################################################
#
#  Trace
#
################################################################################

trace(a::NfRelOrdElem) = trace(a.elem_in_nf)

################################################################################
#
#  Special elements
#
################################################################################

one(O::NfOrdRel) = O(1)

zero(O::NfOrdRel) = O(0)

one(a::NfRelOrdElem) = parent(a)(1)

zero(a::NfRelOrdElem) = parent(a)(0)

################################################################################
#
#  isone/iszero
#
################################################################################

isone(a::NfRelOrdElem) = isone(a.elem_in_nf)

iszero(a::NfRelOrdElem) = iszero(a.elem_in_nf)

################################################################################
#
#  Unary operations
#
################################################################################

function -(a::NfRelOrdElem)
  b = parent(a)()
  b.elem_in_nf = - a.elem_in_nf
  if a.has_coord
    b.elem_in_basis = map(x -> -x, a.elem_in_basis)
    b.has_coord = true
  end
  return b
end

################################################################################
#
#  Binary operations
#
################################################################################

function *(a::NfRelOrdElem, b::NfRelOrdElem)
  parent(a) != parent(b) && error("Parents don't match.")
  c = parent(a)()
  c.elem_in_nf = a.elem_in_nf*b.elem_in_nf
  return c
end

function +(a::NfRelOrdElem, b::NfRelOrdElem)
  parent(a) != parent(b) && error("Parents don't match.")
  c = parent(a)()
  c.elem_in_nf = a.elem_in_nf + b.elem_in_nf
  if a.has_coord && b.has_coord
    c.elem_in_basis = [ a.elem_in_basis[i] + b.elem_in_basis[i] for i = 1:degree(parent(a))]
    c.has_coord = true
  end
  return c
end

function -(a::NfRelOrdElem, b::NfRelOrdElem)
  parent(a) != parent(b) && error("Parents don't match.")
  c = parent(a)()
  c.elem_in_nf = a.elem_in_nf - b.elem_in_nf
  if a.has_coord && b.has_coord
    c.elem_in_basis = [ a.elem_in_basis[i] - b.elem_in_basis[i] for i = 1:degree(parent(a))]
    c.has_coord = true
  end
  return c
end

type NfRelOrdIdl{T} end

type NfRelOrdFracIdl{T} end


# in, elem_in_basis

# help inference
parent{T}(x::NfRelOrdElem{NfRelElem{T}}) = x.parent::NfOrdRel{NfRelElem{T}, NfRelOrdFracIdl{T}}

parent(x::NfRelOrdElem{nf_elem}) = x.parent::NfOrdRel{nf_elem, NfOrdFracIdl}
