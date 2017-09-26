# I don't like that we have to drag S around
# Still hoping for julia/#18466

mutable struct NfRelOrdSet{T}
  nf::NfRel{T}

  function NfRelOrdSet{T}(K::NfRel{T}) where {T}
    a = new(K)
    return a
  end
end

mutable struct NfRelOrd{T, S} <: Ring
  nf::NfRel{T}
  basis_nf::Vector{NfRelElem{T}}
  basis_mat::Generic.Mat{T}
  basis_mat_inv::Generic.Mat{T}
  basis_pmat::PMat{T, S}
  pseudo_basis::Vector{Tuple{NfRelElem{T}, S}}

  disc_abs::NfOrdIdl # used if T == nf_elem
  disc_rel#::NfRelOrdIdl{T} # used otherwise; is a forward declaration
  parent::NfRelOrdSet{T}

  function NfRelOrd{T, S}(K::NfRel{T}, M::PMat{T, S}) where {T, S}
    z = new{T, S}()
    z.nf = K
    z.parent = NfRelOrdSet{T}(K)
    z.basis_pmat = M
    z.basis_mat = M.matrix
    return z
  end
  
  function NfRelOrd{T, S}(K::NfRel{T}, M::Generic.Mat{T}) where {T, S}
    z = new{T, S}()
    z.nf = K
    z.parent = NfRelOrdSet{T}(K)
    z.basis_mat = M
    z.basis_pmat = pseudo_matrix(M)
    return z
  end

  function NfRelOrd{T, S}(K::NfRel{T}) where {T, S}
    z = new{T, S}()
    z.nf = K
    z.parent = NfRelOrdSet{T}(K)
    return z
  end
end

################################################################################
#
#  Basic field access
#
################################################################################

doc"""
***
      nf(O::NfRelOrd) -> NfRel

> Returns the ambient number field of $\mathcal O$.
"""
nf(O::NfRelOrd) = O.nf

doc"""
    parent(O::NfRelOrd) -> NfRelOrdSet

Returns the parent of $\mathcal O$, that is, the set of orders of the ambient
number field.
"""
parent(O::NfRelOrd) = O.parent

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_basis_pmat(O::NfRelOrd{T, S}) where {T, S}
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
    elem_to_mat_row!(M, i, pb[i][1])
    push!(C, pb[i][2])
  end
  O.basis_pmat = PseudoMatrix(M, C)
  return nothing
end

function assure_has_pseudo_basis(O::NfRelOrd{T, S}) where {T, S}
  if isdefined(O, :pseudo_basis)
    return nothing
  end
  if !isdefined(O, :basis_pmat)
    error("No pseudo_basis and no basis_pmat defined.")
  end
  P = basis_pmat(O)
  L = nf(O)
  pseudo_basis = Vector{Tuple{NfRelElem{T}, S}}()
  for i = 1:degree(O)
    a = elem_from_mat_row(L, P.matrix, i)
    push!(pseudo_basis, (a, P.coeffs[i]))
  end
  O.pseudo_basis = pseudo_basis
  return nothing
end

function assure_has_basis_nf(O::NfRelOrd{T, S}) where {T, S}
  if isdefined(O, :basis_nf)
    return nothing
  end
  L = nf(O)
  pb = pseudo_basis(O)
  basis_nf = Vector{NfRelElem{T}}()
  for i = 1:degree(O)
    push!(basis_nf, pb[i][1])
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

doc"""
***
      pseudo_basis(O::NfRelOrd{T, S}) -> Vector{Tuple{NfRelElem{T}, S}}

> Returns the pseudo-basis of $\mathcal O$.
"""
function pseudo_basis(O::NfRelOrd, copy::Type{Val{T}} = Val{true}) where T
  assure_has_pseudo_basis(O)
  if copy == Val{true}
    return deepcopy(O.pseudo_basis)
  else
    return O.pseudo_basis
  end
end

doc"""
***
      basis_pmat(O::NfRelOrd) -> PMat

> Returns the basis pseudo-matrix of $\mathcal O$ with respect to the power basis
> of the ambient number field.
"""
function basis_pmat(O::NfRelOrd, copy::Type{Val{T}} = Val{true}) where T
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

doc"""
***
      basis_nf(O::NfRelOrd) -> Array{NfRelElem, 1}

> Returns the elements of the pseudo-basis of $\mathcal O$ as elements of the
> ambient number field.
"""
function basis_nf(O::NfRelOrd, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_nf(O)
  if copy == Val{true}
    return deepcopy(O.basis_nf)
  else
    return O.basis_nf
  end
end

doc"""
***
      basis_mat(O::NfRelOrd{T, S}) -> Generic.Mat{T}

> Returns the basis matrix of $\mathcal O$ with respect to the power basis
> of the ambient number field.
"""
function basis_mat(O::NfRelOrd, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_mat(O)
  if copy == Val{true}
    return deepcopy(O.basis_mat)
  else
    return O.basis_mat
  end
end

doc"""
***
      basis_mat_inv(O::NfRelOrd{T, S}) -> Generic.Mat{T}

> Returns the inverse of the basis matrix of $\mathcal O$.
"""
function basis_mat_inv(O::NfRelOrd, copy::Type{Val{T}} = Val{true}) where T
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

function show(io::IO, S::NfRelOrdSet)
  print(io, "Set of orders of the number field ")
  print(io, S.nf)
end

function show(io::IO, O::NfRelOrd)
  print(io, "Relative order of ")
  println(io, nf(O))
  print(io, "with pseudo-basis ")
  pb = pseudo_basis(O)
  for i = 1:degree(O)
    print(io, "\n")
    print(io, pb[i])
  end
end

################################################################################
#
#  Discriminant
#
################################################################################

function assure_has_discriminant(O::NfRelOrd{nf_elem, S}) where S
  if isdefined(O, :disc_abs)
    return nothing
  end
  d = det(trace_matrix(O))
  pb = pseudo_basis(O, Val{false})
  a = pb[1][2]^2
  for i = 2:degree(O)
    a *= pb[i][2]^2
  end
  disc = d*a
  simplify_exact!(disc)
  O.disc_abs = num(disc)
  return nothing
end

function discriminant(O::NfRelOrd{nf_elem, S}) where S
  assure_has_discriminant(O)
  return deepcopy(O.disc_abs)
end

function assure_has_discriminant(O::NfRelOrd{NfRelElem{T}, S}) where {T, S}
  if isdefined(O, :disc_rel)
    return nothing
  end
  d = det(trace_matrix(O))
  pb = pseudo_basis(O, Val{false})
  a = pb[1][2]^2
  for i = 2:degree(O)
    a *= pb[i][2]^2
  end
  disc = d*a
  simplify_exact!(disc)
  O.disc_rel = num(disc)
  return nothing
end

function discriminant(O::NfRelOrd{NfRelElem{T}, S}) where {T, S}
  assure_has_discriminant(O)
  return deepcopy(O.disc_rel)
end

################################################################################
#
#  Degree
#
################################################################################

doc"""
***
      degree(O::NfRelOrd) -> Int

> Returns the degree of $\mathcal O$.
"""
degree(O::NfRelOrd) = degree(nf(O))

################################################################################
#
#  Deepcopy
#
################################################################################

doc"""
***
      deepcopy(O::NfRelOrd) -> NfRelOrd

> Makes a copy of $\mathcal O$.
"""
function Base.deepcopy_internal(O::NfRelOrd{T, S}, dict::ObjectIdDict) where {T, S}
  z = NfRelOrd{T, S}(O.nf)
  for x in fieldnames(O)
    if x != :nf && x != :parent && isdefined(O, x)
      setfield!(z, x, Base.deepcopy_internal(getfield(O, x), dict))
    end
  end
  z.nf = O.nf
  z.parent = O.parent
  return z
end

################################################################################
#
#  Inclusion of number field elements
#
################################################################################

function _check_elem_in_order(a::NfRelElem{T}, O::NfRelOrd{T, S}, short::Type{Val{V}} = Val{false}) where {T, S, V}
  assure_has_basis_mat_inv(O)
  assure_has_basis_pmat(O)
  t = MatrixSpace(base_ring(nf(O)), 1, degree(O))()
  elem_to_mat_row!(t, 1, a)
  t = t*O.basis_mat_inv
  if short == Val{true}
    for i = 1:degree(O)
      if !(t[1, i] in O.basis_pmat.coeffs[i])
        return false
      end
    end
    return true
  else
    for i = 1:degree(O)
      if !(t[1, i] in O.basis_pmat.coeffs[i])
        return false, Vector{T}()
      end
    end
    v = Vector{T}(degree(O))
    for i in 1:degree(O)
      v[i] = deepcopy(t[1, i])
    end
    return true, v
  end
end

doc"""
***
      in(a::NfRelElem, O::NfRelOrd) -> Bool

> Checks whether $a$ lies in $\mathcal O$.
"""
function in(a::NfRelElem{T}, O::NfRelOrd{T, S}) where {T, S}
  return _check_elem_in_order(a, O, Val{true})
end

################################################################################
#
#  Construction
#
################################################################################

doc"""
***
      Order(K::NfRel{T}, M::Generic.Mat{T}) -> NfRelOrd

> Returns the order which has basis matrix $M$ with respect to the power basis
> of $K$.
"""
function Order(L::NfRel{nf_elem}, M::Generic.Mat{nf_elem})
  # checks
  return NfRelOrd{nf_elem, NfOrdFracIdl}(L, deepcopy(M))
end

function Order(L::NfRel{NfRelElem{T}}, M::Generic.Mat{NfRelElem{T}}) where T
  # checks
  return NfRelOrd{NfRelElem{T}, NfRelOrdFracIdl{T}}(L, deepcopy(M))
end

doc"""
***
      Order(K::NfRel, M::PMat) -> NfRelOrd

> Returns the order which has basis pseudo-matrix $M$ with respect to the power basis
> of $K$.
"""
function Order(L::NfRel{T}, M::PMat{T, S}) where {T, S}
  # checks
  return NfRelOrd{T, S}(L, deepcopy(M))
end

function EquationOrder(L::NfRel{T}) where T
  M = one(MatrixSpace(base_ring(L), degree(L), degree(L)))
  return Order(L, M)
end

function MaximalOrder(L::NfRel)
  O = EquationOrder(L)
  return MaximalOrder(O)
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

################################################################################
#
#  Trace matrix
#
################################################################################

function trace_matrix(O::NfRelOrd)
  L = nf(O)
  K = base_ring(L)
  b = basis_nf(O, Val{false})
  d = degree(L)
  g = MatrixSpace(K, d, d)()
  for i = 1:d
    t = trace(b[i]*b[i])
    g[i, i] = t
    for j = (i + 1):d
      t = trace(b[i]*b[j])
      g[i, j] = t
      g[j, i] = t
    end
  end
  return g
end

################################################################################
#
#  p-maximal overorder
#
################################################################################

function pmaximal_overorder(O::NfRelOrd, p::NfOrdIdl)
  d = discriminant(O)
  OO = ring_of_multipliers(pradical(O, p))
  dd = discriminant(OO)
  while d != dd
    d = dd
    OO = ring_of_multipliers(pradical(OO, p))
    dd = discriminant(OO)
  end
  return OO
end

function MaximalOrder(O::NfRelOrd)
  disc = discriminant(O)
  fac = factor(disc)
  OO = deepcopy(O)
  for (p, e) in fac
    if e == 1
      continue
    end
    OO += pmaximal_overorder(O, p)
  end
  return OO
end

################################################################################
#
#  Addition of orders
#
################################################################################

function +(a::NfRelOrd{T, S}, b::NfRelOrd{T, S}) where {T, S}
  @assert parent(a) != parent(b)
  aB = basis_pmat(a)
  bB = basis_pmat(b)
  d = degree(a)
  PM = try sub(pseudo_hnf(vcat(aB, bB), :lowerleft), d + 1:2*d, 1:d)
    catch sub(pseudo_hnf_kb(vcat(aB, bB), :lowerleft), d + 1:2*d, 1:d)
    end
  return NfRelOrd{T, S}(nf(a), PM)
end
