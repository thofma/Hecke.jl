mutable struct NfRelOrdIdlSet{T, S}
  order::NfRelOrd{T, S}

  function NfRelOrdIdlSet{T, S}(O::NfRelOrd{T, S}) where {T, S}
    a = new(O)
    return a
  end
end

mutable struct NfRelOrdIdl{T, S}
  order::NfRelOrd{T, S}
  parent::NfRelOrdIdlSet{T, S}
  basis_pmat::PMat{T, S}
  pseudo_basis::Vector{Tuple{NfRelElem{T}, S}}
  basis_mat::GenMat{T}
  basis_mat_inv::GenMat{T}

  norm
  has_norm::Bool

  function NfRelOrdIdl{T, S}(O::NfRelOrd{T, S}) where {T, S}
    z = new{T, S}()
    z.order = O
    z.parent = NfRelOrdIdlSet{T, S}(O)
    z.has_norm = false
    return z
  end

  function NfRelOrdIdl{T, S}(O::NfRelOrd{T, S}, M::PMat{T, S}) where {T, S}
    z = new{T, S}()
    z.order = O
    z.parent = NfRelOrdIdlSet{T, S}(O)
    z.basis_pmat = M
    z.basis_mat = M.matrix
    z.has_norm = false
    return z
  end

  function NfRelOrdIdl{T, S}(O::NfRelOrd{T, S}, M::GenMat{T}) where {T, S}
    z = new{T, S}()
    z.order = O
    z.parent = NfRelOrdIdlSet{T, S}(O)
    z.basis_pmat = pseudo_matrix(M)
    z.basis_mat = M
    z.has_norm = false
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
    order(a::NfRelOrdIdl) -> NfRelOrd

> Returns the order of $a$.
"""
order(a::NfRelOrdIdl) = a.order

doc"""
***
    nf(a::NfRelOrdIdl) -> NfRel

> Returns the number field, of which $a$ is an integral ideal.
"""
nf(a::NfRelOrdIdl) = nf(order(a))

################################################################################
#
#  Parent
#
################################################################################

parent(a::NfRelOrdIdl) = a.parent

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

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
    elem_to_mat_row!(M, i, pb[i][1])
    push!(C, pb[i][2])
  end
  a.basis_pmat = pseudo_hnf(PseudoMatrix(M, C), :lowerleft)
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
  K = base_ring(L)
  pseudo_basis = Vector{Tuple{NfRelElem{T}, S}}()
  for i = 1:degree(L)
    x = elem_from_mat_row(L, P.matrix, i)
    push!(pseudo_basis, (x, P.coeffs[i]))
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

################################################################################
#
#  Pseudo basis / basis pseudo-matrix
#
################################################################################

doc"""
***
      pseudo_basis(a::NfRelOrdIdl{T, S}) -> Vector{Tuple{NfRelElem{T}, S}}

> Returns the pseudo-basis of $a$.
"""
function pseudo_basis(a::NfRelOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_pseudo_basis(a)
  if copy == Val{true}
    return deepcopy(a.pseudo_basis)
  else
    return a.pseudo_basis
  end
end

doc"""
***
      basis_pmat(a::NfRelOrdIdl) -> PMat

> Returns the basis pseudo-matrix of $a$.
"""
function basis_pmat(a::NfRelOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_pmat(a)
  if copy == Val{true}
    return deepcopy(a.basis_pmat)
  else
    return a.basis_pmat
  end
end

################################################################################
#
#  Basis / (inverse) basis matrix
#
################################################################################

doc"""
***
      basis_mat(a::NfRelOrdIdl{T, S}) -> GenMat{T}

> Returns the basis matrix of $a$.
"""
function basis_mat(a::NfRelOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_mat(a)
  if copy == Val{true}
    return deepcopy(a.basis_mat)
  else
    return a.basis_mat
  end
end

doc"""
***
      basis_mat_inv(a::NfRelOrdIdl{T, S}) -> GenMat{T}

> Returns the inverse of the basis matrix of $a$.
"""
function basis_mat_inv(a::NfRelOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_mat_inv(a)
  if copy == Val{true}
    return deepcopy(a.basis_mat_inv)
  else
    return a.basis_mat_inv
  end
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, s::NfRelOrdIdlSet)
  print(io, "Set of ideals of ")
  print(io, s.order)
end

function show(io::IO, a::NfRelOrdIdl)
  print(io, "Ideal of (")
  print(io, order(a), ")\n")
  print(io, "with basis pseudo-matrix\n")
  print(io, basis_pmat(a))
end

################################################################################
#
#  Parent object overloading and user friendly constructors
#
################################################################################

doc"""
***
    ideal(O::NfRelOrd, M::PMat) -> NfRelOrdIdl

> Creates the ideal of $\mathcal O$ with basis pseudo-matrix $M$.
"""
function ideal(O::NfRelOrd{T, S}, M::PMat{T, S}) where {T, S}
  # checks
  H = pseudo_hnf(M, :lowerleft)
  return NfRelOrdIdl{T, S}(O, H)
end

doc"""
***
    ideal(O::NfRelOrd, M::GenMat) -> NfRelOrdIdl

> Creates the ideal of $\mathcal O$ with basis matrix $M$.
"""
ideal(O::NfRelOrd{T, S}, M::GenMat{T}) where {T, S} = ideal(O, PseudoMatrix(M))

################################################################################
#
#  Deepcopy
#
################################################################################

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

################################################################################
#
#  Equality
#
################################################################################

doc"""
***
    ==(a::NfRelOrdIdl, b::NfRelOrdIdl) -> Bool

> Returns whether $a$ and $b$ are equal.
"""
function ==(a::NfRelOrdIdl, b::NfRelOrdIdl)
  order(a) != order(b) && return false
  return basis_pmat(a) == basis_pmat(b)
end

################################################################################
#
#  Norm
#
################################################################################

function assure_has_norm(a::NfRelOrdIdl)
  if a.has_norm
    return nothing
  end
  c = basis_pmat(a).coeffs
  d = basis_pmat(order(a)).coeffs
  n = c[1]*inv(d[1])
  for i = 2:degree(order(a))
    n *= c[i]*inv(d[i])
  end
  simplify(n)
  @assert n.den == 1
  a.norm = n.num
  a.has_norm = true
  return nothing
end

doc"""
***
    norm(a::NfRelOrdIdl) -> NfOrdIdl

> Returns the norm of $a$.
"""
function norm(a::NfRelOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_norm(a)
  if copy == Val{true}
    return deepcopy(a.norm)
  else
    return a.norm
  end
end

################################################################################
#
#  Ideal addition / GCD
#
################################################################################

doc"""
***
    +(a::NfRelOrdIdl, b::NfRelOrdIdl) -> NfRelOrdIdl

> Returns $a + b$.
"""
function +(a::NfRelOrdIdl{T, S}, b::NfRelOrdIdl{T, S}) where {T, S}
  d = degree(order(a))
  H = vcat(basis_pmat(a), basis_pmat(b))
  m = norm(a) + norm(b)
  H = sub(pseudo_hnf_mod(H, m, :lowerleft), (d + 1):2*d, 1:d)
  return NfRelOrdIdl{T, S}(order(a), H)
end

################################################################################
#
#  Ideal multiplication
#
################################################################################

doc"""
    *(a::NfRelOrdIdl, b::NfRelOrdIdl)

> Returns $a \cdot b$.
"""
function *(a::NfRelOrdIdl{T, S}, b::NfRelOrdIdl{T, S}) where {T, S}
  pba = pseudo_basis(a, Val{false})
  pbb = pseudo_basis(b, Val{false})
  L = nf(order(a))
  K = base_ring(L)
  d = degree(order(a))
  M = MatrixSpace(K, d^2, d)()
  C = Array{S, 1}(d^2)
  t = L()
  for i = 1:d
    for j = 1:d
      mul!(t, pba[i][1], pbb[i][1])
      elem_to_mat_row!(M, (i - 1)*d + j, t)
      C[(i - 1)*d + j] = pba[i][2]*pbb[i][2]
    end
  end
  m = norm(a)*norm(b)
  H = sub(pseudo_hnf_mod(PseudoMatrix(M, C), m, :lowerleft), (d*(d - 1) + 1):d^2, 1:d)
  return NfRelOrdIdl{T, S}(order(a), H)
end

################################################################################
#
#  Ad hoc multiplication
#
################################################################################

doc"""
***
    *(a:NfRelOrdIdl{T, S}, x::T) -> NfRelOrdIdl{T, S}

> Returns the ideal $x\cdot a$.
"""
function *(a::NfRelOrdIdl{T, S}, x::T) where {T, S}
  bp = basis_pmat(a)
  P = PseudoMatrix(bp.matrix, x.*bp.coeffs)
  return NfRelOrdIdl{T, S}(order(a), P)
end

*(x::T, a::NfRelOrdIdl{T, S}) where {T, S} = a*x

################################################################################
#
#  Intersection / LCM
#
################################################################################

doc"""
    intersection(a::NfRelOrdIdl, b::NfRelOrdIdl) -> NfRelOrdIdl

> Returns $a \cap b$.
"""
function intersection(a::NfRelOrdIdl{T, S}, b::NfRelOrdIdl{T, S}) where {T, S}
  d = degree(order(a))
  Ma = basis_pmat(a)
  Mb = basis_pmat(b)
  M1 = hcat(Ma, deepcopy(Ma))
  z = zero(MatrixSpace(base_ring(Ma.matrix), d, d))
  M2 = hcat(PseudoMatrix(z, Mb.coeffs), Mb)
  M = vcat(M1, M2)
  m = intersection(norm(a), norm(b))
  H = sub(pseudo_hnf_mod(M, m, :lowerleft), 1:d, 1:d)
  return NfRelOrdIdl{T, S}(order(a), H)
end
