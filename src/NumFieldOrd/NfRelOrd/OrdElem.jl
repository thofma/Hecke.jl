parent_type(::NfRelOrdElem{T, U}) where {T, U} = NfRelOrd{T, fractional_ideal_type(order_type(parent_type(T))), U}
parent_type(::Type{NfRelOrdElem{T, U}}) where {T, U} = NfRelOrd{T, fractional_ideal_type(order_type(parent_type(T))), U}

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(x::NfRelOrdElem, dict::IdDict)
  z = parent(x)()
  z.elem_in_nf = Base.deepcopy_internal(x.elem_in_nf, dict)
  if x.has_coord
    z.has_coord = true
    z.coordinates = Base.deepcopy_internal(x.coordinates, dict)
  end
  return z
end

################################################################################
#
#  Parent object overloading
#
################################################################################
#=
@doc Markdown.doc"""
      (O::NfRelOrd)(a::NumFieldElem, check::Bool = true) -> NfRelOrdElem

Given an element $a$ of the ambient number field of $\mathcal O$, this
function coerces the element into $\mathcal O$. If `check` is `true`
it will be checked that $a$ is contained in $\mathcal O$.
"""
=#
function (O::NfRelOrd{S, T, U})(a::U, check::Bool = true) where {S, T, U}
  if check
    x, y = _check_elem_in_order(a, O)
    !x && error("Number field element not in the order.")
    return NfRelOrdElem{S, U}(O, deepcopy(a), y)
  else
    return NfRelOrdElem{S, U}(O, deepcopy(a))
  end
end

#=
@doc Markdown.doc"""
      (O::NfRelOrd)(a::NfRelOrdElem, check::Bool = true) -> NfRelOrdElem

Given an element $a$ of some order in the ambient number field of
$\mathcal O$, this function coerces the element into $\mathcal O$.
If `check` is `true` it will be checked that $a$ is contained in
$\mathcal O$.
"""
=#
(O::NfRelOrd{S, T, U})(a::NfRelOrdElem{S, U}, check::Bool = true) where {S, T, U} = O(nf(O)(a.elem_in_nf), check)

function (O::NfRelOrd)(a::Vector{T}, check::Bool = true) where T
  t = nf(O)()
  basis = basis_nf(O, copy = false)
  for i = 1:degree(O)
    t += a[i]*basis[i]
  end
  s = O(t, check)
  s.coordinates = a
  s.has_coord = true
  return s
end

(O::NfRelOrd)(a::NfOrdElem, check::Bool = true) = O(nf(O)(a.elem_in_nf), check)

(O::NfRelOrd)(a::IntegerUnion) = O(nf(O)(a))

#=
@doc Markdown.doc"""
      (O::NfRelOrd)() -> NfRelOrdElem

Constructs a new element of $\mathcal O$ which is set to $0$.
"""
=#
(O::NfRelOrd{T, S, U})() where {T, S, U} = NfRelOrdElem{T, U}(O)

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_coord(a::NfRelOrdElem)
  if a.has_coord
    return nothing
  else
    x, y = _check_elem_in_order(a.elem_in_nf, parent(a))
    !x && error("Not a valid order element.")
    a.coordinates = y
    a.has_coord = true
    return nothing
  end
end

################################################################################
#
#  Coordinates
#
################################################################################

@doc Markdown.doc"""
      coordinates(a::NfRelOrdElem{T}) -> Vector{T}

Returns the coefficient vector of $a$.
"""
function coordinates(a::NfRelOrdElem; copy::Bool = true)
  assure_has_coord(a)
  if copy
    return deepcopy(a.coordinates)
  else
    return a.coordinates
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
#  Relative Norm and Trace
#
################################################################################

norm(a::NfRelOrdElem, k::Union{NumField, FlintRationalField }) = base_ring(parent(a))(norm(a.elem_in_nf, k))
tr(a::NfRelOrdElem, k::Union{NumField, FlintRationalField }) = base_ring(parent(a))(tr(a.elem_in_nf, k))

################################################################################
#
#  Conversion
#
################################################################################

(K::NfRel)(a::NfRelOrdElem) = elem_in_nf(a)

(K::NfRelNS)(a::NfRelOrdElem) = elem_in_nf(a)

################################################################################
#
#  Representation matrix
#
################################################################################

function representation_matrix(a::NfRelOrdElem)
  O = parent(a)
  A = representation_matrix(elem_in_nf(a))
  A = basis_matrix(O, copy = false)*A*basis_mat_inv(O, copy = false)
  return A
end
