parent_type(::Type{RelNumFieldOrderElem{T, U}}) where {T, U} = RelNumFieldOrder{T, fractional_ideal_type(order_type(parent_type(T))), U}

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(x::RelNumFieldOrderElem, dict::IdDict)
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
@doc raw"""
      (O::RelNumFieldOrder)(a::NumFieldElem, check::Bool = true) -> RelNumFieldOrderElem

Given an element $a$ of the ambient number field of $\mathcal O$, this
function coerces the element into $\mathcal O$. If `check` is `true`
it will be checked that $a$ is contained in $\mathcal O$.
"""
=#
function (O::RelNumFieldOrder{S, T, U})(a::U, check::Bool = true) where {S, T, U}
  if check
    x, y = _check_elem_in_order(a, O)
    !x && error("Number field element not in the order.")
    return RelNumFieldOrderElem{S, U}(O, deepcopy(a), y)
  else
    return RelNumFieldOrderElem{S, U}(O, deepcopy(a))
  end
end

#=
@doc raw"""
      (O::RelNumFieldOrder)(a::RelNumFieldOrderElem, check::Bool = true) -> RelNumFieldOrderElem

Given an element $a$ of some order in the ambient number field of
$\mathcal O$, this function coerces the element into $\mathcal O$.
If `check` is `true` it will be checked that $a$ is contained in
$\mathcal O$.
"""
=#
(O::RelNumFieldOrder{S, T, U})(a::RelNumFieldOrderElem{S, U}, check::Bool = true) where {S, T, U} = O(nf(O)(a.elem_in_nf), check)

function (O::RelNumFieldOrder)(a::Vector{T}, check::Bool = true) where T
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

(O::RelNumFieldOrder)(a::AbsSimpleNumFieldOrderElem, check::Bool = true) = O(nf(O)(a.elem_in_nf), check)

(O::RelNumFieldOrder)(a::IntegerUnion) = O(nf(O)(a))

#=
@doc raw"""
      (O::RelNumFieldOrder)() -> RelNumFieldOrderElem

Constructs a new element of $\mathcal O$ which is set to $0$.
"""
=#
(O::RelNumFieldOrder{T, S, U})() where {T, S, U} = RelNumFieldOrderElem{T, U}(O)

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_coord(a::RelNumFieldOrderElem)
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

@doc raw"""
      coordinates(a::RelNumFieldOrderElem{T}) -> Vector{T}

Returns the coefficient vector of $a$.
"""
function coordinates(a::RelNumFieldOrderElem; copy::Bool = true)
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

function show(io::IO, a::RelNumFieldOrderElem)
  print(io, a.elem_in_nf)
end

################################################################################
#
#  Relative Norm and Trace
#
################################################################################

norm(a::RelNumFieldOrderElem, k::Union{NumField, QQField }) = base_ring(parent(a))(norm(a.elem_in_nf, k))
tr(a::RelNumFieldOrderElem, k::Union{NumField, QQField }) = base_ring(parent(a))(tr(a.elem_in_nf, k))

################################################################################
#
#  Conversion
#
################################################################################

(K::RelSimpleNumField)(a::RelNumFieldOrderElem) = elem_in_nf(a)

(K::RelNonSimpleNumField)(a::RelNumFieldOrderElem) = elem_in_nf(a)

################################################################################
#
#  Representation matrix
#
################################################################################

function representation_matrix(a::RelNumFieldOrderElem)
  O = parent(a)
  A = representation_matrix(elem_in_nf(a))
  A = basis_matrix(O, copy = false)*A*basis_mat_inv(O, copy = false)
  return A
end
