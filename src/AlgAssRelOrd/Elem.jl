# for arithmetic etc. see AlgAssAbsOrd/Elem.jl

parent_type(::Type{AlgAssRelOrdElem{S, T, U}}) where {S, T, U} = AlgAssRelOrd{S, T, U}

@doc raw"""
    parent(x::AlgAssRelOrdElem) -> AlgAssRelOrd

Returns the order containing $x$.
"""
@inline parent(x::AlgAssRelOrdElem) = x.parent

################################################################################
#
#  Parent check
#
################################################################################

function check_parent(x::AlgAssRelOrdElem{S, T, U}, y::AlgAssRelOrdElem{S, T, U}) where {S, T, U}
  return parent(x) === parent(y)
end

################################################################################
#
#  Parent object overloading
#
################################################################################

(O::AlgAssRelOrd{S, T, U})(a::AbstractAssociativeAlgebraElem{S}, check::Bool = true) where {S, T, U} = begin
  if check
    (x, y) = _check_elem_in_order(a, O)
    !x && error("Algebra element not in the order")
    return AlgAssRelOrdElem{S, T, U}(O, deepcopy(a), y)
  else
    return AlgAssRelOrdElem{S, T, U}(O, deepcopy(a))
  end
end

(O::AlgAssRelOrd{S, T, U})(a::AbstractAssociativeAlgebraElem{S}, arr::Vector{S}, check::Bool = false) where {S, T, U} = begin
  if check
    (x, y) = _check_elem_in_order(a, O)
    (!x || arr != y) && error("Algebra element not in the order")
    return AlgAssRelOrdElem{S, T, U}(O, deepcopy(a), y)
  else
    return AlgAssRelOrdElem{S, T, U}(O, deepcopy(a), deepcopy(arr))
  end
end

(O::AlgAssRelOrd{S, T, U})(arr::Vector{S}, check::Bool = true) where {S, T, U} = begin
  M = basis_matrix(O, copy = false)
  N = matrix(base_ring(algebra(O)), 1, degree(O), arr)
  NM = N*M
  x = elem_from_mat_row(algebra(O), NM, 1)
  return O(x, arr, check)
end

(O::AlgAssRelOrd{S, T, U})(a::AlgAssRelOrdElem{S, T, U}, check::Bool = true) where {S, T, U} = begin
  b = elem_in_algebra(a) # already a copy
  if check
    (x, y) = _check_elem_in_order(b, O)
    !x && error("Algebra element not in the order")
    return AlgAssRelOrdElem{S, T, U}(O, b, y)
  else
    return AlgAssRelOrdElem{S, T, U}(O, b)
  end
end

(O::AlgAssRelOrd)(a::T, check::Bool = true) where T = O(algebra(O)(a), check)

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(a::AlgAssRelOrdElem, dict::IdDict)
  b = parent(a)()
  b.elem_in_algebra = Base.deepcopy_internal(a.elem_in_algebra, dict)
  if a.has_coord
    b.has_coord = true
    b.coordinates = Base.deepcopy_internal(a.coordinates, dict)
  end
  return b
end

################################################################################
#
#  Special elements
#
################################################################################

(O::AlgAssRelOrd{S, T, U})() where {S, T, U} = AlgAssRelOrdElem{S, T, U}(O)

one(O::AlgAssRelOrd) = O(one(algebra(O)))

zero(O::AlgAssRelOrd) = O()

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::AlgAssRelOrdElem)
  print(io, elem_in_algebra(a, copy = false))
end

################################################################################
#
#  Representation matrices
#
################################################################################

@doc raw"""
    representation_matrix(x::AlgAssRelOrdElem, action::Symbol = :left) -> MatElem

Returns a matrix representing multiplication with $x$ with respect to the basis
of `order(x)`.
The multiplication is from the left if `action == :left` and from the right if
`action == :right`.
"""
function representation_matrix(x::AlgAssRelOrdElem, action::Symbol = :left)

  O = parent(x)
  M = basis_matrix(O, copy = false)
  M1 = basis_mat_inv(O, copy = false)

  B = representation_matrix(elem_in_algebra(x, copy = false), action)
  B = M*B
  B = B*M1

  return B
end

################################################################################
#
#  Trace
#
################################################################################

@doc raw"""
    tr(x::AlgAssRelOrdElem{S, T, U}) where { S, T, U } -> S

Returns the trace of $x$.
"""
function tr(x::AlgAssRelOrdElem)
  return tr(elem_in_algebra(x, copy = false))
end

@doc raw"""
    trred(x::AlgAssRelOrdElem{S, T, U}) where { S, T, U } -> S

Returns the reduced trace of $x$.
"""
function trred(x::AlgAssRelOrdElem)
  return trred(elem_in_algebra(x, copy = false))
end

################################################################################
#
#  isone/iszero
#
################################################################################

iszero(a::AlgAssRelOrdElem) = iszero(elem_in_algebra(a, copy = false))

isone(a::AlgAssRelOrdElem) = isone(elem_in_algebra(a, copy = false))

is_unit(a::AlgAssRelOrdElem) = is_unit(norm(a))

################################################################################
#
#  Norm
#
################################################################################

function norm(a::AlgAssRelOrdElem)
  OK = base_ring(parent(a))
  return OK(norm(elem_in_algebra(a, copy = false)))
end

function normred(a::AlgAssRelOrdElem)
  OK = base_ring(parent(a))
  return OK(normred(elem_in_algebra(a, copy = false)))
end
