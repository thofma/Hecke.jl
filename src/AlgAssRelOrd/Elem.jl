# for arithmetic etc. see AlgAssAbsOrd/Elem.jl

parent_type(::Type{AlgAssRelOrdElem{S, T}}) where {S, T} = AlgAssRelOrd{S, T}

parent_type(::AlgAssRelOrdElem{S, T}) where {S, T} = AlgAssRelOrd{S, T}

@inline parent(x::AlgAssRelOrdElem) = x.parent

################################################################################
#
#  Parent check
#
################################################################################

function check_parent(x::AlgAssRelOrdElem{S, T}, y::AlgAssRelOrdElem{S, T}) where {S, T}
  return parent(x) === parent(y)
end

################################################################################
#
#  Parent object overloading
#
################################################################################

(O::AlgAssRelOrd{S, T})(a::AbsAlgAssElem{S}, check::Bool = true) where {S, T} = begin
  if check
    (x, y) = _check_elem_in_order(a, O)
    !x && error("Algebra element not in the order")
    return AlgAssRelOrdElem{S, T}(O, deepcopy(a), y)
  else
    return AlgAssRelOrdElem{S, T}(O, deepcopy(a))
  end
end

(O::AlgAssRelOrd{S, T})(a::AbsAlgAssElem{S}, arr::Vector{S}, check::Bool = false) where {S, T} = begin
  if check
    (x, y) = _check_elem_in_order(a, O)
    (!x || arr != y) && error("Algebra element not in the order")
    return AlgAssRelOrdElem{S, T}(O, deepcopy(a), y)
  else
    return AlgAssRelOrdElem{S, T}(O, deepcopy(a), deepcopy(arr))
  end
end

(O::AlgAssRelOrd{S, T})(arr::Vector{S}, check::Bool = true) where {S, T} = begin
  M = basis_mat(O, copy = false)
  N = matrix(base_ring(algebra(O)), 1, degree(O), arr)
  NM = N*M
  x = elem_from_mat_row(algebra(O), NM, 1)
  return O(x, arr, check)
end

(O::AlgAssRelOrd{S, T})(a::AlgAssRelOrdElem{S, T}, check::Bool = true) where {S, T} = begin
  b = elem_in_algebra(a) # already a copy
  if check
    (x, y) = _check_elem_in_order(b, O)
    !x && error("Algebra element not in the order")
    return AlgAssRelOrdElem{S, T}(O, b, y)
  else
    return AlgAssRelOrdElem{S, T}(O, b)
  end
end

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

(O::AlgAssRelOrd{S, T})() where {S, T} = AlgAssRelOrdElem{S, T}(O)

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

function representation_matrix(x::AlgAssRelOrdElem, action::Symbol = :left)

  O = parent(x)
  M = basis_mat(O, copy = false)
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

function tr(x::AlgAssRelOrdElem)
  return tr(elem_in_algebra(x, copy = false))
end

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
