elem_type(::Type{T}) where {T <: AssociativeAlgebraLattice} =
  AssociativeAlgebraLatticeElem{T, elem_type(_underlying_module_type(T)), elem_type(algebra_type(T))}

parent_type(::Type{AssociativeAlgebraLatticeElem{S, T, U}}) where {S, T, U} = S

parent(x::AssociativeAlgebraLatticeElem) = x.parent

################################################################################
#
#  Construction
#
################################################################################

@doc raw"""
    (L::AssociativeAlgebraLattice)(a::AbstractAssociativeAlgebraElem; check::Bool = true)

Construct an element of `L` from an element of its ambient algebra. If `check`
is `true`, check that `a` belongs to `L`.
"""
function (L::AssociativeAlgebraLattice)(a::AbstractAssociativeAlgebraElem; check::Bool = true)
  @req parent(a) === algebra(L) "The element and lattice have different ambient algebras"
  m = _element_from_ambient_coordinates(underlying_module(L), coefficients(a; copy = true); check)
  return AssociativeAlgebraLatticeElem(L, m)
end

@doc raw"""
    (L::AssociativeAlgebraLattice)(v::Vector; check::Bool = true)

Construct an element of `L` from its basis coordinates. Over a PID, coordinates
lie in `base_ring(L)`. Over a Dedekind domain, they lie in the fraction field
and, if `check` is `true`, must belong to the respective pseudo-basis coefficient
ideals. The length of `v` must equal `rank(L)`.
"""
function (L::AssociativeAlgebraLattice)(v::Vector; check::Bool = true)
  M = underlying_module(L)
  @req length(v) == rank(M) "The coordinates have the wrong length"
  C = _coordinate_ring(M)
  c = deepcopy(elem_type(C)[C(a) for a in v])
  return AssociativeAlgebraLatticeElem(L, _element_from_coordinates(M, c; check))
end

function (L::AssociativeAlgebraLattice)(m::EmbeddedModuleElem; check::Bool = true)
  @req parent(m) === underlying_module(L) "The element belongs to a different embedded module"
  n = _element_from_ambient_coordinates(underlying_module(L), ambient_coordinates(m); check)
  return AssociativeAlgebraLatticeElem(L, n)
end

function (L::AssociativeAlgebraLattice)(x::AssociativeAlgebraLatticeElem; check::Bool = true)
  return L(elem_in_algebra(x); check)
end

(L::AssociativeAlgebraLattice)() = zero(L)

zero(L::AssociativeAlgebraLattice) = L(zero(algebra(L)); check = false)

zero(x::AssociativeAlgebraLatticeElem) = zero(parent(x))

################################################################################
#
#  Representations
#
################################################################################

@doc raw"""
    elem_in_module(x::AssociativeAlgebraLatticeElem)

Return the stored element of the embedded module underlying the parent lattice
of `x`.
"""
function elem_in_module(x::AssociativeAlgebraLatticeElem)
  return x.elem_in_module
end

@doc raw"""
    elem_in_algebra(x::AssociativeAlgebraLatticeElem)

Return the stored element of the ambient algebra, computed on first use.
"""
function elem_in_algebra(x::AssociativeAlgebraLatticeElem)
  if !isdefined(x, :elem_in_algebra)
    x.elem_in_algebra = algebra(parent(x))(ambient_coordinates(elem_in_module(x)); copy = false)
  end
  return x.elem_in_algebra
end

@doc raw"""
    coordinates(x::AssociativeAlgebraLatticeElem; copy::Bool = true)

Return the basis coordinates of `x`. Over a Dedekind domain these are fraction
field elements in the respective pseudo-basis coefficient ideals.
"""
coordinates(x::AssociativeAlgebraLatticeElem; copy::Bool = true) =
  coordinates(x.elem_in_module; copy)

ambient_coordinates(x::AssociativeAlgebraLatticeElem; copy::Bool = true) =
  ambient_coordinates(x.elem_in_module; copy)

################################################################################
#
#  Module arithmetic
#
################################################################################

function +(x::AssociativeAlgebraLatticeElem, y::AssociativeAlgebraLatticeElem)
  @req parent(x) === parent(y) "The elements have different parent lattices"
  return parent(x)(coordinates(x; copy = false) + coordinates(y; copy = false); check = false)
end

function -(x::AssociativeAlgebraLatticeElem, y::AssociativeAlgebraLatticeElem)
  @req parent(x) === parent(y) "The elements have different parent lattices"
  return parent(x)(coordinates(x; copy = false) - coordinates(y; copy = false); check = false)
end

-(x::AssociativeAlgebraLatticeElem) = parent(x)(-coordinates(x; copy = false); check = false)

function *(a::IntegerUnion, x::AssociativeAlgebraLatticeElem)
  return _scale_lattice_element(base_ring(parent(x))(a), x)
end

*(a::RingElem, x::AssociativeAlgebraLatticeElem) = _scale_lattice_element(a, x)

function _scale_lattice_element(a::RingElem, x::AssociativeAlgebraLatticeElem)
  L = parent(x)
  @req parent(a) === base_ring(L) "The scalar does not belong to the coefficient ring"
  M = underlying_module(L)
  C = _coordinate_ring(M)
  c = C === ring(M) ? a : image(fraction_map(M), a)
  return L(elem_type(C)[c * b for b in coordinates(x; copy = false)]; check = false)
end

*(x::AssociativeAlgebraLatticeElem, a::Union{IntegerUnion, RingElem}) = a * x

iszero(x::AssociativeAlgebraLatticeElem) = all(iszero, coordinates(x; copy = false))

################################################################################
#
#  Equality, copying and printing
#
################################################################################

function ==(x::AssociativeAlgebraLatticeElem, y::AssociativeAlgebraLatticeElem)
  return parent(x) === parent(y) && coordinates(x; copy = false) == coordinates(y; copy = false)
end

function Base.hash(x::AssociativeAlgebraLatticeElem, h::UInt)
  return hash(coordinates(x; copy = false), hash(objectid(parent(x)), h))
end

function Base.deepcopy_internal(x::AssociativeAlgebraLatticeElem, dict::IdDict)
  haskey(dict, x) && return dict[x]
  y = AssociativeAlgebraLatticeElem(parent(x), Base.deepcopy_internal(x.elem_in_module, dict))
  dict[x] = y
  if isdefined(x, :elem_in_algebra)
    y.elem_in_algebra = Base.deepcopy_internal(x.elem_in_algebra, dict)
  end
  return y
end

Base.copy(x::AssociativeAlgebraLatticeElem) = deepcopy(x)

show(io::IO, x::AssociativeAlgebraLatticeElem) = show(io, elem_in_algebra(x))
