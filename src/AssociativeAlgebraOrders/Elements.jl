elem_type(::Type{O}) where {O <: AssociativeAlgebraOrder} =
  AssociativeAlgebraOrderElem{O, elem_type(_lattice_type(O))}

parent_type(::Type{AssociativeAlgebraOrderElem{O, E}}) where {O, E} = O
parent(x::AssociativeAlgebraOrderElem) = x.parent

is_exact_type(::Type{AssociativeAlgebraOrderElem{O, E}}) where {O, E} =
  is_exact_type(elem_type(base_ring_type(algebra_type(O))))

# The algebra type alone need not determine whether the algebra is a domain.
is_domain_type(::Type{<:AssociativeAlgebraOrderElem}) = false

function promote_rule(::Type{T}, ::Type{S}) where {O, E, T <: AssociativeAlgebraOrderElem{O, E}, S <: RingElem}
  return S <: IntegerUnion || S === elem_type(base_ring_type(O)) ? T : Union{}
end

function (O::AssociativeAlgebraOrder)(a::Union{AbstractAssociativeAlgebraElem, Vector, EmbeddedModuleElem};
                                     check::Bool = true)
  return AssociativeAlgebraOrderElem(O, underlying_lattice(O)(a; check))
end

function (O::AssociativeAlgebraOrder)(x::AssociativeAlgebraLatticeElem; check::Bool = true)
  return O(elem_in_algebra(x); check)
end

function (O::AssociativeAlgebraOrder)(x::AssociativeAlgebraOrderElem; check::Bool = true)
  return O(elem_in_algebra(x; copy = false); check)
end

function (O::AssociativeAlgebraOrder)(a::Union{IntegerUnion, RingElem}; check::Bool = true)
  K = base_ring(algebra(O))
  c = a isa RingElem && parent(a) === base_ring(O) ?
      image(fraction_map(underlying_module(O)), a) : K(a)
  return O(algebra(O)(c); check)
end

(O::AssociativeAlgebraOrder)() = zero(O)
zero(O::AssociativeAlgebraOrder) = AssociativeAlgebraOrderElem(O, zero(underlying_lattice(O)))
one(O::AssociativeAlgebraOrder) = O(one(algebra(O)); check = false)
zero(x::AssociativeAlgebraOrderElem) = zero(parent(x))
one(x::AssociativeAlgebraOrderElem) = one(parent(x))

elem_in_lattice(x::AssociativeAlgebraOrderElem) = x.elem_in_lattice
elem_in_module(x::AssociativeAlgebraOrderElem) = elem_in_module(elem_in_lattice(x))

function elem_in_algebra(x::AssociativeAlgebraOrderElem; copy::Bool = true)
  a = elem_in_algebra(elem_in_lattice(x))
  return copy ? Base.copy(a) : a
end

coordinates(x::AssociativeAlgebraOrderElem; copy::Bool = true) =
  coordinates(elem_in_lattice(x); copy)

ambient_coordinates(x::AssociativeAlgebraOrderElem; copy::Bool = true) =
  ambient_coordinates(elem_in_lattice(x); copy)

in(x::AssociativeAlgebraOrderElem, O::AssociativeAlgebraOrder) = elem_in_lattice(x) in O
iszero(x::AssociativeAlgebraOrderElem) = iszero(elem_in_lattice(x))
isone(x::AssociativeAlgebraOrderElem) = isone(elem_in_algebra(x; copy = false))

function ==(x::AssociativeAlgebraOrderElem, y::AssociativeAlgebraOrderElem)
  return parent(x) === parent(y) && elem_in_lattice(x) == elem_in_lattice(y)
end

function hash(x::AssociativeAlgebraOrderElem, h::UInt)
  return hash(elem_in_lattice(x), hash(objectid(parent(x)), h))
end

function deepcopy_internal(x::AssociativeAlgebraOrderElem, dict::IdDict)
  haskey(dict, x) && return dict[x]
  y = AssociativeAlgebraOrderElem(parent(x), deepcopy_internal(elem_in_lattice(x), dict))
  dict[x] = y
  return y
end

show(io::IO, x::AssociativeAlgebraOrderElem) = show(io, elem_in_algebra(x; copy = false))

function ConformanceTests.generate_element(O::AssociativeAlgebraOrder{R, _PID}) where {R}
  return O([rand(base_ring(O), 0:3) for _ in 1:degree(O)])
end
