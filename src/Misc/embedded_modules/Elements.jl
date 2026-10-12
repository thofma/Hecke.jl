element(p::PseudoElement) = p.elem
fractional_ideal(p::PseudoElement) = p.ideal

_pseudo_element(elem, R::Ring) = _pseudo_element(elem, R, _ring_type(R))

function _pseudo_element(elem, R::Ring, ::Type{_PID})
  return PseudoElement(elem, nothing)
end

function _pseudo_element(elem, id)
  return PseudoElement(elem, id)
end

function _pseudo_element(elem, R::Ring, ::Type{_DD})
  return PseudoElement(elem, fractional_ideal(R, one(R)))
end

function Base.:(*)(x::PseudoElement, y::PseudoElement)
  return PseudoElement(x.elem * y.elem, x.ideal === nothing ? nothing : x.ideal * y.ideal)
end

parent(x::EmbeddedModuleElem) = x.mod

elem_type(M::EmbeddedModule{RingTypeType, RingType, OverringType}) where {RingTypeType, RingType, OverringType} = EmbeddedModuleElem{typeof(M), RingType, OverringType}

function Base.deepcopy_internal(x::EmbeddedModuleElem, dict::IdDict)
  haskey(dict, x) && return dict[x]
  y = EmbeddedModuleElem(parent(x))
  dict[x] = y
  isdefined(x, :coords) && (y.coords = Base.deepcopy_internal(x.coords, dict))
  isdefined(x, :ambientcoords) && (y.ambientcoords = Base.deepcopy_internal(x.ambientcoords, dict))
  isdefined(x, :pseudocoords) && (y.pseudocoords = Base.deepcopy_internal(x.pseudocoords, dict))
  return y
end

function _element_from_ambient_coordinates(M::EmbeddedModule{S, T, OverringType}, x::Vector; check::Bool = true) where {S, T, OverringType}
  z = EmbeddedModuleElem(M)
  @assert eltype(x) === elem_type(OverringType)
  @req length(x) == ambient_rank(M) "Wrong number of ambient coordinates"
  z.ambientcoords = x
  if check
    fl, c = _in(x, M, Val(true))
    @req fl "Element not contained in module"
    z.coords = c
  end
  return z
end

function _element_from_coordinates(M::EmbeddedModule{S, RingType, OverringType}, x::MatElem; check::Bool = true) where {S, RingType, OverringType}
  @req nrows(x) == 1 "The coordinate matrix must have one row"
  return _element_from_coordinates(M, x[1, :]; check)
end

function _element_from_coordinates(M::EmbeddedModule{S, RingType, OverringType}, x::Vector; check::Bool = true) where {S, RingType, OverringType}
  z = EmbeddedModuleElem(M)
  @assert eltype(x) === elem_type(RingType)
  @req length(x) == rank(M) "Wrong number of coordinates"
  z.coords = x
  return z
end

function _element(M::EmbeddedModule, x, y; check::Bool = false)
  if x === nothing
    @assert y !== nothing
    return _element_from_ambient_coordinates(M, y; check)
  elseif y === nothing
    return _element_from_coordinates(M, x; check)
  else
    return _element_from_coordinates_and_ambient_coordinates(M, x, y; check)
  end
end

function _element_from_coordinates_and_ambient_coordinates(M::EmbeddedModule{S, RingType, OverringType}, x::Vector, y::Vector; check::Bool = true) where {S, RingType, OverringType}
  z = EmbeddedModuleElem(M)
  @assert eltype(x) === elem_type(RingType)
  @assert eltype(y) === elem_type(OverringType)
  @req length(x) == rank(M) "Wrong number of coordinates"
  @req length(y) == ambient_rank(M) "Wrong number of ambient coordinates"
  z.coords = x
  z.ambientcoords = y
  if check
    fl, c = _in(y, M, Val(true))
    @req fl && c == x "Coordinates do not define the same module element"
  end
  return z
end

function zero(M::EmbeddedModule{S, RingType, OverringType}) where {S, RingType, OverringType}
  return _element_from_ambient_coordinates(M, zeros_array(overring(M), ambient_rank(M)); check = false)
end

function coordinates(x::EmbeddedModuleElem{S, RingType}; copy::Bool = true) where {S, RingType}
  if isdefined(x, :coords)
    r = x.coords::Vector{elem_type(RingType)}
    return copy ? deepcopy(r) : r
  else
    fl, c = _in(x.ambientcoords, x.mod, Val(true))
    !fl && error("internal error: element not in module")
    x.coords = c
    r = x.coords::Vector{elem_type(RingType)}
    return copy ? deepcopy(r) : r
  end
end

function ambient_coordinates(x::EmbeddedModuleElem{<:Any, RingType, OverringType}) where {RingType, OverringType}
  if isdefined(x, :ambientcoords)
    return x.ambientcoords::Vector{elem_type(OverringType)}

  else
    M = parent(x)
    c = elem_type(overring(M))[image(fraction_map(M), a)
                              for a in coordinates(x; copy = false)]
    x.ambientcoords = c * basis_matrix(M)
    return x.ambientcoords::Vector{elem_type(OverringType)}
  end
end

function Base.show(io::IO, x::EmbeddedModuleElem)
  print(io, ambient_coordinates(x))
end

function Base.:(*)(a::Union{Integer, Rational, RingElem}, x::EmbeddedModuleElem)
  M = parent(x)
  r = ring(M)(a)
  c = isdefined(x, :coords) ? r .* x.coords : nothing
  if isdefined(x, :ambientcoords)
    s = image(fraction_map(M), r)
    v = s .* x.ambientcoords
  else
    v = nothing
  end
  return _element(M, c, v)
end

Base.:(*)(x::EmbeddedModuleElem, a::Union{Integer, Rational, RingElem}) = a * x

function Base.:(+)(x::EmbeddedModuleElem, y::EmbeddedModuleElem)
  @req parent(x) === parent(y) "Elements must have the same parent"
  c = if isdefined(x, :coords) && isdefined(y, :coords)
    x.coords + y.coords
  else
    nothing
  end
  v = if isdefined(x, :ambientcoords) && isdefined(y, :ambientcoords)
    x.ambientcoords + y.ambientcoords
  else
    nothing
  end
  if c === nothing && v === nothing
    v = ambient_coordinates(x) + ambient_coordinates(y)
  end
  return _element(parent(x), c, v)
end

Base.:(-)(x::EmbeddedModuleElem) = -1 * x

Base.:(-)(x::EmbeddedModuleElem, y::EmbeddedModuleElem) = x + (-y)

function ==(x::EmbeddedModuleElem, y::EmbeddedModuleElem)
  parent(x) === parent(y) || return false
  if isdefined(x, :coords) && isdefined(y, :coords)
    return x.coords == y.coords
  end
  return ambient_coordinates(x) == ambient_coordinates(y)
end

function Base.iszero(x::EmbeddedModuleElem)
  return all(iszero, isdefined(x, :coords) ? x.coords : x.ambientcoords)
end

function Base.hash(x::EmbeddedModuleElem, h::UInt)
  return hash(ambient_coordinates(x), hash(objectid(parent(x)), h))
end
