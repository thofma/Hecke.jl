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
  z.ambientcoords = x
  if check
    fl, c = _in(x, M, Val(true))
    @req fl "Element not contained in module"
    z.coords = c
  end
  return z
end

function _element_from_coordinates(M::EmbeddedModule{S, RingType, OverringType}, x::MatElem; check::Bool = true) where {S, RingType, OverringType}
  return _element_from_coordinates(M, x[1, :]; check)
end

function _element_from_coordinates(M::EmbeddedModule{S, RingType, OverringType}, x::Vector; check::Bool = true) where {S, RingType, OverringType}
  z = EmbeddedModuleElem(M)
  @assert eltype(x) === elem_type(RingType)
  z.coords = x
  return z
end

function _element_from_coordinates_and_ambient_coordinates(M::EmbeddedModule{S, RingType, OverringType}, x::Vector, y::Vector; check::Bool = true) where {S, RingType, OverringType}
  z = EmbeddedModuleElem(M)
  @assert eltype(x) === elem_type(RingType)
  @assert eltype(y) === elem_type(OverringType)
  z.coords = x
  z.ambientcoords = y
  if check
    fl, c = _in(y, M, Val(true))
    @req c == x "Element not contained in module"
  end
  return z
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
    x.ambientcoords = coordinates(x) * basis_matrix(parent(x))
    return x.ambientcoords::Vector{elem_type(OverringType)}
  end
end
