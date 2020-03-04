# From AnticNumberField into something

mutable struct MapDataFromAnticNumberField{T}
  prim_image::T
  isid::Bool

  function MapDataFromAnticNumberField{T}(x::Bool) where T
    @assert x
    z = new{T}()
    z.isid = true
    return z
  end
  
  function MapDataFromAnticNumberField{T}(x::T) where T
    z = new{T}(x, false)
    return z
  end
end

function image(f::MapDataFromAnticNumberField, y::nf_elem)
  f.isid && return y
  z = parent(defining_polynomial(parent(y)))(y)
  return evaluate(z, f.prim_image)
end

function (f::MapDataFromAnticNumberField)(y::nf_elem)
  return image(f, y)
end

map_data_type(K::AnticNumberField, L) = MapDataFromAnticNumberField{elem_type(L)}

map_data(K::AnticNumberField, L, y) = MapDataFromAnticNumberField{typeof(y)}(y)

map_data(K::AnticNumberField, ::Bool) = MapDataFromAnticNumberField{nf_elem}(true)

map_data(K::AnticNumberField, L, ::Bool) = MapDataFromAnticNumberField{elem_type(L)}(true)

# From NfRel into something
mutable struct MapDataFromNfRel{T, S}
  prim_image::T
  base_field_map_data::S
  isid::Bool

  function MapDataFromNfRel{T, S}(x::T, y::S) where {T, S}
    z = new{T, S}(x, y, false)
    return z
  end
  
  function MapDataFromNfRel{T, S}(x::Bool) where {T, S}
    @assert x
    z = new{T, S}()
    z.isid = true
    return z
  end
end

function image(f::MapDataFromNfRel, y)
  f.isid && return y
  z = change_base_ring(y.data, f.base_field_map_data)
  return evaluate(z, f.prim_image)
end

function (f::MapDataFromNfRel)(y)
  return image(f, y)
end

map_data_type(K::NfRel, L) = MapDataFromNfRel{elem_type(L), map_data_type(base_field(K), L)}

map_data_type(K::NfRel, L, base_field_map_data::S) where {S} = MapDataFromNfRel{elem_type(L), S}

map_data(K::NfRel, L, y, g) = MapDataFromNfRel{typeof(y), typeof(g.image_data)}(y, g.image_data)

map_data(K::NfRel, L, y) = MapDataFromNfRel{typeof(y), map_data_type(base_field(K), L)}(y, map_data_type(base_field(K), L)(true))

map_data(K::NfRel, L, ::Bool) = MapDataFromNfRel{elem_type(L), map_data_type(base_field(K), L)}(true)

function map_data(K::NfRel, y) 
  z = MapDataFromNfRel{typeof(y), map_data_type(base_field(K), parent(y))}
  return z(y, map_data(base_field(K), K, true))
end

# From NfAbsNS into something
mutable struct MapDataFromNfAbsNS{T}
  images::T
  isid::Bool

  function MapDataFromNfAbsNS{T}(x::T) where {T}
    z = new{T}(x, false)
    return z
  end
  
  function MapDataFromNfAbsNS{T}(x::Bool) where {T}
    @assert x
    z = new{T}()
    z.isid = true
    return z
  end
end

function image(f::MapDataFromNfAbsNS, y)
  f.isid && return y
  return evaluate(y.data, f.images)
end

function (f::MapDataFromNfAbsNS)(y)
  return image(f, y)
end

map_data_type(K::NfAbsNS, L) = MapDataFromNfAbsNS{Vector{elem_type(L)}}

map_data(K::NfAbsNS, L, y) = MapDataFromNfAbsNS{typeof(y)}(y)

map_data(K::NfAbsNS, L, ::Bool) = MapDataFromNfAbsNS{Vector{elem_type(L)}}(true)

# From NfRelNS into something
mutable struct MapDataFromNfRelNS{T, S}
  images::T
  base_field_map_data::S
  isid::Bool

  function MapDataFromNfRelNS{T, S}(x::T, y::S) where {T, S}
    z = new{T, S}(x, y, false)
    return z
  end
  
  function MapDataFromNfRelNS{T, S}(x::Bool) where {T, S}
    @assert x
    z = new{T, S}()
    z.isid = true
    return z
  end
end

function image(f::MapDataFromNfRelNS, y)
  z = change_base_ring(y.data, f.base_field_map_data)
  return evaluate(z, f.images)
end

function (f::MapDataFromNfRelNS)(y)
  return image(f, y)
end

map_data_type(K::NfRelNS, L) = MapDataFromNfRelNS{Vector{elem_type(L)}, map_data_type(base_field(K), L)}

map_data_type(K::NfRelNS, L, base_field_map_data::S) where {S} = MapDataFromNfRelNS{Vector{elem_type(L)}, S}

# Here g is a NumFieldMor
map_data(K::NfRelNS, L, y, g) = MapDataFromNfRelNS{typeof(y), typeof(g.image_data)}(y, g.image_data)

map_data(K::NfRelNS, L, y) = MapDataFromNfRelNS{typeof(y), map_data_type(base_field(K), L)}(y, map_data_type(base_field(K), L)(true))

#map_data(K::NfRelNS, ::Bool) = MapDataFromNfRelNS{Vector{elem_type(K)}, map_data_type(base_ring(K), K)}(true)

map_data(K::NfRelNS, L, ::Bool) = MapDataFromNfRelNS{Vector{elem_type(L)}, map_data_type(base_ring(K), L)}(true)

mutable struct NumFieldMor{S, T, U, V}
  header::MapHeader{S, T}
  image_data::U
  preimage_data::V

  function NumFieldMor{S, T, U, V}() where {S, T, U, V}
    z = new{S, T, U, V}()
    return z
  end
  
  NumFieldMor{S, T, U, V}(h::MapHeader{S, T}, i::U, p::V) where {S, T, U, V} = new{S, T, U, V}(f, i, p)
end

function _hom(K, L, x...; preimage = nothing)
  header = MapHeader(K, L)
  image_data = map_data(K, L, x...)
  if preimage !== nothing
    preimage_data = map_data(L, preimage...)
    return NumFieldMor(header, image_data, preimage_data)
  end
  z = NumFieldMor{typeof(K), typeof(L), typeof(image_data), map_data_type(L, K)}()
  z.header = header
  z.image_data = image_data
  return z
end

function image(f::NumFieldMor, x)
  return image(f.image_data, x)
end

function preimage(f::NumFieldMor, x)
  return image(f.preimage_data, x)
end

function (f::NumFieldMor)(x)
  return image(f, x)
end

function image_primitive_element(f::NumFieldMor{AnticNumberField})
  return f.image_data.prim_img
end

function image_primitive_element(f::NumFieldMor{<:NfRel})
  return f.image_data.prim_img
end

function domain(f::NumFieldMor)
  return f.header.domain
end

function codomain(f::NumFieldMor)
  return f.header.codomain
end
