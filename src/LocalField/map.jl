################################################################################
#
#  The NumFieldMor type
#
################################################################################

mutable struct LocalFieldMor{S, T, U, V, W} <: Map{S, T, HeckeMap, LocalFieldMor}
  header::MapHeader{S, T}
  image_data::U
  inverse_data::V
  absolute_basis::Vector{W}
  absolute_basis_matrix_image::Generic.MatSpaceElem{padic}
  rref::Tuple{Generic.MatSpaceElem{padic}, Generic.MatSpaceElem{padic}}
  pivots_of_rref::Vector{Int}

  function LocalFieldMor{S, T, U, V}() where {S, T, U, V}
    z = new{S, T, U, V, elem_type(S)}()
    return z
  end

  function LocalFieldMor(K::S, L::T) where {S <: Union{FlintPadicField, FlintQadicField, LocalField}, T <: Union{FlintPadicField, FlintQadicField, LocalField}}
    z = new{typeof(K), typeof(L), map_data_type(K, L), map_data_type(L, K), elem_type(K)}()
    z.header = MapHeader(K, L)
    return z
  end

  function LocalFieldMor{S, T, U, V}(h::MapHeader{S, T}, i::U, p::V) where {S, T, U, V}
    z = new{S, T, U, V, elem_type(S)}(h, i, p)
    return z
  end
end

################################################################################
#
#   Identity
#
################################################################################

function id_hom(K::T) where T <: Union{LocalField, FlintQadicField}
  z = LocalFieldMor{typeof(K), typeof(K), map_data_type(K, K), map_data_type(K, K)}(MapHeader(K, K), map_data(K, K, true), map_data(K, K, true))
end

################################################################################
#
#  Morphism type
#
################################################################################

morphism_type(K::LocalField) = morphism_type(typeof(K), typeof(K))

morphism_type(K::FlintQadicField) = morphism_type(typeof(K), typeof(K))

morphism_type(K::Type{T}) where T <: Union{LocalField, FlintQadicField} = morphism_type(T, T)

morphism_type(K::S, L::T) where {S <: Union{LocalField, FlintQadicField, FlintPadicField}, T <: Union{LocalField, FlintQadicField}} = morphism_type(S, T)

morphism_type(::Type{S}, ::Type{T}) where {S <: Union{LocalField, FlintQadicField, FlintPadicField}, T <: Union{LocalField, FlintQadicField}} = LocalFieldMor{S, T, map_data_type(S, T), map_data_type(T, S), elem_type(S)}
################################################################################
#
#  The hom function
#
################################################################################

function hom(K::S, L::T, x...; inverse = nothing,
                               check::Bool = true,
                               compute_inverse = false) where {S <: Union{LocalField, FlintQadicField},
                                                               T <: Union{LocalField, FlintQadicField}}
  header = MapHeader(K, L)

  # Check if data defines a morphism
  image_data = map_data(K, L, x..., check = check)

  if inverse !== nothing
    # Check if data defines a morphism
    # This goes through _validata_data, since we don't want to split the
    # argument if for example the argument is a Vector
    inverse_data = map_data(L, K, inverse, check = check)

    z = LocalFieldMor{S, T, typeof(image_data),
                       typeof(inverse_data)}(header, image_data, inverse_data)

  else
    z = LocalFieldMor{S, T, typeof(image_data), map_data_type(L, K)}()
  end

  z.header = header
  z.image_data = image_data

  if compute_inverse
    _assure_has_inverse_data(z)
  end

  return z
end

################################################################################
#
#  Image and preimage function
#
################################################################################

function image(f::LocalFieldMor, x)
  @assert domain(f) === parent(x)
  return image(f.image_data, codomain(f), x)
end

################################################################################
#
#  Types to store the data for the maps
#
################################################################################

mutable struct MapDataFromPadicField{S}
  codomain::S
end


function map_data_type(T::Type{FlintPadicField}, L::Type{S}) where S <: Union{LocalField, FlintQadicField, FlintPadicField}
  MapDataFromPadicField{S}
end

map_data_type(T::FlintPadicField, L::Union{LocalField, FlintQadicField, FlintPadicField}) = map_data_type(typeof(T), typeof(L))

# Test if data u, v specfiying a map K -> L define the same morphism
function _isequal(K, L, u::MapDataFromPadicField{T}, v::MapDataFromPadicField{T}) where T
  return true
end

function image(f::MapDataFromPadicField, L, y)
  return L(y)
end

function map_data(K::FlintPadicField, L, ::Bool)
  return MapDataFromPadicField{typeof(L)}(L)
end

function map_data(K::FlintPadicField, L, x...; check::Bool = true)
  return MapDataFromPadicField{typeof(L)}(L)
end

# From LocalField into something
mutable struct MapDataFromLocalField{T, S}
  prim_image::T
  base_field_map_data::S
  isid::Bool

  function MapDataFromLocalField{T, S}(x::T, y::S) where {T, S}
    z = new{T, S}(x, y, false)
    return z
  end

  function MapDataFromLocalField{T, S}(x::Bool) where {T, S}
    @assert x
    z = new{T, S}()
    z.isid = true
    return z
  end
end


function map_data_type(T::Type{<:LocalField}, L::Type{<:Union{LocalField, FlintQadicField, FlintPadicField}})
  MapDataFromLocalField{elem_type(L), map_data_type(base_field_type(T), L)}
end

map_data_type(T::LocalField, L::Union{LocalField, FlintQadicField, FlintPadicField}) = map_data_type(typeof(T), typeof(L))

# Test if data u, v specfiying a map K -> L define the same morphism
function _isequal(K, L, u::MapDataFromLocalField{T, S}, v::MapDataFromLocalField{T, S}) where {T, S}
  if u.isid && v.isid
    return true
  end

  return image(u, L, gen(K)) == image(v, L, gen(K)) &&
         _isequal(base_field(K), L, u.base_field_map_data, v.base_field_map_data)
end

function image(f::MapDataFromLocalField, L, y)
  f.isid && return L(y)
  # TODO: Cache the polynomial ring
  Ly, = polynomial_ring(L, "y", cached = false)
  z = map_coefficients(t -> image(f.base_field_map_data, L, t), y.data, parent = Ly)
  e = evaluate(z, f.prim_image)
  setprecision!(e, min(precision(e), precision(y)))
  return e
end

function map_data(K::LocalField, L, ::Bool) #the embedding
  z = MapDataFromLocalField{elem_type(L), map_data_type(base_field(K), L)}(true)
  z.base_field_map_data = map_data(base_field(K), L, true)
  return z
end

function map_data(K::LocalField, L, g::LocalFieldMor, y; check = true)
  domain(g) !== base_field(K) && error("Data does not define a morphism")
  local z::map_data_type(base_field(K), L)
  if codomain(g) === L
    z = g.image_data
  else
    gg = g * hom(codomain(g), L)
    z = gg.image_data
  end

  return map_data_given_base_field_data(K, L, z, y; check = check)
end

function map_data(K::LocalField, L, x...; check = true)
  if length(x) == 1 && x[1] isa Tuple
    return map_data(K, L, x[1]...; check = check)::map_data_type(K, L)
  end

  local z::map_data_type(base_field(K), L)

  if length(x) > 1
    z = map_data(base_field(K), L, Base.front(x)...; check = check)
  else
    z = map_data(base_field(K), L; check = check)
  end
  return map_data_given_base_field_data(K, L, z, x[end]; check = check)
end

map_data(K::LocalField, L; check = true) = map_data(K, L, true)

function map_data_given_base_field_data(K::LocalField, L, z, y; check = true)
  if parent(y) === L
    yy = y
  else
    yy = L(y)::elem_type(L)
  end

  if check
    f = map_coefficients(w -> image(z, L, w), defining_polynomial(K), cached = false)
    y = evaluate(f, yy)
    !iszero(y) && error("Data does not define a morphism")
  end

  @assert typeof(yy) == elem_type(L)
  @assert typeof(z) == map_data_type(base_field(K), L)

  return MapDataFromLocalField{typeof(yy), typeof(z)}(yy, z)::map_data_type(typeof(K), typeof(L))
end

# From QadicField into something
mutable struct MapDataFromQadicField{T}
  prim_image::T
  isid::Bool

  function MapDataFromQadicField{T}(x::T) where {T}
    z = new{T}(x, false)
    return z
  end

  function MapDataFromQadicField{T}(x::Bool) where {T}
    @assert x
    z = new{T}()
    z.isid = true
    return z
  end
end

function map_data_type(T::Type{FlintQadicField}, L::Type{<:Union{LocalField, FlintQadicField}})
  MapDataFromQadicField{elem_type(L)}
end

map_data_type(::FlintQadicField, L::Union{LocalField, FlintQadicField}) = map_data_type(FlintQadicField, typeof(L))

# Test if data u, v specfiying a map K -> L define the same morphism
function _isequal(K, L, u::MapDataFromQadicField{T}, v::MapDataFromQadicField{T}) where {T}
  if u.isid && v.isid
    return true
  end

  return image(u, L, gen(K)) == image(v, L, gen(K))
end

function image(f::MapDataFromQadicField, L, y)
  f.isid && return L(y)
  # TODO: Cache the polynomial ring
  Qpx = polynomial_ring(base_field(parent(y)), cached = false)[1]
  return evaluate(Qpx(y), f.prim_image)
end

function map_data(K::FlintQadicField, L, f::LocalFieldMor, x; check::Bool = true)
  if check && false
    base_field(K) != domain(f) && error("Data does not define a morphism")
  end

  z = L(x)

  return map_data(K, L, z; check = false)
end


function map_data(K::FlintQadicField, L, f::LocalFieldMor; check::Bool = true)
  if check
    K !== domain(f) && error("Data does not define a morphism")
  end

  z = L(image_primitive_element(f))

  return map_data(K, L, z; check = false)
end


function map_data(K::FlintQadicField, L, ::Bool)
  return MapDataFromQadicField{elem_type(L)}(true)
end

map_data(K::FlintQadicField, L; check = true) = map_data(K, L, L(gen(K)), check = check)


function map_data(K::FlintQadicField, L, x; check = true)

  if check
    y = evaluate(defining_polynomial(K), x)
    !iszero(y) && error("Data does not define a morphism")
  end

  return MapDataFromQadicField{typeof(x)}(x)
end

function image_primitive_element(f::LocalFieldMor)
  if f.image_data.isid
    return codomain(f)(gen(domain(f)))
  end
  return f.image_data.prim_image
end

################################################################################
#
#  Preimage computation
#
# ##############################################################################

function _assert_has_preimage_data(f::LocalFieldMor)
  if isdefined(f, :absolute_basis_matrix_image)
    return nothing
  end
  K = domain(f)
  L = codomain(f)
  b = absolute_basis(K)
  d = absolute_degree(K)
  n = absolute_degree(L)
  M = zero_matrix(absolute_base_field(K), n, d)
  for i in 1:d
    c = f(b[i])
    cc = absolute_coordinates(c)
    for j in 1:length(cc)
      M[j, i] = cc[j]
    end
  end

  r, R, U =  _rref_with_trans(M) #terribly unstable numerically
  pivots = _get_pivots_ut(R)

  f.absolute_basis_matrix_image = M
  f.absolute_basis = b
  f.pivots_of_rref = pivots
  f.rref = R, U

  return nothing
end

function haspreimage(f::LocalFieldMor, g::Union{qadic, LocalFieldElem})
  if isdefined(f, :inverse_data)
    return true, image(f.inverse_data, domain(f), g)
  end
  @assert parent(g) === codomain(f)
  K = domain(f)
  d = absolute_degree(K)
  cc = absolute_coordinates(g)
  _assert_has_preimage_data(f)
  fl, s = can_solve_given_rref(f.rref[1], f.rref[2], f.pivots_of_rref, cc)
  if !fl
    return false, zero(K)
  else
    b = f.absolute_basis
    # This is suboptimal
    prim_preimg = zero(K)
    for i = 1:d
      prim_preimg += s[i, 1] * b[i]
    end
    return true, prim_preimg
  end
end

function preimage(f::LocalFieldMor, g::Union{qadic, LocalFieldElem})
  fl, y = haspreimage(f, g)
  @assert fl
  return y
end

################################################################################
#
#  Computation of the inverse (data)
#
################################################################################

function _assure_has_inverse_data(f::LocalFieldMor)
  if isdefined(f, :inverse_data)
    return nothing
  else
    pr = _compute_inverse_data(f, domain(f), codomain(f))
    f.inverse_data = pr
    return nothing
  end
end

function inv(f::LocalFieldMor{S, T}) where {S, T}
  _assure_has_inverse_data(f)
  pr = f.inverse_data
  hd = MapHeader(codomain(f), domain(f))
  g = NumFieldMor{T, S, map_data_type(T, S), map_data_type(S, T)}(hd, pr, f.image_data)
  return g
end

function _compute_inverse_data(f#= image data =#, K, L::LocalField)
  return _compute_inverse_data(f#= image data =#, K, L, L)
end

function _compute_inverse_data(f#= image data =#, K, L::QadicField)
  return _compute_inverse_data(f#= image data =#, K, L, L)
end

function _compute_inverse_data(f#= image data =#, K, LL, L::LocalField)
  g = LL(gen(L))
  fl, prim_preimg = haspreimage(f, LL(g))
  @assert fl
  return MapDataFromLocalField{typeof(prim_preimg)}(prim_preimg)
end


function _compute_inverse_data(f#= image data =#, K, LL, L::FlintQadicField)
  g = LL(gen(L))
  fl, prim_preimg = haspreimage(f, LL(g))
  @assert fl
  return MapDataFromQadicField{typeof(prim_preimg)}(prim_preimg)
end

################################################################################
#
#  Composition
#
################################################################################

# f : K -> L, g : L -> M
function _compose(f::MapDataFromQadicField, g#= map data =#, K, L, M)
  return map_data_type(K, M)(image(g, M, image(f, L, gen(K))))
end

function _compose(f::MapDataFromLocalField, g#= map data =#, K, L, M)
  return map_data_type(K, M)(image(g, M, image(f, L, gen(K))),
                             _compose(f.base_field_map_data, g, base_field(K), L, M))
end

function Base.:(*)(f::LocalFieldMor, g::LocalFieldMor)
  @req codomain(f) === domain(g) "Composition: Maps are not compatible"
  z = LocalFieldMor(domain(f), codomain(g))
  z.image_data = _compose(f.image_data, g.image_data, domain(f), codomain(f), codomain(g))
  if isdefined(f, :inverse_data) && isdefined(g, :inverse_data)
    z.inverse_data = _compose(g.inverse_data, f.inverse_data, codomain(g), domain(g), domain(f))
  end
  return z
end

################################################################################
#
#  Equality
#
################################################################################

function Base.:(==)(u::T, v::T) where T <: LocalFieldMor
  if (domain(u) != domain(v)) || (codomain(u) != codomain(v))
    return false
  end
  return _isequal(domain(u), codomain(u), u.image_data, v.image_data)
end


################################################################################
#
#  Powering
#
################################################################################

function ^(f::LocalFieldMor, b::Int)
  K = domain(f)
  @assert K == codomain(f)
  d = absolute_degree(K)
  b = mod(b, d)
  if b == 0
    return id_hom(K)
  elseif b == 1
    return f
  else
    bit = ~((~UInt(0)) >> 1)
    while (UInt(bit) & b) == 0
      bit >>= 1
    end
    z = f
    bit >>= 1
    while bit != 0
      z = z * z
      if (UInt(bit) & b) != 0
        z = z * f
      end
      bit >>= 1
    end
    return z
  end
end

^(a::LocalFieldMor, n::IntegerUnion)  = _generic_power(a, n)

################################################################################
#
#  Hashing
#
################################################################################

function Base.hash(f::MapDataFromQadicField, K, L, h::UInt)
  if f.isid
    return xor(hash(L, h), hash(K, h))
  else
    return hash(f.prim_image, h)
  end
end

function Base.hash(f::MapDataFromLocalField, K, L, h::UInt)
  if f.isid
    h = xor(hash(L, h), hash(K, h))
  else
    h = hash(f.prim_image, h)
  end
  h = hash(f.base_field_map_data, base_field(K), L, h)
  return h
end

Base.hash(f::LocalFieldMor, h::UInt) = hash(f.image_data, domain(f), codomain(f), h)

################################################################################
#
#  Restriction
#
################################################################################

function restrict(f::LocalFieldMor, K::Union{FlintQadicField, LocalField})
  k = domain(f)
  return hom(K, k, k(gen(K)))*f
end

################################################################################
#
#   To make the automorphism group work
#
################################################################################

function GrpGenToNfMorSet(G::GrpGen, K::T) where T <: Union{LocalField, FlintQadicField}
  return GrpGenToNfMorSet(automorphism_list(K), G, NfMorSet(K))
end

function GrpGenToNfMorSet(G::GrpGen, aut::Vector{S}, K::T) where {S <: LocalFieldMor, T <: Union{LocalField, FlintQadicField}}
  return GrpGenToNfMorSet(aut, G, NfMorSet(K))
end
