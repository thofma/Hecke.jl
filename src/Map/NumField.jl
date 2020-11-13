################################################################################
#
#  Map/NumField.jl
#
################################################################################

# This implements maps between arbitrary number fields.
#
# Basic idea
# ----------
#
# If f : K -> * is a map from a number field K, then f is completely determined by
#   - f(gen(K)), if K is an AnticNumberField
#   - f(gen(K)), f|_base_field(K), if K is an NfRel
#   - f(gens(K)), if K is an NfAbsNS
#   - f(gens(K)), f|_base_field(K), if K is an NfRelNS
#
# Thus our map type NumFieldMor has fields
#   - header (as usual)
#   - image_data, which define the morphism (as described above)
#   - inverse_data, which define the inverse morphism (if it exists)
#
# To untangle the data defining the morphism and the morphism itself, we
# introduce the types
#
#   MapDataFromAnticNumberField, MapDataFromNfRel, MapDataFromNfAbsNS,
#   MapDataFromNfRelNS
#
# They store the data defining the morphism (these constructions are recursive
# in the relative setting).
#
# Because we know what the type of the inverse_data will be, we can also fully
# initialize the type, even if we don't have access to the preimage data (yet).
#
# Applying a morphism
# -------------------
#
# The application of a morphism is delegated the MapData* types. They implement
# an image function, e.g., with signature
#
#     image(MapDataFromAnticNumberField{NfRel{nf_elem}}, L, x::nf_elem),
#
# which gets called when f : K -> L is a map from AnticNumberField to
# NfRel{nf_elem}. (More precisely, f(a) = image(f.image_data, codomain(f), a))
#
# Note that we do not store L inside explicitely inside MapData* and this
# becomes a problem if f.isid is true. Thus we need to pass L to the function.
#
# Difference to the old system
# ----------------------------
#
# To allow creation of morphism between arbitrary types, we have to be a bit
# careful when it comes to morphism of relative fields.
#
# Assume L/K is an NfRel{nf_elem} and f : L -> L is a morphism, mapping K to K.
# Before, we were basically storing implicitely f(gen(L)) as well as g : K ->
# K. Instead we are storing f(gen(L)) as well as f(L(gen(K)). This new system
# is much more flexible and does not require awkward special cases, which do
# not scale. The (minor) price we pay is that some morphism are a bit slower to
# evaluate.
#
# We are mitigating this regression by storing (in this case) whether f is the
# identity on base_field(K).
#
# Creating morphisms
# ------------------
# This follows now a very easy rule. Let L be any number field. Constructing
# a homorphism K -> L can be constructed as follows:
#
# If K is an AnticNumberField:
#   hom(K, L, ::elem_type(L))
# If K is an NfAbsNS:
#   hom(K, L, ::Vector{elem_type(L)}
# If K is an NfRel:
#   hom(K, L, g, ::elem_type(L)), where g can be
#     - a homomorphism base_field(K) -> L
#     - data defining a homomorphism base_field(K) -> L
#       (e.g., to support
#        hom(::NfRel{nf_elem}, AnticNumberField, nf_elem, nf_elem))
#     - a homorphism base_field(K) -> base_field(L)
#   hom(K, L, ::elem_type(L))
#     - this assumes that the base_field of K embeds naturally into L
# If K is an NfRelNS:
#   hom(K, L, g, ::Vector{elem_type(L)}), where g can be
#     - a homomorphism base_field(K) -> L
#     - data defining a homomorphism base_field(K) -> L
#       (e.g., to support
#        hom(::NfRelNS{nf_elem}, AnticNumberField, nf_elem, Vector{nf_elem}))
#     - a homorphism base_field(K) -> base_field(L)
#   hom(K, L, ::Vector{elem_type(L)})
#     - this assumes that the base_field of K embeds naturally into L 
#
# We also get a nice syntax to create inverses for free:
#
#     hom(K, L, ..., inverse = (x))
#
#  where x is such that hom(L, K, x) works. 
#

################################################################################
#
# The NumFieldMor type
#
################################################################################

mutable struct NumFieldMor{S, T, U, V} <: Map{S, T, HeckeMap, NumFieldMor}
  header::MapHeader{S, T}
  image_data::U
  inverse_data::V

  function NumFieldMor{S, T, U, V}() where {S, T, U, V}
    z = new{S, T, U, V}()
    return z
  end

  function NumFieldMor(K::NumField, L::NumField)
    z = new{typeof(K), typeof(L), map_data_type(K, L), map_data_type(L, K)}()
    z.header = MapHeader(K, L)
    return z
  end
  
  function NumFieldMor{S, T, U, V}(h::MapHeader{S, T}, i::U, p::V) where {S, T, U, V}
    return new{S, T, U, V}(h, i, p)
  end
end

################################################################################
#
#  The hom function
#
################################################################################

function hom(K::S, L::T, x...; inverse = nothing,
                               check::Bool = true,
                               compute_inverse = false) where {S <: NumField,
                                                               T <: NumField}
  header = MapHeader(K, L)

  # Check if data defines a morphism
  image_data = map_data(K, L, x..., check = check)

  if inverse !== nothing
    # Check if data defines a morphism
    # This goes through _validata_data, since we don't want to split the
    # argument if for example the argument is a Vector
    inverse_data = _map_data(L, K, inverse, check = check)
    
    z = NumFieldMor{S, T, typeof(image_data),
                       typeof(inverse_data)}(header, image_data, inverse_data)

  else
    z = NumFieldMor{S, T, typeof(image_data), map_data_type(L, K)}()
  end

  z.header = header
  z.image_data = image_data

  if compute_inverse
    _compute_preimage(z)
  end

  return z
end

################################################################################
#
#  Some type acrobatic. This should be moved to where types will be ending up.
#
################################################################################

base_field_type(::AnticNumberField) = FlintRationalField

base_field_type(::NfAbsNS) = FlintRationalField

base_field_type(::NfRel{T}) where {T} = parent_type(T)

base_field_type(::NfRelNS{T}) where {T} = parent_type(T)

base_field_type(::Type{NfRelNS{T}}) where {T} = parent_type(T)

base_field_type(::Type{NfRel{T}}) where {T} = parent_type(T)

elem_type(::Type{NfRelNS{T}}) where {T} = NfRelNSElem{T}

elem_type(::NfRelNS{T}) where {T} = NfRelNSElem{T}

parent_type(::Type{NfRelNSElem{T}}) where {T} = NfRelNS{T}

elem_type(::Type{NfAbsNS}) = NfAbsNSElem

elem_type(::NfAbsNS) = NfAbsNSElem

parent_type(::Type{NfAbsNSElem}) = NfAbsNS

################################################################################
#
#  Image and preimage function
#
################################################################################

function image(f::NumFieldMor, x)
  @assert domain(f) === parent(x)
  return image(f.image_data, codomain(f), x)
end

function preimage(f::NumFieldMor, x)
  return image(f.inverse_data, domain(f), x)
end

################################################################################
#
#  Now the types to store the data for the maps
#
################################################################################

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

# Helper functions to create the type
map_data_type(K::AnticNumberField, L::NumField) = map_data_type(AnticNumberField, typeof(L))

map_data_type(::Type{AnticNumberField}, T::Type{<:NumField}) = MapDataFromAnticNumberField{elem_type(T)}

# Test if data u, v specfiying a map K -> L define the same morphism
function _isequal(K, L, u::MapDataFromAnticNumberField{T},
                        v::MapDataFromAnticNumberField{S}) where {T, S}
  if u.isid && v.isid
    return true
  end

  z = gen(K)

  return image(u, L, z) == image(v, L, z)
end

# Image function
function image(f::MapDataFromAnticNumberField, L, y::nf_elem)
  f.isid && return L(y)
  z = parent(defining_polynomial(parent(y)))(y)
  return evaluate(z, f.prim_image)
end

# Functions to create and validate the data
#
map_data(K::AnticNumberField, L, ::Bool) = MapDataFromAnticNumberField{elem_type(L)}(true)

function map_data(K::AnticNumberField, L, x::NumFieldElem; check = true)
  if parent(x) === L
    xx = x
  else
    xx = L(x)::elem_type(L)
  end 

  if check
    if !iszero(evaluate(defining_polynomial(K), xx))
      error("Data does not define a morphism")
    end
  end
  return MapDataFromAnticNumberField{elem_type(L)}(xx)
end

function map_data(K::AnticNumberField, L, g::NumFieldMor; check = true)
  if check
    K !== domain(g) && error("Data does not define a morphism")
  end

  z = image_primitive_element(g)

  return map_data(K, L, z; check = false)
end

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

# Helper functions to create the type

function map_data_type(T::Type{<: NfRel}, L::Type{<:Any})
  MapDataFromNfRel{elem_type(L), map_data_type(base_field_type(T), L)}
end

map_data_type(K::NfRel, L::NumField) = map_data_type(typeof(K), typeof(L))

# Test if data u, v specfiying a map K -> L define the same morphism
function _isequal(K, L, u::MapDataFromNfRel{T, S}, v::MapDataFromNfRel{T, S}) where {T, S}
  if u.isid && v.isid
    return true
  end

  return image(u, L, gen(K)) == imgage(v, L, gen(K)) &&
         _isequal(base_field(K), L, u.base_field_map_data, v.base_field_map_data)
end

# Image function
function image(f::MapDataFromNfRel, L, y)
  f.isid && return L(y)
  if parent(f.prim_image) === parent(y) # so from L -> L
    # So we don't have to create the parent
    z = map_coeffs(t -> image(f.base_field_map_data, L, t), y.data, parent = parent(y.data))
  else
    Ly, = PolynomialRing(L, "y", cached = false)
    z = map_coeffs(t -> image(f.base_field_map_data, L, t), y.data, parent = Ly)
  end
  return evaluate(z, f.prim_image)
end

# Functions to validate and create the data.

map_data(K::NfRel, L, ::Bool) = MapDataFromNfRel{elem_type(L), map_data_type(base_field(K), L)}(true)

function map_data(K::NfRel, L, x...; check = true)
  z = map_data(base_field(K), L, Base.front(x)...; check = check)

  local yy::elem_type(L)

  if Base.last(x) isa NumFieldMor
    domain(Base.last(x)) !== K && error("Data does not define a morphism")
    _y = image_primitive_element(Base.last(x))
    if parent(_y) === L
      yy = _y
    else
      yy = L(_y)::elem_type(L)
    end
  else
    y = Base.last(x)
    if parent(y) === L
      yy = y
    else
      yy = L(y)::elem_type(L)
    end
  end

  if check
    y = evaluate(map_coeffs(w -> image(z, L, w), defining_polynomial(K), cached = false), yy)
    !iszero(y) && error("")
  end

  @assert typeof(yy) == elem_type(L)
  @assert typeof(z) == map_data_type(base_field(K), L)
     
  return MapDataFromNfRel{typeof(yy), typeof(z)}(yy, z)
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

function _isequal(K, L, u::MapDataFromNfAbsNS{T}, v::MapDataFromNfAbsNS{T}) where {T}
  # If one is the identity, this means that K === L
  if (u.isid && !v.isid)
    if (v.images == gens(parent(v[1])))
      return true
    end
  elseif (v.isid && !u.isid)
    if (u.images == gens(parent(u[1])))
      return true
    end
  elseif u.isid && v.isid
    return true
  end

  return v.images == u.images 
end

function image(f::MapDataFromNfAbsNS, L, y)
  f.isid && return L(y)
  return msubst(y.data, f.images)
end

map_data_type(K::NfAbsNS, L) = MapDataFromNfAbsNS{Vector{elem_type(L)}}

map_data_type(T::Type{NfAbsNS}, L::Type{<:Any}) = MapDataFromNfAbsNS{Vector{elem_type(L)}}

function map_data(K::NfAbsNS, L, x::Vector; check = true)
  if length(x) != ngens(K)
    error("Data does not define a morphism")
  end

  local xx::Vector{elem_type(L)}

  if x isa Vector{elem_type(L)}
    if parent(x[1]) !== L
      error("Data does not define a morphism")
    end
    xx = x
  else
    xx = map(L, x)::Vector{elem_type(L)}
  end

  if check
    for i in 1:ngens(K)
      if !iszero(evaluate(K.pol[i], xx))
        error("")
      end
    end
  end 

  @assert typeof(xx) == Vector{elem_type(L)}

  return MapDataFromNfAbsNS{typeof(xx)}(xx)
end 

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

function _isequal(K, L, u::MapDataFromNfRelNS{T, S}, v::MapDataFromNfRelNS{T, S}) where {T, S}
   if u.isid && v.isid
    return true
  end

  return all(g -> image(u, L, g) == image(v, L, g), gens(K)) && _isequal(base_field(K), base_field(L), u.base_field_map_data, v.base_field_map_data)
end

function image(f::MapDataFromNfRelNS, L, y)
  f.isid && return L(y)
  z = map_coeffs(w -> image(f.base_field_map_data, L, w), y.data, cached = false)
  return evaluate(z, f.images)
end

function map_data_type(T::Type{<: NfRelNS}, L::Type{<:Any})
  MapDataFromNfRelNS{Vector{elem_type(L)}, map_data_type(base_field_type(T), L)}
end

map_data_type(K::NfRelNS, L) = MapDataFromNfRelNS{Vector{elem_type(L)}, map_data_type(base_field(K), L)}

map_data(::NfRelNS, L, ::Bool) = MapDataFromNfRelNS{Vector{elem_type(L)}, map_data_type(base_ring(K), L)}(true)

function map_data(K::NfRelNS, L, x...; check = true)
  z = map_data(base_field(K), L, Base.front(x)...; check = check)

  local yy::Vector{elem_type(L)}

  if Base.last(x) isa NumFieldMor
    domain(Base.last(x)) !== K && error("")
    _y = image_generators(Base.last(x))
    if parent(_y[1]) === L
      yy = _y
    else
      yy = map(L, _y)::Vector{elem_type(L)}
    end
  else
    y = Base.last(x)
    if !(y isa Vector)
      error("")
    end
    if parent(y[1]) === L
      yy = y
    else
      yy = map(L, y)::Vector{elem_type(L)}
    end
  end

  if check
    for i in 1:ngens(K)
      w = evaluate(map_coeffs(w -> image(z, L, w), K.pol[i], cached = false), yy)
      !iszero(w) && error("Data does not define a morphism")
    end
  end

  @assert typeof(yy) == Vector{elem_type(L)}
  @assert typeof(z) == map_data_type(base_field(K), L)

  return MapDataFromNfRelNS{typeof(yy), typeof(z)}(yy, z)
end

################################################################################
#
#  Equality
#
################################################################################

function Base.:(==)(u::NumFieldMor, v::NumFieldMor)
  if (domain(u) != domain(v)) || (codomain(u) != codomain(v))
    return false
  end
  return _isequal(domain(u), codomain(u), u.image_data, v.image_data)
end

################################################################################
#
#  Identity morphism
#
################################################################################

function id_hom(K::NumField)
  return NumFieldMor{typeof(K), typeof(K), map_data_type(K, K), map_data_type(K, K)}(MapHeader(K, K), map_data(K, K, true), map_data(K, K, true))
end

################################################################################
#
#  Helper functions to compare morphisms
#
################################################################################

_convert_map_data(g::NumFieldMor, L) = __convert_map_data(g.image_data, L)

__convert_map_data(d::MapDataFromAnticNumberField, L) = MapDataFromAnticNumberField{elem_type(L)}(d.isid ? true : L(d.prim_image))

__convert_map_data(d::MapDataFromNfRel, L) = MapDataFromNfReld{elem_type(L)}(L(d.prim_image), d.isid ? true : __convert_map_data(d.base_field_map_data), d.isid)

################################################################################
#
#  Helper functions to pass through inverse data
#
################################################################################

@inline _validate_data(L, K, inverse) = validate_data(L, K, inverse)

@inline _validate_data(L, K, inverse::Tuple) = validate_data(L, K, inverse...)

@inline _map_data(L, K, inverse; check::Bool) = map_data(L, K, inverse, check = check)

@inline _map_data(L, K, inverse::Tuple; check::Bool) = map_data(L, K, inverse..., check = check)

################################################################################
#
#  Morphism type
#
################################################################################

morphism_type(K::NumField) = morphism_type(typeof(K), typeof(K))

morphism_type(K::Type{T}) where T <: NumField = morphism_type(T, T)

morphism_type(K::S, L::T) where {S <: NumField, T <: NumField} = morphism_type(S, T)

morphism_type(::Type{S}, ::Type{T}) where {S <: NumField, T <: NumField} = NumFieldMor{S, T, map_data_type(S, T), map_data_type(T, S)}

################################################################################
#
#  Type aliases
#
################################################################################

const NfToNfMor = morphism_type(AnticNumberField, AnticNumberField)

const NfAbsNSToNfAbsNS = morphism_type(NfAbsNS, NfAbsNS)

const NfAbsToNfAbsNS = morphism_type(AnticNumberField, NfAbsNS)

const NfToNfRel =  morphism_type(AnticNumberField, NfRel{nf_elem})

const NfRelToNfRelMor_nf_elem_nf_elem =  morphism_type(NfRel{nf_elem}, NfRel{nf_elem})

const NfRelToNf = morphism_type(NfRel{nf_elem}, AnticNumberField)

const NfRelNSToNfRelNSMor_nf_elem = morphism_type(NfRelNS{nf_elem}, NfRelNS{nf_elem})

const NfRelToNfRelNSMor_nf_elem = morphism_type(NfRel{nf_elem}, NfRelNS{nf_elem})

################################################################################
#
#  Images of primitive elements/generators
#
################################################################################

function image_primitive_element(f::NumFieldMor{AnticNumberField})
  if f.image_data.isid
    return codomain(f)(gen(domain(f)))
  end
  return f.image_data.prim_image
end

function preimage_primitive_element(f::NfToNfMor)
  if f.inverse_data.isid
    return codomain(f)(gen(domain(f)))
  else
    return f.inverse_data.prim_image
  end
end

function image_generators(f::NumFieldMor{<:NfRelNS})
  return f.image_data.images
end

function image_generators(f::NumFieldMor{<:NfAbsNS})
  return f.image_data.images
end

function image_primitive_element(f::NumFieldMor{<:NfRel})
  if f.image_data.isid
    return gen(domain(f))
  end
  return f.image_data.prim_image
end

################################################################################
#
#  Hashing needs to be done
#
################################################################################

Base.hash(f::NumFieldMor, h::UInt) = zero(UInt)

################################################################################
#
#  Compositions
#
################################################################################

# TODO: Fix this
function Base.:(*)(f::NumFieldMor{AnticNumberField, T, U, V}, g::NumFieldMor{T, T, W, X}) where {T, U, V, W, X}
  return hom(domain(f), codomain(g), g(image_primitive_element(f)))
end

function Base.:(*)(f::NumFieldMor{NfRel{nf_elem}, NfRel{nf_elem}, U, V}, g::NumFieldMor{NfRel{nf_elem}, NfRel{nf_elem}, U, V}) where {U, V}
  K = domain(f)
  return hom(domain(f), codomain(g), g(f(K(gen(base_field(K))))), g(image_primitive_element(f)))
end

function Base.:(*)(f::NumFieldMor{NfRel{T}, NfRelNS{T}}, g::NumFieldMor{NfRelNS{T}, NfRelNS{T}}) where {T}
  @assert base_field(f) === base_field(g)
  return hom(domain(f), codomain(g), g(image_primitive_element(f)))
end

################################################################################
#
#  Computing preimage data
#
################################################################################

function _compute_preimage(f::NfToNfMor)
  K = domain(f)
  L = codomain(f)
  M = zero_matrix(FlintQQ, degree(L), degree(L))
  b = basis(K)
  for i = 1:degree(L)
    c = f(b[i])
    for j = 1:degree(L)
      M[j, i] = coeff(c, j - 1)
    end
  end
  t = zero_matrix(FlintQQ, degree(L), 1)
  if degree(L) == 1
    t[1, 1] = coeff(gen(L), 0)
  else
    t[2, 1] = fmpq(1) # coefficient vector of gen(L)
  end

  s = solve(M, t)
  preim = K(parent(K.pol)([ s[i, 1] for i = 1:degree(K) ]))
  f.inverse_data = map_data(L, K, preim)
  return nothing
end

function _compute_preimg(m::NfToNfMor)
  # build the matrix for the basis change
  K = domain(m)
  L = codomain(m)
  M = zero_matrix(FlintQQ, degree(L), degree(L))
  b = basis(K)
  for i = 1:degree(L)
    c = m(b[i])
    for j = 1:degree(L)
      M[j, i] = coeff(c, j - 1)
    end
  end
  t = zero_matrix(FlintQQ, degree(L), 1)
  t[2, 1] = fmpq(1) # coefficient vector of gen(L)
  s = solve(M, t)
  prim_preimg = K(parent(K.pol)([ s[i, 1] for i = 1:degree(K) ]))
  m.inverse_data = map_data(L, K, prim_preimg)
  #local prmg
  #let L = L, m = m
  #  function prmg(x::nf_elem)
  #    g = parent(L.pol)(x)
  #    return evaluate(g, m.prim_preimg)
  #  end
  #end
  #m.header.preimage = prmg
  #return m.prim_preimg
  return prim_preimg
end


function _compute_preimage(f::NfAbsToNfAbsNS)
  K = domain(f)
  L = codomain(f)
  M = zero_matrix(FlintQQ, degree(K), degree(K))
  el = one(L)
  a = image_primitive_element(f)
  elem_to_mat_row!(M, 1, el)
  for i = 2:degree(K)
    el = mul!(el, el, a)
    elem_to_mat_row!(M, i, el)
  end
  N = zero_matrix(FlintQQ, ngens(L), degree(K))
  gL = gens(L)
  for i = 1:length(gL)
    elem_to_mat_row!(N, i, gL[i])
  end
  fl, x = can_solve(M, N, side = :left)
  @assert fl
  x1, den = _fmpq_mat_to_fmpz_mat_den(x)
  embs = nf_elem[elem_from_mat_row(K, x1, i, den) for i = 1:nrows(x)]
  f.inverse_data = map_data(L, K, embs)
  return nothing
end

function _compute_preimage(f::NumFieldMor{AnticNumberField, <:NfRelNS})
  K = domain(f)
  L = codomain(f)
  el = one(L)
  M = zero_matrix(FlintQQ, degree(K), degree(K))
  M[1, 1] = 1
  a = image_primitive_element(f)
  for i = 2:degree(K)
    el *= a
    v = absolute_coordinates(el)
    for j = 1:degree(K)
      M[i, j] = v[j]
    end
  end
  N = zero_matrix(FlintQQ, ngens(L)+1, degree(K))
  gk = L(gen(base_field(L)))
  v = absolute_coordinates(gk)
  for j = 1:degree(K)
    N[1, j] = v[j]
  end
  gL = gens(L)
  for i = 1:length(gL)
    v = absolute_coordinates(gL[i])
    for j = 1:degree(K)
      N[i+1, j] = v[j]
    end
  end
  fl, x = can_solve(M, N, side = :left)
  x1, den = _fmpq_mat_to_fmpz_mat_den(x)
  preimg_base_field = Nemo.elem_from_mat_row(K, x1, 1, den)
  preimgs = Vector{nf_elem}(undef, length(gL))
  for i = 1:length(gL)
    preimgs[i] = Nemo.elem_from_mat_row(K, x1, i+1, den)
  end
  f.inverse_data = map_data(L, K, preimg_base_field, preimgs)
  return nothing
end

################################################################################
#
#  Computation of the inverse (data)
#
################################################################################

function inv(f::NumFieldMor{S, T}) where {S, T}
  if isdefined(f, :inverse_data)
    pr = f.inverse_data
  else
    pr = _compute_inverse_data(f.image_data, domain(f), codomain(f))
    f.inverse_data = pr
  end

  hd = MapHeader(codomain(f), domain(f))

  g = NumFieldMor{T, S, map_data_type(T, S), map_data_type(S, T)}(hd, pr, f.image_data)

  return g
end

# into AnticNumberField
function _compute_inverse_data(f#= image data =#, K, L::AnticNumberField)
  return _compute_inverse_data(f#= image data =#, K, L, L)
end

function _compute_inverse_data(f#= image data =#, K, LL, L::AnticNumberField)
  d = absolute_degree(K)
  @assert d == absolute_degree(K)
  M = zero_matrix(FlintQQ, d, d)
  b = absolute_basis(K)
  for i = 1:d
    c = image(f, b[i])
    cc = absolute_coordinates(c)
    for j = 1:length(cc)
      M[j, i] = cc[j]
    end
  end
  return _compute_inverse_data(f, K, LL, L, M, b)
end

function _compute_inverse_data(f#= image data =#, K, LL, L::AnticNumberField, M, b)
  d = absolute_degree(K)
  t = zero_matrix(FlintQQ, d, 1)
  g = LL(gen(L))
  cc = absolute_coordinates(g)
  for j in 1:length(cc)
    t[j, 1] = cc[j]
  end
  s = solve(M, t)
  prim_preimg = reduce(+, (s[i, 1] * b[i] for i in 1:d), init = zero(K))
  inverse_data = map_data(L, K, prim_preimg)
  return MapDataFromAnticNumberField{typeof(prim_preimg)}(prim_preimg)
end

# into NfAbsNS
function _compute_inverse_data(f#= image data =#, K, L::NfAbsNS)
  return _compute_inverse_data(f, K, L, L)
end

function _compute_inverse_data(f#= image data =#, K, LL, L::NfAbsNS)
  d = absolute_degree(K)
  @assert d == absolute_degree(K)
  M = zero_matrix(FlintQQ, d, d)
  b = absolute_basis(K)
  for i = 1:d
    c = image(f, b[i])
    cc = coordinates(c)
    for j = 1:length(cc)
      M[j, i] = cc[j]
    end
  end
  return _compute_inverse_data(f, K, LL, L, M, b)
end

function _compute_inverse_data(f#= image data =#, K, LL, L::NfAbsNS, M, b)
  t = zero_matrix(FlintQQ, d, 1)
  d = absolute_degree(K)
  preimg_gens = elem_type(L)[]
  for g in gens(L)
    cc = coordinates(LL(g))
    for j in 1:length(cc)
      t[j, 1] = cc[j]
    end
    s = solve(M, t)
    preimg = reduce(+, (s[i, 1] * b[i] for i in 1:d), init = zero(K))
    push!(preimg_gens, preimg)
  end
  return MapDataFromNfAbsNS{typeof(preimg_gens)}(preimg_gens)
end

# into NfRel
function _compute_inverse_data(f#= image data =#, K, L::NfRel)
  return _compute_inverse_data(f#= image data =#, K, L, L)
end

function _compute_inverse_data(f#= image data =#, K, LL, L::NfRel)
  b = absolute_basis(K)
  d = absolute_degree(K)
  M = zero_matrix(FlintQQ, d, d)
  for i in 1:d
    c = image(f, b[i])
    cc = absolute_coordinates(c)
    for j in 1:length(cc)
      M[j, i] = cc[j]
    end
  end
  return _compute_inverse_data(f, K, LL, L, M, b)
end

function _compute_inverse_data(f#= image data =#, K, LL, L::NfRel, M, b)
  d = absolute_degree(K)
  t = zero_matrix(FlintQQ, d, 1)
  g = gen(L)
  cc = absolute_coordinates(LL(g))
  for j in 1:length(cc)
    t[j, 1] = cc[j]
  end
  s = solve(M, t)
  preimg = reduce(+, (s[i, 1] * b[i] for i in 1:d), init = zero(K))
  inverse_data_base_field = _compute_inverse_data(f, K, LL, base_field(L), M, b)
  return MapDataFromNfRel{typeof(preimg), typeof(inverse_data_base_field)}(preimg, inverse_data_base_field)
end

# into NfRelNS

function _compute_inverse_data(f#= image data =#, K, L::NfRelNS)
  return _compute_inverse_data(f, K, L, L)
end

function _compute_inverse_data(f#= image data =#, K, LL, L::NfRelNS)
  b = absolute_basis(K)
  d = absolute_degree(K)
  M = zero_matrix(FlintQQ, d, d)
  for i in 1:d
    c = image(f, b[i])
    cc = absolute_coordinates(c)
    for j in 1:length(cc)
      M[j, i] = cc[j]
    end
  end
  return _compute_inverse_data(f, K, LL, L, M, b)
end

function _compute_inverse_data(f, K, LL, L::NfRelNS, M, b)
  d = absolute_degree(K)
  t = zero_matrix(FlintQQ, d, 1)
  preimg_gens = elem_type(K)[]
  for g in gens(L)
    cc = absolute_coordinates(LL(g))
    for j in 1:length(cc)
      t[j, 1] = cc[j]
    end
    s = solve(M, t)
    preimg = reduce(+, (s[i, 1] * b[i] for i in 1:d), init = zero(K))
    push!(preimg_gens, preimg)
  end
  inverse_data_base_field = _compute_inverse_data(f, K, LL, base_field(L), M, b)
  return MapDataFromNfRel{typeof(preimg_gens), typeof(inverse_data_base_field)}(preimg, inverse_data_base_field)
end

################################################################################
#
#  Auxillary map_data function
#
################################################################################

function map_data(K::NumField, L::NumField; check = true)
  return map_data(K, L, true)
end
