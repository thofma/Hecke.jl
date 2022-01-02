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

export restrict

################################################################################
#
#   The NumFieldMor type
#
################################################################################

mutable struct NumFieldMor{S, T, U, V, W} <: Map{S, T, HeckeMap, NumFieldMor}
  header::MapHeader{S, T}
  image_data::U
  inverse_data::V
  absolute_basis::Vector{W}
  absolute_basis_matrix_image::fmpq_mat
  rref::Tuple{fmpq_mat, fmpq_mat}
  pivots_of_rref::Vector{Int}

  function NumFieldMor{S, T, U, V}() where {S, T, U, V}
    z = new{S, T, U, V, elem_type(S)}()
    return z
  end

  function NumFieldMor(K::NumField, L::NumField)
    z = new{typeof(K), typeof(L), map_data_type(K, L), map_data_type(L, K), elem_type(K)}()
    z.header = MapHeader(K, L)
    return z
  end

  function NumFieldMor{S, T, U, V}(h::MapHeader{S, T}, i::U, p::V) where {S, T, U, V}
    z = new{S, T, U, V, elem_type(S)}(h, i, p)
    return z
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
    _assure_has_inverse_data(z)
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

  return image(u, L, gen(K)) == image(v, L, gen(K)) &&
         _isequal(base_field(K), L, u.base_field_map_data, v.base_field_map_data)
end

# Image function
function image(f::MapDataFromNfRel, L, y)
  f.isid && return L(y)
  # TODO: Cache the polynomial ring
  Ly, = PolynomialRing(L, "y", cached = false)
  z = map_coefficients(t -> image(f.base_field_map_data, L, t), y.data, parent = Ly)
  return evaluate(z, f.prim_image)
end

# Functions to validate and create the data.

function map_data(K::NfRel, L, ::Bool)
  z = MapDataFromNfRel{elem_type(L), map_data_type(base_field(K), L)}(true)
  z.base_field_map_data = map_data(base_field(K), L, true)
  return z
end

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
    y = evaluate(map_coefficients(w -> image(z, L, w), defining_polynomial(K), cached = false), yy)
    !iszero(y) && error("Data does not define a morphism")
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
    return v.images == gens(K)
  elseif (v.isid && !u.isid)
    return u.images == gens(K)
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

map_data(K::NfAbsNS, L, ::Bool) = MapDataFromNfAbsNS{Vector{elem_type(L)}}(true)

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
        error("Data does not define a morphism")
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
  z = map_coefficients(w -> image(f.base_field_map_data, L, w), y.data, cached = false)
  return evaluate(z, f.images)
end

function map_data_type(T::Type{<: NfRelNS}, L::Type{<:Any})
  MapDataFromNfRelNS{Vector{elem_type(L)}, map_data_type(base_field_type(T), L)}
end

map_data_type(K::NfRelNS, L) = MapDataFromNfRelNS{Vector{elem_type(L)}, map_data_type(base_field(K), L)}

function map_data(K::NfRelNS, L, ::Bool)
  z = MapDataFromNfRelNS{Vector{elem_type(L)}, map_data_type(base_field(K), L)}(true)
  z.base_field_map_data = map_data(base_field(K), L, true)
  return z
end

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
      w = evaluate(map_coefficients(w -> image(z, L, w), K.pol[i], cached = false), yy)
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
  z = NumFieldMor{typeof(K), typeof(K), map_data_type(K, K), map_data_type(K, K)}(MapHeader(K, K), map_data(K, K, true), map_data(K, K, true))
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

morphism_type(::Type{S}, ::Type{T}) where {S <: NumField, T <: NumField} = NumFieldMor{S, T, map_data_type(S, T), map_data_type(T, S), elem_type(S)}

################################################################################
#
#  Type aliases
#
################################################################################

const NfToNfMor = morphism_type(AnticNumberField, AnticNumberField)

const NfAbsNSToNfAbsNS = morphism_type(NfAbsNS, NfAbsNS)

const NfAbsToNfAbsNS = morphism_type(AnticNumberField, NfAbsNS)

const NfToNfRel = morphism_type(AnticNumberField, NfRel{nf_elem})

const NfRelToNfRelMor_nf_elem_nf_elem = morphism_type(NfRel{nf_elem}, NfRel{nf_elem})

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
#  Preimage computation
#
# ##############################################################################

function _assert_has_preimage_data(f::NumFieldMor)
  if isdefined(f, :absolute_basis_matrix_image)
    return nothing
  end
  K = domain(f)
  L = codomain(f)
  b = absolute_basis(K)
  d = absolute_degree(K)
  n = absolute_degree(L)
  M = zero_matrix(FlintQQ, n, d)
  for i in 1:d
    c = f(b[i])
    cc = absolute_coordinates(c)
    for j in 1:length(cc)
      M[j, i] = cc[j]
    end
  end

  r, R, U =  _rref_with_trans(M)
  pivots = _get_pivots_ut(R)

  f.absolute_basis_matrix_image = M
  f.absolute_basis = b
  f.pivots_of_rref = pivots
  f.rref = R, U

  return nothing
end

function haspreimage(f::NumFieldMor, g::NumFieldElem)
  if isdefined(f, :inverse_data)
    return true, image(f.inverse_data, domain(f), g)
  end
  @assert parent(g) === codomain(f)
  cc = absolute_coordinates(g)
  K = domain(f)
  _assert_has_preimage_data(f)
  fl, s = can_solve_given_rref(f.rref[1], f.rref[2], f.pivots_of_rref, cc)
  if !fl
    return false, zero(K)
  else
    b = f.absolute_basis
    # This is suboptimal
    prim_preimg = reduce(+, (s[i, 1] * b[i] for i in 1:length(b)), init = zero(K))::elem_type(K)
    return true, prim_preimg
  end
end

function preimage(f::NumFieldMor, g::NumFieldElem)
  fl, y = haspreimage(f, g)
  @assert fl
  return y
end

################################################################################
#
#  Computation of the inverse (data)
#
################################################################################

function _assure_has_inverse_data(f::NumFieldMor)
  if isdefined(f, :inverse_data)
    return nothing
  else
    pr = _compute_inverse_data(f, domain(f), codomain(f))
    f.inverse_data = pr
    return nothing
  end
end

function inv(f::NumFieldMor{S, T}) where {S, T}
  _assure_has_inverse_data(f)
  pr = f.inverse_data
  hd = MapHeader(codomain(f), domain(f))
  g = NumFieldMor{T, S, map_data_type(T, S), map_data_type(S, T)}(hd, pr, f.image_data)

  return g
end

# into AnticNumberField
function _compute_inverse_data(f#= image data =#, K, L::AnticNumberField)
  return _compute_inverse_data(f#= image data =#, K, L, L)
end

function _compute_inverse_data(f#= image data =#, K, LL, L::AnticNumberField)
  g = LL(gen(L))
  fl, prim_preimg = haspreimage(f, LL(g))
  @assert fl
  return MapDataFromAnticNumberField{typeof(prim_preimg)}(prim_preimg)
end

# into NfAbsNS
function _compute_inverse_data(f#= image data =#, K, L::NfAbsNS)
  return _compute_inverse_data(f, K, L, L)
end

function _compute_inverse_data(f#= image data =#, K, LL, L::NfAbsNS)
  preimg_gens = elem_type(K)[]
  for g in gens(L)
    fl, preimg = haspreimage(f, LL(g))
    @assert fl
    push!(preimg_gens, preimg)
  end
  return MapDataFromNfAbsNS{typeof(preimg_gens)}(preimg_gens)
end

# into NfRel
function _compute_inverse_data(f#= image data =#, K, L::NfRel)
  return _compute_inverse_data(f#= image data =#, K, L, L)
end

function _compute_inverse_data(f#= image data =#, K, LL, L::NfRel)
  g = gen(L)
  fl, preimg = haspreimage(f, LL(g))
  inverse_data_base_field = _compute_inverse_data(f, K, LL, base_field(L))
  return MapDataFromNfRel{typeof(preimg), typeof(inverse_data_base_field)}(preimg, inverse_data_base_field)
end

# into NfRelNS

function _compute_inverse_data(f#= image data =#, K, L::NfRelNS)
  return _compute_inverse_data(f, K, L, L)
end

function _compute_inverse_data(f, K, LL, L::NfRelNS)
  preimg_gens = elem_type(K)[]
  for g in gens(L)
    fl, preimg = haspreimage(f, LL(g))
    push!(preimg_gens, preimg)
  end
  inverse_data_base_field = _compute_inverse_data(f, K, LL, base_field(L))
  return MapDataFromNfRelNS{typeof(preimg_gens), typeof(inverse_data_base_field)}(preimg_gens, inverse_data_base_field)
end

################################################################################
#
#  Auxillary map_data function
#
################################################################################

function map_data(K::NumField, L; check = true)
  return map_data(K, L, true)
end

function map_data(K::NfRel, L; check = true)
  return map_data(K, L, true)
end

function map_data(K::NfRelNS, L; check = true)
  return map_data(K, L, true)
end

################################################################################
#
#  Composition
#
################################################################################

# f : K -> L, g : L -> M
function _compose(f::MapDataFromAnticNumberField, g#= map data =#, K, L, M)
  return map_data_type(K, M)(image(g, M, image(f, L, gen(K))))
end

function _compose(f::MapDataFromNfRel, g#= map data =#, K, L, M)
  return map_data_type(K, M)(image(g, M, image(f, L, gen(K))),
                             _compose(f.base_field_map_data, g, base_field(K), L, M))
end

function _compose(f::MapDataFromNfAbsNS, g#= map data =#, K, L, M)
  return map_data_type(K, M)(elem_type(M)[image(g, M, image(f, L, u)) for u in gens(K)])
end

function _compose(f::MapDataFromNfRelNS, g#= map data =#, K, L, M)
  return map_data_type(K, M)(elem_type(M)[image(g, M, image(f, L, u)) for u in gens(K)],
                             _compose(f.base_field_map_data, g, base_field(K), L, M))
end

function Base.:(*)(f::NumFieldMor, g::NumFieldMor)
  @req codomain(f) === domain(g) "Composition: Maps are not compatible"
  z = NumFieldMor(domain(f), codomain(g))
  z.image_data = _compose(f.image_data, g.image_data, domain(f), codomain(f), codomain(g))
  if isdefined(f, :inverse_data) && isdefined(g, :inverse_data)
    z.inverse_data = _compose(g.inverse_data, f.inverse_data, codomain(g), domain(g), domain(f))
  end
  return z
end

################################################################################
#
#  Powering
#
################################################################################

function ^(f::NumFieldMor, b::Int)
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

^(a::NumFieldMor, n::IntegerUnion)  = _generic_power(a, n)

################################################################################
#
#  Hashing
#
################################################################################

function Base.hash(f::MapDataFromAnticNumberField, K, L, h::UInt)
  if f.isid
    return xor(hash(L, h), hash(K, h))
  else
    return hash(f.prim_image, h)
  end
end

function Base.hash(f::MapDataFromNfRel, K, L, h::UInt)
  if f.isid
    h = xor(hash(L, h), hash(K, h))
  else
    h = hash(f.prim_image, h)
  end
  h = hash(f.base_field_map_data, base_field(K), L, h)
  return h
end

function Base.hash(f::MapDataFromNfAbsNS, K, L, h::UInt)
  if f.isid
    return xor(hash(L, h), hash(K, h))
  else
    G = f.images
    for g in G
      h = hash(g, h)
    end
    return h
  end
end

function Base.hash(f::MapDataFromNfRelNS, K, L, h::UInt)
  if f.isid
    h = xor(hash(L, h), hash(K, h))
  else
    G = f.images
    for g in G
      h = hash(g, h)
    end
  end
  h = hash(f.base_field_map_data, base_field(K), L, h)
end

Base.hash(f::NumFieldMor, h::UInt) = hash(f.image_data, domain(f), codomain(f), h)

################################################################################
#
#  Restriction
#
################################################################################

function restrict(f::NumFieldMor, K::NonSimpleNumField)
  k = domain(f)
  return hom(K, k, [k(x) for x in gens(K)])*f
end

function restrict(f::NumFieldMor, K::SimpleNumField)
  k = domain(f)
  return hom(K, k, k(gen(K)))*f
end
