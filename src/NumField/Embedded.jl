################################################################################
#
#  Types
#
################################################################################

mutable struct EmbeddedNumField{S, E} <: Field
  field::S
  embedding::E
end

mutable struct EmbeddedNumFieldElem{T} <: FieldElem
  parent
  element::T

  function EmbeddedNumFieldElem{T}(parent, element::T) where {T}
    @assert Hecke.parent(element) === number_field(parent)
    return new{T}(parent, element)
  end
end

const EmbeddedAbsSimpleNumField = EmbeddedNumField{AbsSimpleNumField, AbsSimpleNumFieldEmbedding}

const EmbeddedAbsSimpleNumFieldElem = EmbeddedNumFieldElem{AbsSimpleNumFieldElem}

function (E::EmbeddedNumField{S})(x::T) where {S, T <: NumFieldElem}
  if elem_type(S) === T
    @assert parent(x) === number_field(E)
    return EmbeddedNumFieldElem{T}(E, x)
  else
    return E(number_field(E)(x))
  end
end

function (E::EmbeddedNumField)(x::EmbeddedNumFieldElem)
  @assert parent(x) === E
  return x
end

function (E::EmbeddedNumField)(x::RingElement)
  return E(number_field(E)(x))
end

function hash(x::EmbeddedNumFieldElem, h::UInt)
  return xor(hash(data(x), h), 0x5cccaf5d1346dc53%UInt)
end

function Base.deepcopy_internal(x::EmbeddedNumFieldElem, id::IdDict)
  return parent(x)(Base.deepcopy_internal(data(x), id))
end

number_field(K::EmbeddedNumField) = K.field

embedding(K::EmbeddedNumField) = K.embedding

parent(x::EmbeddedNumFieldElem{T}) where {T} = x.parent::parent_type(x)

elem_type(::Type{EmbeddedNumField{S, E}}) where {S, E} = EmbeddedNumFieldElem{elem_type(S)}

parent_type(::Type{EmbeddedNumFieldElem{T}}) where {T} = EmbeddedNumField{parent_type(T), embedding_type(parent_type(T))}

base_ring(::EmbeddedNumField) = FlintQQ

base_ring_type(::Type{<:EmbeddedNumField}) = QQField

data(x::EmbeddedNumFieldElem) = x.element

function embedded_field(K::SimpleNumField, i::NumFieldEmb)
  @assert number_field(i) === K
  E = EmbeddedNumField(K, i)
  return E, E(gen(K))
end

function embedded_field(K::NonSimpleNumField, i::NumFieldEmb)
  @assert number_field(i) === K
  E = EmbeddedNumField(K, i)
  return E, E.(gens(K))
end

(E::EmbeddedNumField)() = zero(E)

unary_ops = [:(-)]

binary_ops = [:(+), :(*), :(-), :(div), :(//)]

for b in unary_ops
  @eval begin
    function ($b)(x::EmbeddedNumFieldElem)
      return parent(x)($(b)(data(x)))
    end
  end
end

for b in binary_ops
  @eval begin
    function ($b)(x::EmbeddedNumFieldElem, y::EmbeddedNumFieldElem)
      return parent(x)($(b)(data(x), data(y)))
    end
  end
end

function divexact(x::EmbeddedNumFieldElem, y::EmbeddedNumFieldElem; check::Bool = true)
  return parent(x)(divexact(data(x), data(y), check = check))
end

function ==(x::EmbeddedNumFieldElem, y::EmbeddedNumFieldElem)
  return ==(data(x), data(y))
end

iszero(x::EmbeddedNumFieldElem) = iszero(data(x))

isone(x::EmbeddedNumFieldElem) = isone(data(x))

is_unit(x::EmbeddedNumFieldElem) = is_unit(data(x))

zero(E::EmbeddedNumField) = E(zero(number_field(E)))

one(E::EmbeddedNumField) = E(one(number_field(E)))

# Now the ordering

function isless(x::EmbeddedNumFieldElem, y::EmbeddedNumFieldElem)
  i = embedding(parent(x))
  # Need to exclude equality
  if x == y
    return false
  end
  p = 32
  xe, ye = i(data(x), p), i(data(y), p)
  while overlaps(xe, ye)
    p = Int(floor(p * 1.42))
    xe, ye = i(data(x), p), i(data(y), p)
  end
  if real(xe) < real(ye)
    return true
  else
    @assert real(xe) > real(ye)
    return false
  end
end

isless(x::EmbeddedNumFieldElem, y) = isless(x, parent(x)(y))

isless(x, y::EmbeddedNumFieldElem) = isless(parent(y)(x), y)

# Support comparing with floats

function isless(x::EmbeddedNumFieldElem, y::AbstractFloat)
  i = embedding(parent(x))
  # Need to exclude equality
  p = 32
  xe = i(data(x), p)
  # check if y is "equal" to x as a rational
  if is_rational(data(x))
    xq = QQ(data(x))
    d = denominator(xq)
    if isone(d)
      yd = y
    else
      yd = d * y
    end
    if isinteger(yd) && numerator(xq) == yd
      return false
    end
  end

  while contains(real(xe), BigFloat(y))
    p = Int(floor(p * 1.42))
    xe = i(data(x), p)
  end
  if real(xe) < y
    return true
  else
    @assert real(xe) > y
    return false
  end
end

function isless(y::AbstractFloat, x::EmbeddedNumFieldElem)
  i = embedding(parent(x))
  # Need to exclude equality
  p = 32
  xe = i(data(x), p)
  # check if y is "equal" to x as a rational
  if is_rational(data(x))
    xq = QQ(data(x))
    d = denominator(xq)
    if isone(d)
      yd = y
    else
      yd = d * y
    end
    if isinteger(yd) && numerator(xq) == yd
      return false
    end
  end

  while contains(real(xe), BigFloat(y))
    p = Int(floor(p * 1.42))
    xe = i(data(x), p)
  end
  if real(xe) > y
    return true
  else
    @assert real(xe) < y
    return false
  end
end

is_positive(x::EmbeddedNumFieldElem) = x > 0

is_negative(x::EmbeddedNumFieldElem) = x < 0

################################################################################
#
#  Sign
#
################################################################################

function sign(x::EmbeddedNumFieldElem)
  if is_zero(x)
    return x
  end
  if x > 0
    return one(parent(x))
  else
    return -one(parent(x))
  end
end

################################################################################
#
#  Abs
#
################################################################################

abs(x::EmbeddedNumFieldElem) = sign(x) * x

################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, E::EmbeddedNumField)
  print(io, "Embedded field\n$(number_field(E))\nat\n$(embedding(E))")
end

# I overload this to get the value at the embedding
# (But I don't want this in the general printing routines, e.g., over polynomial
# rings.)
function Base.show(io::IO, ::MIME"text/plain", x::EmbeddedNumFieldElem)
  print(io, "$(data(x))")
  a = Float64(real(embedding(parent(x))(data(x), 32)))
  print(io, @sprintf " (%.2f)" a)
end

function Base.show(io::IO, x::EmbeddedNumFieldElem)
  print(io, "$(data(x))")
end

function AbstractAlgebra.expressify(x::EmbeddedNumFieldElem; context = nothing)
  AbstractAlgebra.expressify(data(x), context = context)
end

################################################################################
#
#  Constructors
#
################################################################################

function embedded_number_field(f::Union{QQPolyRingElem, ZZPolyRingElem}, r::Union{AbstractFloat, Tuple}, var = "a")
  K, a = number_field(f, var)
  r = real_embedding(K, r)
  return embedded_field(K, r)
end

function embedded_number_field(f::Vector{<:Union{QQPolyRingElem, ZZPolyRingElem}}, r::Vector{<:Union{AbstractFloat, Tuple}}, var = "a")
  K, a = number_field(f, var)
  r = real_embedding(K, r)
  return embedded_field(K, r)
end

################################################################################
#
#  Creation of elements
#
################################################################################

(E::EmbeddedNumField)(v::Vector) = E(number_field(E)(v))

################################################################################
#
#  Promote rule
#
################################################################################

function AbstractAlgebra.promote_rule(::Type{EmbeddedNumFieldElem{T}}, ::Type{S}) where {T <: NumFieldElem, S <: RingElement}
  if T === S
    return Union{}
  else
    if AbstractAlgebra.promote_rule(T, S) === T
      return EmbeddedNumFieldElem{T}
    else
      return Union{}
    end
  end
end

function AbstractAlgebra.promote_rule(::Type{EmbeddedNumFieldElem{T}}, ::Type{EmbeddedNumFieldElem{T}}) where {T <: NumFieldElem}
  return EmbeddedNumFieldElem{T}
end

################################################################################
#
#  Coercion
#
################################################################################

function (QQ::QQField)(x::EmbeddedNumFieldElem)
  return QQ(data(x))
end

function is_rational(x::EmbeddedNumFieldElem)
  return is_rational(data(x))
end

################################################################################
#
#  Factorization and roots
#
################################################################################

function roots(f::PolyRingElem{<:EmbeddedNumFieldElem})
  E = base_ring(parent(f))
  K = number_field(E)
  return E.(roots(map_coefficients(data, f, cached = false)))
end

function factor(f::PolyRingElem{<:EmbeddedNumFieldElem})
  Ex = parent(f)
  E = base_ring(parent(f))
  K = number_field(E)
  fa = factor(map_coefficients(data, f, cached = false))
  return Fac(Ex(E(constant_coefficient(unit(fa)))),
             Dict{typeof(f), Int}(
               (map_coefficients(E, g, parent = Ex), e) for (g, e) in fa))
end

################################################################################
#
#  Rounding
#
################################################################################

function floor(::Type{ZZRingElem}, a::EmbeddedNumFieldElem)
  i = embedding(parent(a))
  p = 32
  fl, b = unique_integer(floor(real(i(data(a), p))))
  while !fl
    p = Int(floor(p * 1.42))
    fl, b = unique_integer(real(i(data(a), p)))
  end
  return b
end

function floor(a::EmbeddedNumFieldElem)
  return parent(a)(floor(ZZRingElem, a))
end

function ceil(::Type{ZZRingElem}, a::EmbeddedNumFieldElem)
  i = embedding(parent(a))
  p = 32
  fl, b = unique_integer(ceil(real(i(data(a), p))))
  while !fl
    p = Int(ceil(p * 1.42))
    fl, b = unique_integer(real(i(data(a), p)))
  end
  return b
end

function ceil(a::EmbeddedNumFieldElem)
  return parent(a)(ceil(ZZRingElem, a))
end

# rounding
function round(::Type{ZZRingElem}, a::EmbeddedNumFieldElem, ::RoundingMode{:Nearest})
  if is_zero(a)
    return zero(ZZ)
  end

  ca = floor(ZZRingElem, a)
  if a < ca + QQ(1//2)
    return ca
  elseif a > ca + QQ(1//2)
    return ca + 1
  else
    return is_even(ca) ? ca : ca + 1
  end
end

function round(a::EmbeddedNumFieldElem, ::RoundingMode{:Nearest})
  return parent(a)(round(ZZRingElem, a, RoundNearest))
end

round(x::EmbeddedNumFieldElem, ::RoundingMode{:Up}) = ceil(x)
round(::Type{ZZRingElem}, x::EmbeddedNumFieldElem, ::RoundingMode{:Up})= ceil(ZZRingElem, x)

round(x::EmbeddedNumFieldElem, ::RoundingMode{:Down}) = floor(x)
round(::Type{ZZRingElem}, x::EmbeddedNumFieldElem, ::RoundingMode{:Down}) = floor(ZZRingElem, x)

round(x::EmbeddedNumFieldElem, ::RoundingMode{:NearestTiesAway}) = sign(x) * floor(abs(x) + 1 // 2)
function round(::Type{ZZRingElem}, x::EmbeddedNumFieldElem, ::RoundingMode{:NearestTiesAway})
    tmp = floor(ZZRingElem, abs(x) + 1 // 2)
    return is_positive(x) ? tmp : -tmp
end

# default
round(a::EmbeddedNumFieldElem) = round(a, RoundNearestTiesAway)
round(::Type{ZZRingElem}, a::EmbeddedNumFieldElem) = round(ZZRingElem, a, RoundNearestTiesAway)
