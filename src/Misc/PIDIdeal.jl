# Ideals for principal ideal domains
struct PIDIdeal{T} <: Ideal{T}
  gen::T

  PIDIdeal(x::T) where {T} = new{T}(_canonicalize(x))
end

base_ring(x::PIDIdeal) = parent(x.gen)

base_ring_type(::Type{PIDIdeal{T}}) where {T} = parent_type(T)

_can_canonicalize(::Type{ZZRingElem}) = true

_can_canonicalize(::Type{<:PolyRingElem{T}}) where {T <: FieldElem} = true

_can_canonicalize(::Type{<:FieldElem}) = true

function _canonicalize(x::ZZRingElem)
  if x > 0
    return x
  else
    return abs(x)
  end
end

function _canonicalize(x::PolyRingElem{ <: FieldElem})
  if is_monic(x)
    return x
  else
    return iszero(x) ? x : inv(canonical_unit(x)) * x
  end
end

_canonicalize(x::FieldElem) = iszero(x) ? x : one(x)

_canonicalize(x) = x

Base.hash(x::PIDIdeal{T}, h::UInt) where {T} = _can_canonicalize(T) ? hash(gen(x), h) : zero(UInt)

# constructors
*(R::Ring, x::IntegerUnion) = ideal(R, x)

*(x::IntegerUnion, R::Ring) = ideal(R, x)

function _ideal_pid(R::Ring, x::RingElement, y::RingElement...)
  return PIDIdeal(mapreduce(z -> parent(z) === R ? z : R(z), gcd, (x,y...)))
end

function _ideal_pid(R::Ring, x::Vector)
  return _ideal_pid(R, mapreduce(x -> parent(x) === R ? x : R(x), gcd, x; init = zero(R)))
  if parent(x) === R
    return PIDIdeal(x)
  else
    return PIDIdeal(R(x))
  end
end

function ideal(R::PolyRing{<:FieldElem}, x...)
  return _ideal_pid(R, x...)
end

function ideal(R::PolyRing{<:FieldElem}, xs::AbstractVector{T}) where T<:RingElement
  return _ideal_pid(R, xs)
end

function ideal(R::Field, x...)
  return _ideal_pid(R, x...)
end

function ideal(R::Field, xs::AbstractVector{T}) where T<:RingElement
  return _ideal_pid(R, xs)
end

ideal_type(::Type{T}) where {T<:Field} = PIDIdeal{elem_type(T)}

ideal_type(::Type{T}) where {T<:PolyRing{<:FieldElem}} = PIDIdeal{elem_type(T)}


# Show

function Base.show(io::IO, x::PIDIdeal)
  print(io, "ideal(", gen(x), ")")
end

# comparison
function ==(I::PIDIdeal{T}, J::PIDIdeal{T}) where {T}
  if _can_canonicalize(T)
    return I.gen == J.gen
  else
    return divides(I.gen, J.gen) && divides(J.gen, I.gen)
  end
end

# access
gen(I::PIDIdeal) = I.gen

gens(I::PIDIdeal{T}) where {T} = T[I.gen]

# arithmetic

function *(s::RingElement, J::PIDIdeal)
  t = s * J.gen
  return ideal(parent(t), s * J.gen)
end

function *(J::PIDIdeal, s::RingElement)
  return s*J
end

# Arithmetic

gcd(x::PIDIdeal, y::PIDIdeal) = PIDIdeal(gcd(x.gen, y.gen))

lcm(x::PIDIdeal, y::PIDIdeal) = intersect(x, y)

+(x::PIDIdeal, y::PIDIdeal) = gcd(x, y)

*(x::PIDIdeal, y::PIDIdeal) = PIDIdeal(x.gen * y.gen)

^(x::PIDIdeal, n::IntegerUnion) = PIDIdeal(x.gen ^ n)

intersect(x::PIDIdeal, y::PIDIdeal) = PIDIdeal(lcm(x.gen, y.gen))

# Predicates

function is_one(x::PIDIdeal{T}) where {T}
  if _can_canonicalize(T)
    return is_one(gen(x))
  else
    return is_unit(gen(x))
  end
end

is_zero(x::PIDIdeal) = is_zero(gen(x))
