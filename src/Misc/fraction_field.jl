struct FractionFieldMap{RingType, FieldType}
  R::RingType
  K::FieldType
end

fraction_field_map(R::Ring, K::Field) = FractionFieldMap{typeof(R), typeof(K)}(R, K)

image(f::FractionFieldMap, x) = K(x)

# numerator, denominator

decompose(f::FractionFieldMap{T, T}, x) where {T} = x

_has_preimage(f::FractionFieldMap{T, T}, x) where {T} = true

ring(f::FractionFieldMap) = f.R

function decompose(f::FractionFieldMap, x::RingElement)
  y, d = integral_split(x, ring(f))
end

function decompose(f::FractionFieldMap, x::MatrixElem)
  return integral_split(x, ring(f))
end

function decompose(f::FractionFieldMap, x::Vector)
  return integral_split(x, ring(f))
end

function denominator(f::FractionFieldMap, x::Array)
  l = one(ring(f))
  for y in x
    l = lcm!(l, l, denominator(f, y))
  end
  return l
end

denominator(f::FractionFieldMap, x) = integral_split(x, ring(f))[2]

_has_preimage(f::FractionFieldMap, x) = is_unit(integral_split(x, ring(f))[2])

function _has_preimage(f::FractionFieldMap, x::Vector)
  for y in x
    if !_has_preimage(f, y)
      return false
    end
  end
  return true
end

function _has_preimage(f::FractionFieldMap{ZZRing, QQField}, x::QQFieldElem)
  return isinteger(x)
end
