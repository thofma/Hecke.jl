struct WithCache{T}
  data::T
  cache::UInt

end

function with_cache(x::T) where {T}
  h = hash(x)
  return WithCache{T}(x, h)
end

Base.hash(x::WithCache{T}) where {T} = x.cache

struct FacElemWrap{T, S}
  fac::Dict{WithCache{T}, fmpz}
  hash::UInt
  #parent::FacElemMon{S}
end

@inline function Base.iterate(x::FacElemWrap)
  z, st = iterate(x.fac)
  ((z[1]).data => z[2]), st
end

@inline function Base.iterate(x::FacElemWrap, st)
  v = iterate(x.fac, st)
  if v === nothing
    return nothing
  else
    z, st = v
    return ((z[1]).data => z[2]), st
  end
end

function Base.:(*)(x::FacElemWrap, y::FacElemWrap)
  z = copy(x.fac)
  z = copy(x.fac)
  for (a, v) in y.fac
    add_to_key!(z, a, v, remove_zero = true)
  end
  return FacElemWrap(z)
end

function FacElemWrap(x::Dict{T, fmpz}) where {T}
  z = Dict{WithCache{T}, fmpz}(with_cache(k) => p for (k, p) in x)
  return FacElemWrap{T, Nothing}(z, UInt(0))
end
