mutable struct CartesianProductIt{T, U}
  ranges::Vector{T}
  inplace::Bool
  value::Vector{U}

  function CartesianProductIt{T, U}() where {T, U}
    return new{T, U}()
  end
end

function cartesian_product_iterator(x::T, n::Int; inplace::Bool = true) where T
  v = fill(x, n)
  return cartesian_product_iterator(v, inplace = inplace)
end

function cartesian_product_iterator(v::Vector{T}; inplace::Bool = true) where T
  it = CartesianProductIt{T, eltype(T)}()
  it.ranges = v
  it.inplace = inplace
  it.value = Vector{eltype(T)}(undef, length(v))
  return it
end

function Base.iterate(F::CartesianProductIt{T, U}) where {T, U}
  r = length(F.ranges)
  if r == 0
    return nothing
  end
  x = iterate(F.ranges[1])
  if x isa Nothing
    return nothing
  end
  a, b = x
  st = Vector{typeof(b)}(undef, r)
  st[1] = b
  F.value[1] = a
  for i = 2:r
    x = iterate(F.ranges[i])
    if x isa Nothing
      return nothing
    end
    a, b = x
    st[i] = b
    F.value[i] = a
  end

  if !F.inplace
    ret = deepcopy(F.value)
  else
    ret = F.value
  end

  return ret, st
end

function Base.iterate(F::CartesianProductIt, st::Vector{S}) where {S}
  i = 1
  r = length(F.ranges) + 1
  while i != r
    it = iterate(F.ranges[i], st[i])
    if it === nothing
      a, b = iterate(F.ranges[i])
      F.value[i] = a
      st[i] = b
      #st[i] = first(F.ranges[i])
      i += 1
      continue
    end
    F.value[i] = it[1]
    st[i] = it[2]

    if !F.inplace
      ret = deepcopy(F.value)
    else
      ret = F.value
    end

    return ret, st
  end
  return nothing
end

function Base.length(F::CartesianProductIt)
  return prod(length(x) for x in F.ranges)
end

Base.IteratorSize(::Type{<:CartesianProductIt{T}}) where T = Base.HasLength()

Base.eltype(::Type{<:CartesianProductIt{T}}) where T = Vector{eltype(T)}

function Base.getindex(F::CartesianProductIt{T}, i::Int) where T
  v = Vector{eltype{T}}(undef, length(F.ranges))
  ind = i
  for s = length(v):-1:1
    d = prod(Int[length(F.ranges[j]) for j = 1:s-1])
    q, ind = divrem(ind, d)
    if iszero(ind)
      v[s] = F.ranges[s][q]
      for t = s-1:-1:1
        v[t] = last(F.ranges[t])
      end
      return v
    end
    v[s] = F.ranges[s][q+1]
  end
  return v
end

function Base.getindex(F::CartesianProductIt, coordinates::Vector{Int})
  @assert length(coordinates) == length(F.ranges)
  return Int[F.ranges[i][coordinates[i]] for i = 1:length(F.ranges)]
end
