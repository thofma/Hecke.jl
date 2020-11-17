mutable struct CartesianProductIt{T}
  ranges::Vector{T}
  inplace::Bool
  function CartesianProductIt{T}() where T
    return new{T}()
  end
end

function cartesian_product_iterator(x::T, n::Int; inplace::Bool = true) where T
  v = fill(x, n)
  return cartesian_product_iterator(v, inplace = inplace)
end

function cartesian_product_iterator(v::Vector{T}; inplace::Bool = true) where T
  it = CartesianProductIt{T}()
  it.ranges = v
  it.inplace = inplace
  return it
end

function Base.iterate(F::CartesianProductIt{T}) where T
  r = length(F.ranges)
  st = Vector{eltype(T)}(undef, r)
  for i = 1:r
    st[i] = first(F.ranges[i])
  end
  return st, st
end

function Base.iterate(F::CartesianProductIt, st1::Vector{Int})
  i = 1
  if !F.inplace
    st = copy(st1)
  else
    st = st1
  end
  r = length(F.ranges) + 1
  while i != r
    it = iterate(F.ranges[i], st[i])
    if it === nothing
      st[i] = first(F.ranges[i])
      i += 1
      continue
    end
    st[i] = it[1]
    return st, st
  end
  return nothing
end

function Base.length(F::CartesianProductIt)
  return prod(length(x) for x in F.ranges)
end

Base.IteratorSize(::Type{CartesianProductIt{T}}) where T = Base.HasLength()

Base.eltype(::CartesianProductIt{T}) where T = Vector{eltype(T)}

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








