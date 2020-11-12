mutable struct CartesianProductIt
  ranges::Vector{UnitRange{Int}}
  st::Vector{Int}
  inplace::Bool
  function CartesianProductIt()
    return new()
  end
end

function cartesian_product_iterator(v::Vector{UnitRange{Int}}; inplace::Bool = true)
  it = CartesianProductIt()
  it.ranges = v
  it.st = Vector{Int}(undef, length(v))
  for i = 1:length(v)
    it.st[i] = v[i].start
  end
  it.inplace = inplace
  return it
end

function Base.iterate(F::CartesianProductIt)
  return F.st, F.st
end

function Base.iterate(F::CartesianProductIt, st1::Vector{Int})
  i = 1
  if !F.inplace
    st = copy(st1)
  else
    st = st1
  end
  while i <= length(F.ranges)
    it = iterate(F.ranges[i], st[i])
    if it == nothing
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

Base.IteratorSize(::Type{CartesianProductIt}) = Base.HasLength()

Base.eltype(::CartesianProductIt) = Vector{Int}








