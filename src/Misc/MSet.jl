export MSet

mutable struct MSet{T} <: AbstractSet{T}
  dict::Dict{T, Int}
  MSet{T}() where {T} = new(Dict{T,Int}())
  MSet{T}(itr) where {T} = union!(new(Dict{T,Int}()), itr)
end

MSet() = MSet{Any}()
MSet(itr) = MSet{eltype(itr)}(itr)


Base.eltype(::Type{MSet{T}}) where {T} = T
Base.similar(s::MSet{T}) where {T} = MSet{T}()
Base.similar(s::MSet, T::Type) = MSet{T}()

#TODO: compact printing, remove trailing , ... the works...
function Base.show(io::IO, s::MSet)
    print(io,"MSet")
    if isempty(s)
        print(io,"{",eltype(s),"}()")
        return
    end
    print(io,"(")
    for (k,v) = s.dict
      if v > 1
        print(io, "$k : $v, ") # ugly
      else
        print(io, "$k, ") # ugly
      end
    end
    print(io,")")
end

Base.isempty(s::MSet) = isempty(s.dict)
Base.length(s::MSet)  = BigInt(sum(values(s.dict)))
Base.in(x, s::MSet) = haskey(s.dict, x)
function Base.push!(s::MSet, x)
  if haskey(s.dict, x)
    s.dict[x] += 1
  else
    s.dict[x] = 1
  end
end

function Base.pop!(s::MSet, x) 
  s.dict[x] -= 1
  if s.dict[x] == 0
    delete!(s.dict, x)
  end
  return x
end
Base.pop!(s::MSet, x, deflt) = x in s ? pop!(s, x) : deflt
Base.pop!(s::MSet) = (idx = start(s.dict); val = s.dict.keys[idx]; pop!(s, val))
Base.delete!(s::MSet, x) = (delete!(s.dict, x); s)

Base.copy(s::MSet) = union!(similar(s), s)

Base.start(s::MSet)       = (start(s.dict), 1)
Base.done(s::MSet, state) = done(s.dict, state[1])
function Base.next(s::MSet, state)
  if state[2] < s.dict.vals[state[1]]
    return s.dict.keys[state[1]], (state[1], state[2]+1)
  else
    val, st = next(s.dict, state[1])
    return (val[1], (st, 1))
  end
end

union(s::MSet) = copy(s)
function union(s::MSet, sets::Set...)
    u = MSet{join_eltype(s, sets...)}()
    union!(u,s)
    for t in sets
        union!(u,t)
    end
    return u
end
const ∪ = union
union!(s::MSet, xs) = (for x=xs; push!(s,x); end; s)
union!(s::MSet, xs::AbstractArray) = (for x=xs; push!(s,x); end; s)

function multiplicities(s::MSet)
  return values(s.dict)
end

function Base.unique(s::MSet)
  return collect(keys(s.dict))
end

#... to be completed from base/Set.jl ...
