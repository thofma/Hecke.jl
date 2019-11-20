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
Base.IteratorSize(s::MSet) = Base.HasLength()
Base.IteratorEltype(s::MSet) = Base.HasEltype()
Base.eltype(s::MSet{T}) where {T} = T
Base.in(x, s::MSet) = haskey(s.dict, x)
function Base.push!(s::MSet, x, mult::Int = 1)
  add_to_key!(s.dict, x, mult)
  #if haskey(s.dict, x)
  #  s.dict[x] += mult
  #else
  #  s.dict[x] = mult
  #end
end

function Base.pop!(s::MSet, x) 
  s.dict[x] -= 1
  if s.dict[x] == 0
    delete!(s.dict, x)
  end
  return x
end
Base.pop!(s::MSet, x, deflt) = x in s ? pop!(s, x) : deflt
Base.pop!(s::MSet) = (val = iterate(s.dict)[1][1]; pop!(s, val))
Base.delete!(s::MSet, x) = (delete!(s.dict, x); s)

Base.copy(s::MSet) = union!(similar(s), s)

function Base.iterate(s::MSet)
  I = iterate(s.dict)
  I === nothing && return I
  return I[1][1], (I[1], I[2], 1)
end

function Base.iterate(s::MSet, state)
  if state[3] < state[1][2]
    return state[1][1], (state[1], state[2], state[3]+1)
  else
    I = iterate(s.dict, state[2])
    I === nothing && return I
    val, st = I
    return (val[1], (val, st, 1))
  end
end

Base.union(s::MSet) = copy(s)
function Base.union(s::MSet, sets::Set...)
    u = MSet{join_eltype(s, sets...)}()
    union!(u,s)
    for t in sets
        union!(u,t)
    end
    return u
end
Base.union!(s::MSet, xs) = (for x=xs; push!(s,x); end; s)
Base.union!(s::MSet, xs::AbstractArray) = (for x=xs; push!(s,x); end; s)

function multiplicities(s::MSet)
  return values(s.dict)
end

function Base.unique(s::MSet)
  return collect(keys(s.dict))
end

############################################
# subsets iterator
############################################

struct MSubSetItr{T}
  b::Array{T, 1}
  m::Array{Int, 1}
  length::Int
end

function subsets(s::MSet{T}) where T
  # subsets are represented by integers in a weird base
  # the distinct elements are b0...bn with mult mi
  # subset (bi, ni) -> sum ni gi where gi = prod (mj+1)
  b = collect(unique(s))
  m = [s.dict[x] for x = b]
  #= not needed for the iterator
  g = [1]
  for i=2:length(b)
    push!(g, g[end]*(m[i]+1))
  end
  =#
  return MSubSetItr{T}(b, m, length(m) == 0 ? 1 : prod(x+1 for x=m))
end

function int_to_elt(M::MSubSetItr{T}, i::Int) where T
  s = MSet{T}()
  for j=1:length(M.b)
    k = i % (M.m[j]+1)
    for l=1:k
      push!(s, M.b[j])
    end
    i = div(i-k, M.m[j]+1)
  end
  return s
end

function Base.iterate(M::MSubSetItr)
  return int_to_elt(M, 0), 0
end

function Base.iterate(M::MSubSetItr, st::Int)
  st += 1
  st >= M.length && return nothing
  return int_to_elt(M, st), st
end

function Base.length(M::MSubSetItr)
  return M.length
end

Base.IteratorSize(M::MSubSetItr) = Base.HasLength()
Base.IteratorEltype(M::MSubSetItr) = Base.HasEltype()
Base.eltype(M::MSubSetItr{T}) where {T} = MSet{T}

function Base.show(io::IO, M::MSubSetItr)
  println(io, "subset iterator of length $(M.length) for $(M.b) with multiplicities $(M.m)")
end

#... to be completed from base/Set.jl ...

#subsets for Set
struct SubSetItr{T}
  b::Array{T, 1}
  length::Int
end

function subsets(s::Set{T}) where T
  # subsets are represented by integers in base 2
  b = collect(unique(s))
  return SubSetItr{T}(b, 2^length(b))
end

function int_to_elt(M::SubSetItr{T}, i::Int) where T
  s = Set{T}()
  j = 1
  while i > 0
    if isodd(i)
      push!(s, M.b[j])
    end
    j += 1
    i = div(i, 2)
  end
  return s
end

function Base.iterate(M::SubSetItr)
  return int_to_elt(M, 0), 0
end

function Base.iterate(M::SubSetItr, st::Int)
  st += 1
  st >= M.length && return nothing
  return int_to_elt(M, st), st
end

function Base.length(M::SubSetItr)
  return M.length
end

Base.IteratorSize(M::SubSetItr) = Base.HasLength()
Base.IteratorEltype(M::SubSetItr) = Base.HasEltype()
Base.eltype(M::SubSetItr{T}) where {T} = Set{T}

function Base.show(io::IO, M::SubSetItr)
  println(io, "subset iterator of length $(M.length) for $(M.b)")
end

#only subsets of a given size

struct SubSetSizeItr{T}
  b::Array{T, 1}
  k::Int #subsets of size k only
  B::Array{Array{Int, 1}, 1}
  length::Int
end

function subsets(s::Set{T}, k::Int) where T
  # subsets are represented by integers in the Combinatorial_number_system
  # https://en.wikipedia.org/wiki/Combinatorial_number_system
  # this iterator could indexed, the other one below not
  # maybe use "The coolest way to generate combinations" instead
  b = collect(unique(s))
  m = Int(binomial(length(b), k))
  C = Array{Array{Int, 1}, 1}()
  while k >= 1
    B = Int[]
    i = k-1
    while true
      c = Int(binomial(i, k))
      if c < m && length(B) < length(b)
        push!(B, c)
        i += 1
      else
        break
      end
    end
    push!(C, B)
    k -=1 
  end

  return SubSetSizeItr{T}(b, length(C), C, m)
end


function int_to_elt(M::SubSetSizeItr{T}, i::Int) where T
  s = Set{T}()
  j = 1
  while j <= length(M.B)
    z = findlast(x -> x <= i, M.B[j])
    push!(s, M.b[z + M.k - j])
    i -= M.B[j][z]
    j += 1
  end
  while length(s) < M.k
    push!(s, M.b[length(s)])
  end

  return s
end

function Base.iterate(M::SubSetSizeItr)
  return int_to_elt(M, 0), 0
end

function Base.iterate(M::SubSetSizeItr, st::Int)
  st += 1
  st >= M.length && return nothing
  return int_to_elt(M, st), st
end

function Base.length(M::SubSetSizeItr)
  return M.length
end

Base.IteratorSize(M::SubSetSizeItr) = Base.HasLength()
Base.IteratorEltype(M::SubSetSizeItr) = Base.HasEltype()
Base.eltype(M::SubSetSizeItr{T}) where {T} = Set{T}

function Base.show(io::IO, M::SubSetSizeItr)
  println(io, "subset iterator of length $(M.length) for $(M.b) and subsets of size $(M.k)")
end


