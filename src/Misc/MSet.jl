export MSet
export multiplicities
export multiplicity
export multiset
export subsets

@doc raw"""
    MSet{T} <: AbstractSet{T}

Type for a multi-set, i.e. a set where elements are not unique, they
(can) have a multiplicity. `MSet`s can be created from any finite iterator.

# Examples
```jldoctest
julia> MSet([1,1,2,3,4,4,5])
MSet{Int64} with 7 elements:
  5
  4 : 2
  2
  3
  1 : 2
```
`4 : 2` means the element `4` has multiplicity `2`, i.e. was included twice.
"""
mutable struct MSet{T} <: AbstractSet{T}
  dict::Dict{T,Int}

  MSet{T}() where {T} = new{T}(Dict{T,Int}())
  MSet{T}(itr) where {T} = union!(new{T}(Dict{T,Int}()), itr)
  MSet{T}(d::Dict{T, Int}) where {T} = new{T}(d)
  MSet{T}(l::Vector{T}, m::Vector{Int}) where {T} = MSet{T}(Dict(zip(l, m)))
end

MSet() = MSet{Any}()
MSet(itr) = MSet{eltype(itr)}(itr)
MSet(d::Dict{T, Int}) where {T} = MSet{T}(d)
MSet(l::Vector{T}, m::Vector{Int}) where {T} = MSet{T}(l, m)

@doc raw"""
    multiset(iter) -> MSet{eltype(iter)}
    multiset(d::Dict{T, Int}) -> MSet{T}
    multiset{l::Vector{T}, m::Vector{Int}} -> MSet{T}

Given either:
 - a finite iterator `iter`;
 - a dictionary `d` whose values are positive integers;
 - a list `l` and a list of positive integers `m` of same length as `l`;
return the asscciated multi-set `M`.

# Examples
```jldoctest
julia> str = "A nice sentence"
"A nice sentence"

julia> multiset(str)
MSet{Char} with 15 elements:
  'n' : 3
  'A'
  'c' : 2
  'i'
  'e' : 4
  's'
  't'
  ' ' : 2

julia> multiset(Int[x^3%8 for x = 1:50])
MSet{Int64} with 50 elements:
  0 : 25
  5 : 6
  7 : 6
  3 : 6
  1 : 7

julia> d = Dict("a" => 4, "b" => 1, "c" =>9)
Dict{String, Int64} with 3 entries:
  "c" => 9
  "b" => 1
  "a" => 4

julia> multiset(d)
MSet{String} with 14 elements:
  "c" : 9
  "b"
  "a" : 4

julia> multiset(["a", "b", "c"], [4, 1, 9])
MSet{String} with 14 elements:
  "c" : 9
  "b"
  "a" : 4
```
"""
multiset(iter) = MSet(iter)

function multiset(d::Dict{T, Int}) where {T}
  @req minimum(collect(values(d))) > 0 "The values of d must be positive integers"
  return MSet{T}(d)
end

function multiset(l::Vector{T}, m::Vector{Int}) where {T}
  @req length(m) == length(l) "Lists must have the same length"
  @req minimum(m) > 0 "Multiplicity list must consist of positive integers"
  return MSet{T}(l, m)
end

@doc raw"""
    multiset(T::Type) -> MSet{T}

Create an unitialized multi-set `M` with elements of type `T`.

# Examples
```jldoctest
julia> multiset(QQFieldElem)
MSet{QQFieldElem}()

julia> multiset()
MSet{Any}()
```
"""
multiset() = MSet()

multiset(T::DataType) = MSet{T}()

@doc raw"""
    Base.similar(M::MSet{T}) -> MSet{T}
    Base.similar(M::MSet, T::Type) -> MSet{T}

Create an unitialized multi-set with elements of type `T`.

# Examples
```jldoctest
julia> m = multiset([1,1,2,3,4,4,5])
MSet{Int64} with 7 elements:
  5
  4 : 2
  2
  3
  1 : 2

julia> similar(m)
MSet{Int64}()

julia> similar(m, QQFieldElem)
MSet{QQFieldElem}()
```
"""
Base.similar(::MSet{T}) where {T} = MSet{T}()
Base.similar(::MSet, T::Type) = MSet{T}()

# We try to adopt the same conventions as in Oscar, so one-line printing should
# stay in one line, and we do not give details about what is in the MSet: the
# detailled printing will take care of it
function Base.show(io::IO, s::MSet{T}) where {T}
  if isempty(s)
    print(io, "MSet{$(eltype(s))}()")
  elseif get(io, :supercompact, false)
    io = pretty(io)
    print(io, "Multi-set with ", ItemQuantity(length(s), "element"))
    if !(T == Any)
      print(io, " of type $T")
    end
  else
    print(io, "MSet(")
    first = true
    for (k, v) in s.dict
      first || print(io, ", ")
      first = false
      if v > 1
        print(io, "$k : $v")
      else
        print(io, "$k")
      end
    end
    print(io, ")")
  end
end

# We use the one-line (hopefully implemented!) printing system for the elements
# in
function Base.show(io::IO, ::MIME"text/plain", s::MSet)
  print(io,"MSet{",eltype(s),"}")
  if isempty(s)
    print(io,"()")
  else
    io = pretty(io)
    szh, szw = displaysize(io)
    szh -= 5
    szw -= 10
    print(io, " with ", ItemQuantity(length(s), "element"), ":")
    print(io, Indent())
    d = s.dict
    un = collect(keys(d))
    if length(un) <= szh
      rmax = maximum(ndigits(k) for k in values(d))
      offmax = szw - (rmax + 3)
      lmax = min(maximum(length(sprint(show, a)) for a in un), offmax)
      for k in un
        pk = sprint(show, k)
        lk = length(pk)
        v = d[k]
        println(io)
        if lk > offmax
          print(io, pk[1:offmax-length(" \u2026")], " \u2026")
        else
          print(io, pk)
        end
        lk = min(offmax, lk)
        if v > 1
          print(io, " "^(lmax-lk+1), ": $v")
        end
      end
    else
      lmax = maximum(length(sprint(show, a)) for a in un[1:szh])
      for i in 1:sz
        println(io)
        k = un[i]
        lk = length(sprint(show, k))
        v = d[k]
        if v > 1
          print(io, "$k", " "^(lmax-lk+1), ": $v")
        else
          print(io, "$k")
        end
      end
      println(io)
      print(io, "\u22ee")
    end
  end
end

Base.isempty(s::MSet) = isempty(s.dict)
Base.length(s::MSet) = sum(values(s.dict))
Base.IteratorSize(::Type{MSet}) = Base.HasLength()
Base.IteratorEltype(::Type{MSet}) = Base.HasEltype()
Base.eltype(::Type{MSet{T}}) where {T} = T
Base.in(x, s::MSet) = haskey(s.dict, x)

function Base.push!(s::MSet, x, mult::Int=1)
  add_to_key!(s.dict, x, mult)
end

function Base.pop!(s::MSet{T}, x) where {T}
  y = x isa T ? x : T(x)
  y in s || throw(KeyError(y))
  add_to_key!(s.dict, y, -1)
  return y
end

function Base.pop!(s::MSet{T}, x, default) where {T}
  y = x isa T ? x : T(x)
  return y in s ? pop!(s, y) : (default isa T ? default : T(default))
end

Base.pop!(s::MSet) = (val = iterate(s.dict)[1][1]; pop!(s, val))

function Base.delete!(s::MSet{T}, x) where {T}
  y = x isa T ? x : T(x)
  delete!(s.dict, y)
  return s
end

Base.copy(s::MSet) = union!(similar(s), s)

==(s1::MSet, s2::MSet) = s1.dict == s2.dict

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

function Base.union(s::MSet, sets...)
  T = Base.promote_eltype(s, sets...)
  u = MSet{T}()
  union!(u, s)
  for t in sets
    union!(u, t)
  end
  return u
end

function Base.union!(s::MSet, xs)
  T = eltype(s)
  @req promote_type(T, eltype(xs)) == T "Cannot coerce elements"
  for x in xs
    push!(s, convert(T, x))
  end
  return s
end

function Base.filter(pred, s::MSet)
  t = similar(s)
  for (x, m) in s.dict
    if pred(x)
      push!(t, x, m)
    end
  end
  return t
end

function Base.filter!(pred, s::MSet)
  un = unique(s)
  for x in un
    if !pred(x)
      delete!(s, x)
    end
  end
  return s
end

@doc raw"""
    multiplicities(s::MSet{T}) -> ValueIterator{Dict{T, Int}}

Return an iterator for the multiplicities of all the elements in `s`.

# Examples
```jldoctest
julia> m = multiset([1,1,2,3,4,4,5])
MSet{Int64} with 7 elements:
  5
  4 : 2
  2
  3
  1 : 2

julia> mult_m = multiplicities(m)
ValueIterator for a Dict{Int64, Int64} with 5 entries. Values:
  1
  2
  1
  1
  2

julia> collect(mult_m)
5-element Vector{Int64}:
 1
 2
 1
 1
 2
```
"""
function multiplicities(s::MSet)
  return values(s.dict)
end

@doc raw"""
    multiplicity(s::MSet{T}, x::T) -> Int

Return the multiplicity of the element `x` in the multi-set `s`. If `x` is not
in `s`, return 0.

# Examples
```jldoctest
julia> m = multiset([1,1,2,3,4,4,5])
MSet{Int64} with 7 elements:
  5
  4 : 2
  2
  3
  1 : 2

julia> multiplicity(m, 2)
1

julia> multiplicity(m, 6)
0
```
"""
function multiplicity(s::MSet{T}, x::T) where {T}
  y = x isa T ? x : T(x)
  if haskey(s.dict, y)
    return s.dict[y]
  else
    return 0
  end
end

function Base.unique(s::MSet)
  return collect(keys(s.dict))
end

Base.setdiff(s::MSet, itrs...) = setdiff!(copy(s), itrs...)

function Base.setdiff!(s::MSet, itrs...)
  for x in itr
    setdiff!(s, itr)
  end
  return s
end

function Base.setdiff!(s::MSet, itr)
  for x in itr
    pop!(s, x)
  end
  return s
end

############################################
# subsets iterator
############################################

struct MSubSetItr{T}
  b::Vector{T}
  m::Vector{Int}
  length::Int
end

@doc raw"""
    subsets(s::MSet) -> MSubSetIt{T}

Return an iterator on all sub-multi-sets of `s`.
"""
function subsets(s::MSet{T}) where T
  # subsets are represented by integers in a weird base
  # the distinct elements are b0...bn with mult mi
  # subset (bi, ni) -> sum ni gi where gi = prod (mj+1)
  b = unique(s)
  m = Int[multiplicity(s, x) for x in b]
  #= not needed for the iterator
  g = [1]
  for i=2:length(b)
    push!(g, g[end]*(m[i]+1))
  end
  =#
  return MSubSetItr{T}(b, m, length(m) == 0 ? 1 : prod(x+1 for x in m))
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

Base.IteratorSize(::Type{MSubSetItr}) = Base.HasLength()
Base.IteratorEltype(::Type{MSubSetItr}) = Base.HasEltype()
Base.eltype(::Type{MSubSetItr{T}}) where {T} = MSet{T}

function Base.show(io::IO, M::MSubSetItr{T}) where {T}
  print(io, "Iterator for subsets of a multi-set")
  if !get(io, :supercompact, false) && T != Any
    print(io, " with elements of type $T")
  end
end

function Base.show(io::IO, ::MIME"text/plain", M::MSubSetItr)
  io = pretty(io)
  println(io, "Iterator for subsets")
  println(io, Indent(), "of ", MSet(M.b, M.m))
  print(io, Dedent(), "of length ", M.length)
end

#... to be completed from base/Set.jl ...

#subsets for Set
struct SubSetItr{T}
  b::Vector{T}
  length::Int
end

@doc raw"""
    subsets(s::Set) -> SubSetItr{T}

Return an iterator for all sub-sets of `s`.
"""
function subsets(s::Set{T}) where T
  # subsets are represented by integers in base 2
  b = unique(s)
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

Base.IteratorSize(::Type{SubSetItr}) = Base.HasLength()
Base.IteratorEltype(::Type{SubSetItr}) = Base.HasEltype()
Base.eltype(::Type{SubSetItr{T}}) where {T} = Set{T}

function Base.show(io::IO, M::SubSetItr{T}) where {T}
  print(io, "Iterator for subsets of a set")
  if !get(io, :supercompact, false) && T != Any
    print(io, " with elements of type $T")
  end
end

function Base.show(io::IO, ::MIME"text/plain", M::SubSetItr)
  io = pretty(io)
  println(io, "Iterator for subsets")
  println(io, Indent(), "of ", Set(M.b))
  print(io, Dedent(), "of length ", M.length)
end

#only subsets of a given size
struct SubSetSizeItr{T}
  b::Vector{T}
  k::Int #subsets of size k only
  B::Vector{Vector{Int}}
  length::Int
end

@doc raw"""
    subsets(s::Set, k::Int) -> SubSetSizeItr{T}

Return an iterator on all sub-sets of size `k` of `s`.
"""
function subsets(s::Set{T}, k::Int) where T
  # subsets are represented by integers in the Combinatorial_number_system
  # https://en.wikipedia.org/wiki/Combinatorial_number_system
  # this iterator could indexed, the other one below not
  # maybe use "The coolest way to generate combinations" instead
  b = unique(s)
  m = Int(binomial(length(b), k))
  C = Vector{Vector{Int}}()
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
  0 >= M.length && return nothing
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

Base.IteratorSize(::Type{SubSetSizeItr}) = Base.HasLength()
Base.IteratorEltype(::Type{SubSetSizeItr}) = Base.HasEltype()
Base.eltype(::Type{SubSetSizeItr{T}}) where {T} = Set{T}

function Base.getindex(S::SubSetSizeItr, i::Int)
  return Hecke.int_to_elt(S, i)
end

function Base.show(io::IO, M::SubSetSizeItr{T}) where {T}
  print(io, "Iterator for subsets of size $(M.k) of a set")
  if !get(io, :supercompact, false) && T != Any
    print(io, " with elements of type $T")
  end
end

function Base.show(io::IO, ::MIME"text/plain", M::SubSetSizeItr)
  io = pretty(io)
  println(io, "Iterator for subsets of size $(M.k)")
  println(io, Indent(), "of ", Set(M.b))
  print(io, Dedent(), "of length ", M.length)
end
