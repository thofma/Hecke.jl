```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# Elements
Elements in a finitely generated abelian group are of type `FinGenAbGroupElem`
and are always given as a linear combination of the generators.
Internally this representation is normalised to have a unique
representative.

## Creation
In addition to the standard function `id`, `zero` and `one` that can be
used to create the neutral element, we also support more targeted creation:
```@docs
gens(G::FinGenAbGroup)
FinGenAbGroup(x::Vector{ZZRingElem})
FinGenAbGroup(x::ZZMatrix)
getindex(A::FinGenAbGroup, i::Int)
rand(G::FinGenAbGroup)
rand(G::FinGenAbGroup, B::ZZRingElem)
parent(x::FinGenAbGroupElem)
```
## Access

```@docs
getindex(x::FinGenAbGroupElem, v::AbstractVector{Int})
getindex(x::FinGenAbGroupElem, i::Int)
```

## Predicates

We have the standard predicates `iszero`, `isone` and `is_identity`
to test an element for being trivial.

## Invariants
```@docs
order(A::FinGenAbGroupElem)
```
## Iterator
One can iterate over the elements of a finite abelian group.

```jldoctest
julia> G = abelian_group(ZZRingElem[1 2; 3 4])
Finitely generated abelian group
  with 2 generators and 2 relations and relation matrix
  [1   2]
  [3   4]

julia> for g in G
         println(g)
       end
Abelian group element [0, 0]
Abelian group element [0, 1]
```

