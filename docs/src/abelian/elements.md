## Elements
Elements in a finitely generated abelian group are of type `GrpAbFinGenElem`
and are always given as a linear combination of the generators.
Internally this representation is normliased to have a unique
representative.

### Creation
In addition to the standard function `id`, `zero` and `one` that can be
used to create the neutral element, we also support more targeted creation:
```@docs
gens(G::GrpAbFinGen)
GrpAbFinGen(x::Vector{ZZRingElem})
GrpAbFinGen(x::ZZMatrix)
getindex(A::GrpAbFinGen, i::Int)
rand(G::GrpAbFinGen)
rand(G::GrpAbFinGen, B::ZZRingElem)
parent(x::GrpAbFinGenElem)
```
### Access

```@docs
getindex(x::GrpAbFinGenElem, i::Int)
```

### Predicates

We have the standard predicates `iszero`, `isone` and `is_identity`
to test an element for being trivial.

### Invariants
```@docs
order(A::GrpAbFinGenElem)
```
### Iterator
One can iterate over the elements of a finite abelian group.

```@repl
using Hecke # hide
G = abelian_group(ZZRingElem[1 2; 3 4])
for g = G
  println(g)
end
```

