## Structural Computations
Abelian groups support a wide range of structural operations such as
 - enumeration of subgroups
 - (outer) direct products
 - tensor and `hom` constructions
 - free resolutions and general complexes
 - (co)-homology and tensor and `hom`-functors

```@docs
snf(A::FinGenAbGroup)
Hecke.find_isomorphism(G, op, A::Hecke.GrpAb)
```

### Subgroups and Quotients
```@docs
torsion_subgroup(G::FinGenAbGroup)
sub(G::FinGenAbGroup, s::Vector{FinGenAbGroupElem})
sub(s::Vector{FinGenAbGroupElem})
sub(G::FinGenAbGroup, M::ZZMatrix)
sub(G::FinGenAbGroup, n::ZZRingElem)
sub(G::FinGenAbGroup, n::Integer)
sylow_subgroup(G::FinGenAbGroup, p::Union{ZZRingElem, Integer})
Hecke.has_quotient(G::FinGenAbGroup, invariant::Vector{Int})
Hecke.has_complement(f::FinGenAbGroupHom)
is_pure(U::FinGenAbGroup, G::FinGenAbGroup)
is_neat(U::FinGenAbGroup, G::FinGenAbGroup)
saturate(U::FinGenAbGroup, G::FinGenAbGroup)
```

A sophisticated algorithm for the enumeration of all (or selected) subgroups
of a finite abelian group is available.

```@docs
psubgroups(g::FinGenAbGroup, p::Integer)
```
```@repl subgroups
using Hecke # hide
G = abelian_group([6, 12])
shapes = MSet{Vector{ZZRingElem}}()
for U = psubgroups(G, 2)
  push!(shapes, elementary_divisors(U[1]))
end
shapes
```
So there are $2$ subgroups isomorphic to $C_4$ (`ZZRingElem[4] : 2`),
$1$ isomorphic to $C_2\times C_4$, 1 trivial and $3$ $C_2$ subgroups.

```@docs
subgroups(g::FinGenAbGroup)
```
```@repl subgroups
for U = subgroups(G, subtype = [2])
  @show U[1], map(U[2], gens(U[1]))
end
for U = subgroups(G, quotype = [2])
  @show U[1], map(U[2], gens(U[1]))
end
```

```@docs
quo(G::FinGenAbGroup, s::Vector{FinGenAbGroupElem})
quo(G::FinGenAbGroup, M::ZZMatrix)
quo(G::FinGenAbGroup, n::Integer)
quo(G::FinGenAbGroup, n::ZZRingElem)
quo(G::FinGenAbGroup, U::FinGenAbGroup)
```

For 2 subgroups `U` and `V` of the same group `G`, `U+V` returns
the smallest subgroup of `G` containing both. Similarly, $U\cap V$
computes the intersection and $U \subset V$ tests for inclusion.
The difference between `issubset =` $\subset$ and
`is_subgroup` is that the inclusion map is also returned in the 2nd call.

```@docs
intersect(mG::FinGenAbGroupHom, mH::FinGenAbGroupHom)
```

### Direct Products
```@docs
direct_product(G::FinGenAbGroup...)
canonical_injection(G::FinGenAbGroup, i::Int)
canonical_projection(G::FinGenAbGroup, i::Int)
flat(G::FinGenAbGroup)
```

### Tensor Producs
```@docs
tensor_product(G::FinGenAbGroup...)
hom(G::FinGenAbGroup, H::FinGenAbGroup, A::Vector{ <: Map{FinGenAbGroup, FinGenAbGroup}})
```

### Hom-Group
```@docs
hom(::FinGenAbGroup, ::FinGenAbGroup)
```

