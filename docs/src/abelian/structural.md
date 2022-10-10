## Structural Computations
Abelian groups support a wide range of structural operations such as
 - enumeration of subgroups
 - (outer) direct products
 - tensor and `hom` constructions
 - free resolutions and general complexes
 - (co)-homology and tensor and `hom`-functors

```@docs
snf(A::GrpAbFinGen)
Hecke.find_isomorphism(G, op, A::Hecke.GrpAb)
```

### Subgroups and Quotients
```@docs
torsion_subgroup(G::GrpAbFinGen)
sub(G::GrpAbFinGen, s::Vector{GrpAbFinGenElem})
sub(s::Vector{GrpAbFinGenElem})
sub(G::GrpAbFinGen, M::fmpz_mat)
sub(G::GrpAbFinGen, n::fmpz)
sub(G::GrpAbFinGen, n::Integer)
psylow_subgroup(G::GrpAbFinGen, p::Union{fmpz, Integer})
Hecke.has_quotient(G::GrpAbFinGen, invariant::Vector{Int})
Hecke.has_complement(f::GrpAbFinGenMap)
```

A sophisticated algorithm for the enumeration of all (or selected) subgroups
of a finite abelian group is available.

```@docs
psubgroups(g::GrpAbFinGen, p::Integer)
```
```@repl subgroups
using Hecke # hide
G = abelian_group([6, 12])
shapes = MSet{Vector{fmpz}}()
for U = psubgroups(G, 2)
  push!(shapes, elementary_divisors(U[1]))
end
shapes
```
So there are $2$ subgroups isomorphic to $C_4$ (`fmpz[4] : 2`),
$1$ isomorphic to $C_2\times C_4$, 1 trivial and $3$ $C_2$ subgroups.

```@docs
subgroups(g::GrpAbFinGen)
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
quo(G::GrpAbFinGen, s::Vector{GrpAbFinGenElem})
quo(G::GrpAbFinGen, M::fmpz_mat)
quo(G::GrpAbFinGen, n::Integer)
quo(G::GrpAbFinGen, n::fmpz)
quo(G::GrpAbFinGen, U::GrpAbFinGen)
```

For 2 subgroups `U` and `V` of the same group `G`, `U+V` returns
the smallest subgroup of `G` containing both. Similarly, $U\cap V$
computes the intersection and `U \subset V` tests for inclusion.
The difference between `issubset =` $\subset$ and
`is_subgroup` is that the inclusion map is also returned in the 2nd call.

```@docs
intersect(mG::GrpAbFinGenMap, mH::GrpAbFinGenMap)
```

### Direct Products
```@docs
direct_product(G::GrpAbFinGen...)
Hecke.canonical_injection(G::GrpAbFinGen, i::Int)
Hecke.canonical_projection(G::GrpAbFinGen, i::Int)
flat(G::GrpAbFinGen)
```

### Tensor Producs
```@docs
tensor_product(G::GrpAbFinGen...)
hom(G::GrpAbFinGen, H::GrpAbFinGen, A::Vector{ <: Map{GrpAbFinGen, GrpAbFinGen}})
```

### Hom-Group
```@docs
hom(::GrpAbFinGen, ::GrpAbFinGen)
```

