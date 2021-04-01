```@meta
DocTestSetup = quote
    using Hecke
end
```
# Abelian Groups

Here we describe the interface to abelian groups in Hecke.

## Introduction

Within Hecke, abelian groups are of generic abstract type `GrpAb` which does not
have to be finitely generated, $\mathbb Q/\mathbb Z$ is an example of a more
general abelian group. Having said that, most of the functionality is
restricted to abelian groups that are finitely presented as $\mathbb Z$-modules.

### Basic Creation

Finitely presented (as $\mathbb Z$-modules) abelian groups are of type `GrpAbFinGen`
with elements of type `GrpAbFinGenElem`. The creation is mostly via a relation
matrix $M = (m_{i,j})$ for $1\le i\le n$ and $1\le j\le m$. This creates
a group with $m$ generators $e_j$ and relations
```math
   \sum_{i=1}^n m_{i,j} e_j = 0.
```

```@docs
abelian_group(M::fmpz_mat)
abelian_group(M::Array{fmpz, 2})
abelian_group(M::Array{Integer, 2})
```

Alternatively, there are shortcuts to create products of cyclic groups:
```@docs
abelian_group(M::Vector{Union{fmpz, Integer}})
abelian_group(M::Union{fmpz, Integer}...)
```

or even

```@docs
free_abelian_group(::Int)
abelian_groups(n::Int)
```

### Invariants
```@docs
issnf(A::GrpAbFinGen)
ngens(A::GrpAbFinGen)
nrels(G::GrpAbFinGen)
rels(A::GrpAbFinGen)
isfinite(A::GrpAbFinGen)
isinfinite(A::GrpAbFinGen)
rank(A::GrpAbFinGen)
order(A::GrpAbFinGen)
exponent(A::GrpAbFinGen)
istrivial(A::GrpAbFinGen)
istorsion(G::GrpAbFinGen)
iscyclic(G::GrpAbFinGen)
elementary_divisors(G::GrpAbFinGen)
```

## Elements
### Creation
```@docs
id(G::GrpAbFinGen)
gens(G::GrpAbFinGen)
(A::GrpAbFinGen)(x::Array{fmpz, 1})
(A::GrpAbFinGen)(x::fmpz_mat)
getindex(A::GrpAbFinGen, i::Int)
rand(G::GrpAbFinGen)
rand(G::GrpAbFinGen, B::fmpz)
parent(x::GrpAbFinGenElem)
```
### Access

```@docs
getindex(x::GrpAbFinGenElem, i::Int)
```

### Predicates
```@docs
iszero(a::GrpAbFinGenElem)
isone(a::GrpAbFinGenElem)
isidentity(a::GrpAbFinGenElem) 
```
### Invariants
```@docs
order(A::GrpAbFinGenElem)
```
### Iterator
One can iterate over the elements of a finite abelian group.


## Maps
Maps between abelian groups can be constructed via
 - images of the generators
 - pairs of elements 
 - via composition
 - and isomorphism/ inclusion testing

```@docs
hom(G::GrpAbFinGen, H::GrpAbFinGen, A::Array{ <: Map{GrpAbFinGen, GrpAbFinGen}, 2})
isisomorphic(G::GrpAbFinGen, H::GrpAbFinGen)
+(f::GrpAbFinGenMap, g::GrpAbFinGenMap)
-(f::GrpAbFinGenMap, g::GrpAbFinGenMap)
```
## Structural Computations

```@docs
snf(A::GrpAbFinGen)
find_isomorphism(G, op, A::GrpAb)
```

### Subgroups and Quotients
```@docs
torsion_subgroup(G::GrpAbFinGen)
sub(G::GrpAbFinGen, s::Array{GrpAbFinGenElem, 1})
sub(s::Array{GrpAbFinGenElem, 1})
sub(G::GrpAbFinGen, M::fmpz_mat)
sub(G::GrpAbFinGen, n::fmpz)
sub(G::GrpAbFinGen, n::Integer)
psylow_subgroup(G::GrpAbFinGen, p::Union{fmpz, Integer})
has_quotient(G::GrpAbFinGen, invariant::Vector{Int})
has_complement(f::GrpAbFinGenMap)
```

```@docs
psubgroups(g::GrpAbFinGen, p::Integer)
```
```@docs
subgroups(g::GrpAbFinGen)
```

```@docs
quo(G::GrpAbFinGen, s::Array{GrpAbFinGenElem, 1})
quo(G::GrpAbFinGen, M::fmpz_mat)
quo(G::GrpAbFinGen, n::Integer})
quo(G::GrpAbFinGen, n::fmpz})
quo(G::GrpAbFinGen, U::GrpAbFinGen)
```

```@docs
intersect(mG::GrpAbFinGenMap, mH::GrpAbFinGenMap)
+(G::GrpAbFinGen, H::GrpAbFinGen)
intersect(G::GrpAbFinGen, H::GrpAbFinGen)
intersect(A::Array{GrpAbFinGen, 1})
issubset(G::GrpAbFinGen, H::GrpAbFinGen)
issubgroup(G::GrpAbFinGen, H::GrpAbFinGen)
```

### Direct Products
```@docs
direct_product(G::GrpAbFinGen...)
canonical_injection(G::GrpAbFinGen, i::Int)
canonical_projection(G::GrpAbFinGen, i::Int)
flat(G::GrpAbFinGen)
```

### Tensor Producs
```@docs
tensor_product(G::GrpAbFinGen...)
hom(G::GrpAbFinGen, H::GrpAbFinGen, A::Array{ <: Map{GrpAbFinGen, GrpAbFinGen}, 1})
```

### Hom-Group
```@docs
hom(::GrpAbFinGen, ::GrpAbFinGen)
```



