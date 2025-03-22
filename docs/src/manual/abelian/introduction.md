```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# [Introduction](@id AbelianGroupLink2)

Within Hecke, abelian groups are of generic abstract type `GrpAb` which does not
have to be finitely generated, $\mathbb Q/\mathbb Z$ is an example of a more
general abelian group. Having said that, most of the functionality is
restricted to abelian groups that are finitely presented as $\mathbb Z$-modules.

## Basic Creation

Finitely presented (as $\mathbb Z$-modules) abelian groups are of type `FinGenAbGroup`
with elements of type `FinGenAbGroupElem`. The creation is mostly via a relation
matrix $M = (m_{i,j})$ for $1\le i\le n$ and $1\le j\le m$. This creates
a group with $m$ generators $e_j$ and relations
```math
   \sum_{i=1}^n m_{i,j} e_j = 0.
```

```@docs
abelian_group(M::ZZMatrix)
abelian_group(M::Matrix{ZZRingElem})
abelian_group(M::Matrix{Integer})
```

Alternatively, there are shortcuts to create products of cyclic groups:
```@docs
abelian_group(M::Vector{Union{ZZRingElem, Integer}})
```
```jldoctest
julia> G = abelian_group(2, 2, 6)
(Z/2)^2 x Z/6
```

or even

```@docs
free_abelian_group(::Int)
abelian_groups(n::Int)
```
```jldoctest
julia> abelian_groups(8)
3-element Vector{FinGenAbGroup}:
 (Z/2)^3
 Z/2 x Z/4
 Z/8
```

## Invariants
```@docs
is_snf(A::FinGenAbGroup)
number_of_generators(A::FinGenAbGroup)
nrels(G::FinGenAbGroup)
rels(A::FinGenAbGroup)
is_finite(A::FinGenAbGroup)
torsion_free_rank(A::FinGenAbGroup)
order(A::FinGenAbGroup)
exponent(A::FinGenAbGroup)
is_trivial(A::FinGenAbGroup)
is_torsion(G::FinGenAbGroup)
is_cyclic(G::FinGenAbGroup)
elementary_divisors(G::FinGenAbGroup)
```

