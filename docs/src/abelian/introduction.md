```@meta
DocTestSetup = quote
    using Hecke
end
```
# [Abelian Groups](@id AbelianGroupLink)

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
abelian_group(M::Matrix{fmpz})
abelian_group(M::Matrix{Integer})
```

Alternatively, there are shortcuts to create products of cyclic groups:
```@docs
abelian_group(M::Vector{Union{fmpz, Integer}})
```
```@repl
using Hecke # hide
G = abelian_group(2, 2, 6)
```

or even

```@docs
free_abelian_group(::Int)
abelian_groups(n::Int)
```
```@repl
using Hecke # hide
abelian_groups(8)
```

### Invariants
```@docs
is_snf(A::GrpAbFinGen)
ngens(A::GrpAbFinGen)
nrels(G::GrpAbFinGen)
rels(A::GrpAbFinGen)
isfinite(A::GrpAbFinGen)
is_infinite(A::GrpAbFinGen)
rank(A::GrpAbFinGen)
order(A::GrpAbFinGen)
exponent(A::GrpAbFinGen)
istrivial(A::GrpAbFinGen)
is_torsion(G::GrpAbFinGen)
is_cyclic(G::GrpAbFinGen)
elementary_divisors(G::GrpAbFinGen)
```

