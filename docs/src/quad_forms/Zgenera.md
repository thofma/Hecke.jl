# Genera of Integer Lattices
```@meta
CurrentModule = Hecke
DocTestSetup = quote
    using Hecke
  end
```
Two $\mathbb{Z}$-lattices $M$ and $N$ are said to be in the same genus if
their completions $M \otimes \mathbb{Z}_p$ and $N \otimes \mathbb{Z}_p$ are isometric for all
prime numbers $p$ as well as $M \otimes \mathbb{R} \cong N\otimes \mathbb{R}$.

The genus of a $\mathbb{Z}$-lattice is encoded in its Conway-Sloane genus symbol.
The genus symbol itself is a collection of its local genus symbols.
See [CS99](@cite) Chapter 15 for the definitions.
Note that genera for non-integral lattices are supported.

The class `ZGenus` supports genera of $\mathbb{Z}$-lattices.

```@docs
ZGenus
```

## Creation of Genera

### From an integral Lattice

```@docs
genus(::ZLat)
```

### From a gram matrix

```@docs
genus(A::MatElem)
```

### Enumeration of genus symbols

```@docs
Zgenera(sig_pair::Tuple{Int,Int}, determinant::Union{Int,ZZRingElem})
```
### From other genus symbols
```@docs
orthogonal_sum(G1::ZGenus, G2::ZGenus)
```

## Attributes of the genus

```@docs
dim(G::ZGenus)
rank(G::ZGenus)
signature(G::ZGenus)
det(G::ZGenus)
iseven(G::ZGenus)
is_definite(G::ZGenus)
level(G::ZGenus)
scale(G::ZGenus)
norm(G::ZGenus)
primes(G::ZGenus)
is_integral(G::ZGenus)
```
### Discriminant group
[`discriminant_group(::ZGenus)`](@ref)

### Primary genera
```docs
is_primary_with_prime(G::ZGenus)
is_primary(G::ZGenus, p::Union{Integer, ZZRingElem})
is_elementary_with_prime(G::ZGenus)
is_elementary(G::ZGenus, p::Union{Integer, ZZRingElem})
```

### local Symbol
```@docs
local_symbol(G::ZGenus, p)
```

## Representative(s)

```@docs
quadratic_space(G::ZGenus)
rational_representative(G::ZGenus)
representative(G::ZGenus)
representatives(G::ZGenus)
mass(G::ZGenus)
rescale(::ZGenus, ::RationalUnion)
```

## Embeddings and Representations
```@docs
represents(G1::ZGenus, G2::ZGenus)
```

## Local genus Symbols

```@docs
ZpGenus
```

### Creation

```@docs
genus(L::ZLat, p)
genus(A::ZZMatrix, p)
```

### Attributes
```@docs
prime(S::ZpGenus)
iseven(S::ZpGenus)
symbol(S::ZpGenus, scale::Int)
hasse_invariant(S::ZpGenus)
det(S::ZpGenus)
dim(S::ZpGenus)
rank(S::ZpGenus)
excess(S::ZpGenus)
signature(S::ZpGenus)
oddity(S::ZpGenus)
scale(S::ZpGenus)
norm(S::ZpGenus)
level(S::ZpGenus)
```
### Representative
```@docs
representative(S::ZpGenus)
gram_matrix(S::ZpGenus)
rescale(S::ZpGenus, a::RationalUnion)
```

### Orthogonal sums
```@docs
orthogonal_sum(S1::ZpGenus, S2::ZpGenus)
```

### Embeddings/Representations
```@docs
represents(G1::ZpGenus, G2::ZpGenus)
```

