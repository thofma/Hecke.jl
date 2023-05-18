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

The class `ZZGenus` supports genera of $\mathbb{Z}$-lattices.

```@docs
ZZGenus
```

## Creation of Genera

### From an integral Lattice

```@docs
genus(::ZZLat)
```

### From a gram matrix

```@docs
genus(A::MatElem)
```

### Enumeration of genus symbols

```@docs
integer_genera(sig_pair::Tuple{Int,Int}, determinant::Union{Int,ZZRingElem})
```
### From other genus symbols
```@docs
direct_sum(G1::ZZGenus, G2::ZZGenus)
```

## Attributes of the genus

```@docs
dim(G::ZZGenus)
rank(G::ZZGenus)
signature(G::ZZGenus)
det(G::ZZGenus)
iseven(G::ZZGenus)
is_definite(G::ZZGenus)
level(G::ZZGenus)
scale(G::ZZGenus)
norm(G::ZZGenus)
primes(G::ZZGenus)
is_integral(G::ZZGenus)
```
### Discriminant group
[`discriminant_group(::ZZGenus)`](@ref)

### Primary genera
```docs
is_primary_with_prime(G::ZZGenus)
is_primary(G::ZZGenus, p::Union{Integer, ZZRingElem})
is_elementary_with_prime(G::ZZGenus)
is_elementary(G::ZZGenus, p::Union{Integer, ZZRingElem})
```

### local Symbol
```@docs
local_symbol(G::ZZGenus, p)
```

## Representative(s)

```@docs
quadratic_space(G::ZZGenus)
rational_representative(G::ZZGenus)
representative(G::ZZGenus)
representatives(G::ZZGenus)
mass(G::ZZGenus)
rescale(::ZZGenus, ::RationalUnion)
```

## Embeddings and Representations
```@docs
represents(G1::ZZGenus, G2::ZZGenus)
```

## Local genus Symbols

```@docs
LocalZZGenus
```

### Creation

```@docs
genus(L::ZZLat, p)
genus(A::ZZMatrix, p)
```

### Attributes
```@docs
prime(S::LocalZZGenus)
iseven(S::LocalZZGenus)
symbol(S::LocalZZGenus, scale::Int)
hasse_invariant(S::LocalZZGenus)
det(S::LocalZZGenus)
dim(S::LocalZZGenus)
rank(S::LocalZZGenus)
excess(S::LocalZZGenus)
signature(S::LocalZZGenus)
oddity(S::LocalZZGenus)
scale(S::LocalZZGenus)
norm(S::LocalZZGenus)
level(S::LocalZZGenus)
```
### Representative
```@docs
representative(S::LocalZZGenus)
gram_matrix(S::LocalZZGenus)
rescale(S::LocalZZGenus, a::RationalUnion)
```

### Direct sums
```@docs
direct_sum(S1::LocalZZGenus, S2::LocalZZGenus)
```

### Embeddings/Representations
```@docs
represents(G1::LocalZZGenus, G2::LocalZZGenus)
```

