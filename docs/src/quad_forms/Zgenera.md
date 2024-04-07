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

```@docs; canonical=false
ZZGenus
```

## Creation of Genera

### From an integral Lattice

```@docs; canonical=false
genus(::ZZLat)
```

### From a gram matrix

```@docs; canonical=false
genus(A::MatElem)
```

### Enumeration of genus symbols

```@docs; canonical=false
integer_genera(sig_pair::Tuple{Int,Int}, determinant::Union{Int,ZZRingElem})
```
### From other genus symbols
```@docs; canonical=false
direct_sum(G1::ZZGenus, G2::ZZGenus)
```

## Attributes of the genus

```@docs; canonical=false
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

```@docs; canonical=false
is_primary_with_prime(G::ZZGenus)
is_primary(G::ZZGenus, p::Union{Integer, ZZRingElem})
is_elementary_with_prime(G::ZZGenus)
is_elementary(G::ZZGenus, p::Union{Integer, ZZRingElem})
```

### local Symbol
```@docs; canonical=false
local_symbol(G::ZZGenus, p)
```

## Representative(s)

```@docs; canonical=false
quadratic_space(G::ZZGenus)
rational_representative(G::ZZGenus)
representative(G::ZZGenus)
representatives(G::ZZGenus)
mass(G::ZZGenus)
rescale(::ZZGenus, ::RationalUnion)
```

## Embeddings and Representations
```@docs; canonical=false
represents(G1::ZZGenus, G2::ZZGenus)
```

## Local genus Symbols

```@docs; canonical=false
ZZLocalGenus
```

### Creation

```@docs; canonical=false
genus(::ZZLat, ::IntegerUnion)
genus(::QQMatrix, ::IntegerUnion)
```

### Attributes
```@docs; canonical=false
prime(S::ZZLocalGenus)
iseven(S::ZZLocalGenus)
symbol(S::ZZLocalGenus, scale::Int)
hasse_invariant(S::ZZLocalGenus)
det(S::ZZLocalGenus)
dim(S::ZZLocalGenus)
rank(S::ZZLocalGenus)
excess(S::ZZLocalGenus)
signature(S::ZZLocalGenus)
oddity(S::ZZLocalGenus)
scale(S::ZZLocalGenus)
norm(S::ZZLocalGenus)
level(S::ZZLocalGenus)
```
### Representative
```@docs; canonical=false
representative(S::ZZLocalGenus)
gram_matrix(S::ZZLocalGenus)
rescale(S::ZZLocalGenus, a::RationalUnion)
```

### Direct sums
```@docs; canonical=false
direct_sum(S1::ZZLocalGenus, S2::ZZLocalGenus)
```

### Embeddings/Representations
```@docs; canonical=false
represents(G1::ZZLocalGenus, G2::ZZLocalGenus)
```

