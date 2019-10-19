# Quadratic and hermitian lattices 
```@meta
CurrentModule = Hecke
```

## Creation of lattices

```@docs
quadratic_lattice(::NumField, ::MatElem; gram_ambient_space = nothing)
quadratic_lattice(::NumField, ::PMat; gram_ambient_space = nothing)
hermitian_lattice(::NumField, ::MatElem; gram_ambient_space = nothing)
hermitian_lattice(::NumField, ::PMat; gram_ambient_space = nothing)
```
---

## Basic invariants

```@docs
ambient_space(L::AbsLat)
rational_span(::AbsLat)
diagonal(L::AbsLat)
fixed_field(L::AbsLat)
involution(::AbsLat)
rank(L::AbsLat)
degree(L::AbsLat)
gram_matrix_of_basis(L::AbsLat)
generators(L::AbsLat; minimal::Bool = false)
discriminant(L::AbsLat)
pseudo_matrix(L::AbsLat)
coefficient_ideals(L::AbsLat)
basis_matrix(L::AbsLat)
absolute_basis(L::AbsLat)
absolute_basis_matrix(L::AbsLat)
```
---

## Rational invariants

```@docs
hasse_invariant(L::QuadLat, p)
witt_invariant(L::QuadLat, p::NfAbsOrdIdl)
isrationally_equivalent(::AbsLat, ::AbsLat, ::NfAbsOrdIdl)
isrationally_equivalent(L::AbsLat, M::AbsLat)
```
---

## Definiteness

```@docs
ispositive_definite(L::AbsLat)
isnegative_definite(L::AbsLat)
isdefinite(L::AbsLat)
can_scale_totally_positive(L::AbsLat)
```
---

## Module operations

```@docs
Base.:(+)(::AbsLat, M::AbsLat)
intersect(L::AbsLat, M::AbsLat)
Base.:(*)(::NumFieldElem, ::AbsLat)
Base.:(*)(::NfOrdIdl, ::AbsLat)
Base.:(*)(::NfOrdFracIdl, ::AbsLat)
rescale(::AbsLat, ::NumFieldElem)
dual(::AbsLat)
```
---

## Invariants

```@docs
norm(::AbsLat)
scale(L::AbsLat)
isintegral(L::AbsLat)
volume(L::AbsLat)
ismodular(L::AbsLat)
```
---

## Local properties

```@docs
local_basis_matrix(L::AbsLat, p; type::Symbol = :any)
ismodular(L::AbsLat, p)
bad_primes(L::AbsLat; even::Bool = false)
jordan_decomposition(L::AbsLat, p::NfOrdIdl)
islocally_isometric(::AbsLat, ::AbsLat, ::NfOrdIdl)
```
---

## Genera

# Creation of genera from lattices

```@docs
genus(L::HermLat, p)
genus(L::HermLat)
```
---

# Properties of genera

```@docs
rank(G::LocalGenusHerm)
rank(G::LocalGenusHerm, i::Int)
ranks(G::LocalGenusHerm)
det(G::LocalGenusHerm)
det_representative(G::LocalGenusHerm)
gram_matrix(G::LocalGenusHerm)
gram_matrix(G::LocalGenusHerm, i::Int)
primes(G::GenusHerm)
```
---

# Check if lattice is contained in genus

```@docs
Base.in(L::HermLat, G::LocalGenusHerm)
Base.in(L::HermLat, G::GenusHerm)
```
---

# Creating representatives

```@docs
representative(G::LocalGenusHerm)
```
