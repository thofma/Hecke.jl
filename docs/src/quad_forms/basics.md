# Basics 
```@meta
CurrentModule = Hecke
```

## Creation of spaces

```@docs
quadratic_space(::NumField, ::Int)
quadratic_space(::NumField, ::MatElem)
```

## Attributes

```@docs
rank(::AbsSpace)
dim(::AbsSpace)
gram_matrix(::AbsSpace)
base_field(::AbsSpace)
involution(::AbsSpace)
isregular(::AbsSpace)
det(::AbsSpace)
discriminant(::AbsSpace)
```

## Inner products and diagonalization

```@docs
gram_matrix(::AbsSpace{T}, ::MatElem{S}) where {S, T}
gram_matrix(::AbsSpace{T}, ::Vector{Vector{U}}) where {T, U}
inner_product(::AbsSpace, ::Vector, ::Vector)
orthogonal_basis(::AbsSpace)
diagonal(::AbsSpace)
```

## Equivalence
```@docs
hasse_invariant(::QuadSpace, p)
witt_invariant(::QuadSpace, p)
isequivalent(::AbsSpace, ::AbsSpace, p)
invariants(::QuadSpace)
isequivalent(::QuadSpace, ::QuadSpace)
```
