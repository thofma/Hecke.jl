# Basics

```@meta
CurrentModule = Hecke
DocTestSetup = quote
  using Hecke
end
```

## Creation of algebras

See the corresponding sections in ?????
```@docs
zero_algebra(::Field)
```

## Basic properties

```@docs
base_ring(::Hecke.AbstractAssociativeAlgebra)
basis(::Hecke.AbstractAssociativeAlgebra)
```

## Predicates

```@docs
is_zero(::Hecke.AbstractAssociativeAlgebra)
is_commutative(::Hecke.AbstractAssociativeAlgebra)
is_central(::AbstractAssociativeAlgebra)
```

## Generators

```@docs
gens(::AbstractAssociativeAlgebra)
gens_with_data(::AbstractAssociativeAlgebra)
```

## Center

```@docs
center(::Hecke.AbstractAssociativeAlgebra)
dimension_of_center(::Hecke.AbstractAssociativeAlgebra)
dimension_over_center(::Hecke.AbstractAssociativeAlgebra)
```
