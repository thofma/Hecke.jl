```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# Basics


## Creation of algebras

See the corresponding sections on [structure constant algebras](@ref SCA), [group algebras](@ref group-alg) and [quaternion algebras](@ref quat-alg).

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

## Creation of elements

Elements of algebras can be constructed by arithmetic with basis elements, generators or by providing coordinates.

```jldoctest
julia> Q = quaternion_algebra(QQ, -1, -1)
Quaternion algebra
  over rational field
  defined by i^2 = -1, j^2 = -1

julia> B = basis(Q);

julia> x = B[1] + B[2] + 1//3 * B[4]
1 + i + 1//3*k

julia> Q([1, 1, 0, 1//3])
1 + i + 1//3*k
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
