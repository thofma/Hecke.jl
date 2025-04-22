```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# [Quaternion algebras](@id quat-alg)


We provide a model for quaternion algebras over a field $K$ in *standard form*, which is
parametrized by two elements $a, b \in K$.
The corresponding quaternion algebra has a basis $1, i, j, k$ satisfying $i^2 = a$, $j^2 = b$ and $ij = -ji = k$.

This functionality is currently restricted to fields of characteristic not equal to two.

## Creation

```@docs
quaternion_algebra(::Field, ::Any, ::Any)
```

## Arithmetic of elements

```@docs
conjugate(a::AssociativeAlgebraElem)
```

```@docs; canonical=false
trred(::AbstractAssociativeAlgebraElem)
normred(::Hecke.AbstractAssociativeAlgebraElem{T}) where {T}
reduced_charpoly(::AbstractAssociativeAlgebraElem)
```

### Example

```jldoctest
julia> Q = quaternion_algebra(QQ, -1, -1)
Quaternion algebra
  over rational field
  defined by i^2 = -1, j^2 = -1

julia> z = Q([1, 2, 0, 1//3])
1 + 2*i + 1//3*k

julia> trred(z)
2

julia> normred(z)
46//9

julia> reduced_charpoly(z)
x^2 - 2*x + 46//9

julia> m = reduced_charpoly(z)
x^2 - 2*x + 46//9

julia> m(z)
0
```

## Splitting of quaternion algebras

```@docs
is_split_with_zero_divisor
```

