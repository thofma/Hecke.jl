# Group algebras

```@meta
CurrentModule = Hecke
DocTestSetup = quote
  using Hecke
end
```

As is natural, the basis of a group algebra $K[G]$ correspond to the elements of $G$ with respect
to some arbitrary ordering.

## Creation

```@docs
group_algebra(::Field, ::Group)
```

Note that by default, this construction requires enumerating all elements of
the group and thus is inefficient for large groups. Using the optional argument `sparse = true`,
the algebra can be constructed with a different internal model. This allows for much larger groups,
but not all functionality is available in this case.

```jldoctest
julia> G = abelian_group([2 for i in 1:10]) # group of order 2^10
(Z/2)^10

julia> QG = group_algebra(QQ, G; sparse = true);
```

## Elements

Given a group algebra `A` and an element of a group `g`, the corresponding group algebra element
can be constructed using the syntax `A(g)`.

```jldoctest
julia> G = abelian_group([2, 2]); a = G([0, 1]);

julia> QG = group_algebra(QQ, G);

julia> x = QG(a)
[0, 0, 1, 0]
```

Vice versa, one can obtain the coefficient of a group algebra element `x` with respect to a group
element `a` using the syntax `x[a]`.

```jldoctest
julia> G = abelian_group([2, 2]); a = G([0, 1]);

julia> QG = group_algebra(QQ, G);

julia> x = QG(a)
[0, 0, 1, 0]

julia> x[a]
1
```

It is also possible to create elements from dictionaries:

```jldoctest
julia> G = abelian_group([2, 2]); a = G([0, 1]);

julia> QG = group_algebra(QQ, G);

julia> QG(Dict(a => 2, zero(G) => 1)) == 2 * QG(a) + 1 * QG(zero(G))
true
```
