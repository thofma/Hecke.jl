```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# [Group algebras](@id group-alg)


As is natural, the basis of a group algebra $K[G]$ correspond to the elements of $G$ with respect
to some arbitrary ordering.

## Creation

```@docs
group_algebra(::Field, ::Group)
```

## Elements

Given a group algebra `A` and an element of a group `g`, the corresponding group algebra element
can be constructed using the syntax `A(g)`.

```jldoctest grpalgex1
julia> G = abelian_group([2, 2]); a = G([0, 1]);

julia> QG = group_algebra(QQ, G);

julia> x = QG(a)
[0, 0, 1, 0]
```

Vice versa, one can obtain the coordinate of a group algebra element `x` with respect to a group
element `a` using the syntax `x[a]`.

```jldoctest grpalgex1
julia> x[a]
1
```

It is also possible to create elements by specifying for each group element the corresponding coordinate either by a list of pairs or a dictionary:

```jldoctest grpalgex1
julia> QG(a => 2, zero(G) => 1) == 2 * QG(a) + 1 * QG(zero(G))
true

julia> QG(Dict(a => 2, zero(G) => 1)) == 2 * QG(a) + 1 * QG(zero(G))
true
```
