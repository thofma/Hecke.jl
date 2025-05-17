```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# Maps
Maps between abelian groups are mainly of type `FinGenAbGroupHom`. They
allow normal map operations such as `image`, `preimage`, `domain`, `codomain`
and can be created in a variety of situations.

Maps between abelian groups can be constructed via
 - images of the generators
 - pairs of elements
 - via composition
 - and isomorphism/ inclusion testing

```@docs
hom_direct_sum(G::FinGenAbGroup, H::FinGenAbGroup, A::Matrix{ <: Map{FinGenAbGroup, FinGenAbGroup}})
is_isomorphic(G::FinGenAbGroup, H::FinGenAbGroup)
```

```jldoctest
julia> G = free_abelian_group(2)
Z^2

julia> h = hom(G, G, [gen(G, 2), 3*gen(G, 1)])
Map
  from Z^2
  to Z^2

julia> h(gen(G, 1))
Abelian group element [0, 1]

julia> h(gen(G, 2))
Abelian group element [3, 0]
```

Homomorphisms also allow addition and subtraction corresponding to the
pointwise operation:
```jldoctest
julia> G = free_abelian_group(2)
Z^2

julia> h = hom(G, G, [2*gen(G, 2), 3*gen(G, 1)])
Map
  from Z^2
  to Z^2

julia> (h+h)(gen(G, 1))
Abelian group element [0, 4]
```

