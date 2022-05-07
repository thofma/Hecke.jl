Maps between abelian groups are mainly of type `GrpAbFinGenMap`. They
allow normal map operations such as `image`, `preimage`, `domain`, `codomain`
and can be created in a variety of situations.
## Maps
Maps between abelian groups can be constructed via
 - images of the generators
 - pairs of elements
 - via composition
 - and isomorphism/ inclusion testing

```@docs
hom(G::GrpAbFinGen, H::GrpAbFinGen, A::Matrix{ <: Map{GrpAbFinGen, GrpAbFinGen}})
is_isomorphic(G::GrpAbFinGen, H::GrpAbFinGen)
```

```@repl
using Hecke # hide
G = free_abelian_group(2)
h = hom(G, G, [gen(G, 2), 3*gen(G, 1)])
h(gen(G, 1))
h(gen(G, 2))
```

Homomorphisms also allow addition and subtraction corresponding to the
pointwise operation:
```@repl
using Hecke # hide
G = free_abelian_group(2)
h = hom(G, G, [2*gen(G, 2), 3*gen(G, 1)])
(h+h)(gen(G, 1))
```

