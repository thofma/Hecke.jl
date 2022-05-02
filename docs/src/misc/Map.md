# Map from julia functions

For the situation where it is desirable to create a `Map` given arbitrary
callable julia objects (like anonymous functions), the type `MapFromFunc` is provided.

```@docs
MapFromFunc
```

!!! note
    When applying an object `f` of type  `MapFromFunc` to an element `x`, it
    will be checked whether the parent of `x` coincides with the domain and
    whether the parent of `f(x)` coincides with the codomain of `f`. Similar
    for the optional preimage function.
