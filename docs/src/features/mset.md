# Multi-sets and sub-set iterators

```@meta
CurrentModule = Hecke
DocTestSetup = quote
    using Hecke
end
```

## Multi-sets

### Type and constructors

Objects of type `Mset` consists of a dictionary whose keys are the elements in
the set, and the values are their respective multiplicity.

```@docs
MSet
```

We can create multi-sets from any finite iterator, dictionary or pair of lists
with the appropriate conditions.

```@docs
multiset
```

### Functions

Existing functions for any collection of objects which are currently available
for `MSet`:

* `similar`
* `isempty`
* `length`
* `eltype`
* `push!`
* `copy`
* `==`
* `unique`

One can also iterate over an `MSet`, and use `filter` for a given predicate on
the keys of the underlying dictionary (not on their values!). One can also test
containment.

While `unique` will return the keys of the underlying dictionary, one can access
the values (i.e. the multiplicities of the elements in the multi-set) via the
following functions:

```@docs
multiplicities(::MSet)
multiplicity(::MSet{T}, ::T) where T
```

Note that `pop!` and `delete!` for `MSet` are available but have a different behaviour.
For an element `x` in an multi-set `M <: MSet`, then `pop!(M, x)` will remove
*one* instance of `x` in `M` - in particular `multiplicity(M, x)` will drop by
$1$. Much stronger, `delete!(M, x)` will remove *all* instances of `x` in `M` and
so `multiplicity(M, x)` will be $0$.

Finally, one can take unions (`union`, `union!`) of an `MSet` with other
finite collections of objects. Note that `union!` will require coercion of
elements. Similarly, one can compare an `MSet` with another collection with the
`setdiff/setdiff!` functions.

## Sub-set iterators

### Sub-multi-sets

```@docs
subsets(::MSet{Int})
```

### Sub-sets

```@docs
subsets(::Set{Int})
```

### Sub-sets of a given size

```@docs
subsets(::Set, ::Int)
```
