```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# Multi-sets and sub-set iterators


## Multi-sets

### Type and constructors

Objects of type `MSet` consists of a dictionary whose keys are the elements in
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

One can iterate over an `MSet` as on a regular `Set`. Here is moreover a list
of functions defined for collections of objects which are currently available
for `MSet`:

* `==`
* `all`
* `any`
* `copy`
* `delete!`
* `eltype`
* `filter`
* `filter!`
* `in`
* `intersect`
* `intersect!`
* `isempty`
* `issubset`
* `length`
* `pop!`
* `push!`
* `setdiff`
* `setdiff!`
* `similar`
* `unique`
* `union`
* `union!`
* ...

Note that `pop!` and `delete!` for `MSet` are available but have a different behaviour.
For an element `x` in an multi-set `M <: MSet`, then `pop!(M, x)` will remove
*one* instance of `x` in `M` - in particular `multiplicity(M, x)` will drop by
$1$. Much stronger, `delete!(M, x)` will remove *all* instances of `x` in `M` and
so `multiplicity(M, x)` will be $0$.

While `unique` will return the keys of the underlying dictionary, one can access
the values (i.e. the multiplicities of the elements in the multi-set) via the
following functions:

```@docs
multiplicities(::MSet)
multiplicity(::MSet{T}, ::T) where {T}
```

Finally, the sum and difference for `MSet` are also available. Difference is
given by the complements of sets and the sum is given by disjoint union of sets.

```@docs
Base.:(+)(::MSet, ::MSet)
Base.:(-)(::MSet, ::MSet...)
```

## Subset iterators for sets and multisets

```@docs
subsets(::MSet{T}) where {T}
```

### Sub-sets of a given size

```@docs
subsets(::Set{T}, ::Int64) where {T}
```
