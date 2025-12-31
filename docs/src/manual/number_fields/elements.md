```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# Element operations

## Creation

We can return the generator $\alpha$ of a simple extension $K(\alpha)/K$ and the vector of generators $\alpha_1, ..., \alpha_n$ of a nonsimple extension $K(\alpha_1, ..., \alpha_n)/K$ with the following.

```@docs
gen(::SimpleNumField)
gens(::NonSimpleNumField)
```

Elements can also be created by specifying the coordinates with respect to the basis of the number field:

```julia
(L::number_field)(c::Vector{NumFieldElem}) -> NumFieldElem
```

Given a number field $L/K$ of degree $d$ and a vector `c` of elements from $K$ of length $d$, the above method constructs the element `a` with `coordinates(a) == c`.

```jldoctest
julia> Qx, x = QQ["x"];

julia> K, a = number_field(x^2 - 2, "a");

julia> basis(K)
2-element Vector{AbsSimpleNumFieldElem}:
 1
 a

julia> K([1, 2])
2*a + 1

julia> L, b = radical_extension(3, a, "b")
(Relative number field of degree 3 over K, b)

julia> basis(L)
3-element Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}:
 1
 b
 b^2

julia> L([a, 1, 1//2])
1//2*b^2 + b + a
```

Conversely, given an element $x$ of a number field $K$, we can extract the coordinates of $x$ under various bases.


```@docs
coordinates(::NumFieldElem)
absolute_coordinates(::NumFieldElem)
coefficients(::SimpleNumFieldElem)
coeff(::SimpleNumFieldElem, ::Int)
```
## Functions on elements

The following are groups of functions that take as input an element of a number field.

### Basis Dependent

Functions that depend on a basis:

```@docs
representation_matrix(::NumFieldElem)
basis_matrix(::Vector{AbsSimpleNumFieldElem})
```

### Invariants

Common invariants of an element:

```@docs
norm(::NumFieldElem)
absolute_norm(::NumFieldElem)
norm(::NumFieldElem, ::NumField)
tr(::NumFieldElem)
absolute_tr(::NumFieldElem)
minpoly(::NumFieldElem)
absolute_minpoly(::NumFieldElem)
charpoly(::NumFieldElem)
absolute_charpoly(::NumFieldElem)
```

### Predicates

```@docs
is_integral(::NumFieldElem)
is_torsion_unit(::AbsSimpleNumFieldElem)
is_local_norm(::NumField, ::NumFieldElem, ::Any)
is_norm_divisible(::AbsSimpleNumFieldElem, ::ZZRingElem)
is_norm(::AbsSimpleNumField, ::ZZRingElem)
```
### Conjugates

```@docs
conjugates(::NumFieldElem, ::AcbField)
conjugates(::NumFieldElem)
conjugates_log(::AbsSimpleNumFieldElem, ::Int)
conjugates_real(::AbsSimpleNumFieldElem)
conjugates_complex(::AbsSimpleNumFieldElem)
conjugates_arb_log_normalise(::AbsSimpleNumFieldElem)
minkowski_map(::AbsSimpleNumFieldElem)
```

### Miscellaneous

```@docs
quadratic_defect(a::NumFieldElem, p)
hilbert_symbol(a::AbsSimpleNumFieldElem, b::AbsSimpleNumFieldElem, p::Union{AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal})
valuation(::NumFieldElem, ::Any)
torsion_unit_order(::AbsSimpleNumFieldElem, ::Int)
algebraic_split(::AbsSimpleNumFieldElem)
```
