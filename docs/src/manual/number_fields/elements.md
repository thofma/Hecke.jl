```@meta
CurrentModule = Hecke
DocTestSetup = quote
    using Hecke
  end
```

# Element operations

## Creation

```@docs
gen(::SimpleNumField)
gens(::NonSimpleNumField)
```

Elements can also be created by specifying the coordinates with respect to the
basis of the number field:

```julia
    (L::number_field)(c::Vector{NumFieldElem}) -> NumFieldElem
```

Given a number field $L/K$ of degree $d$ and a vector `c` length $d$, this constructs
the element `a` with `coordinates(a) == c`.

```jldoctest
julia> Qx, x = QQ["x"];

julia> K, a = number_field(x^2 - 2, "a");

julia> K([1, 2])
2*a + 1

julia> L, b = radical_extension(3, a, "b")
(Relative number field of degree 3 over number field, b)

julia> L([a, 1, 1//2])
1//2*b^2 + b + a
```


```@docs
quadratic_defect(a::NumFieldElem, p)
hilbert_symbol(a::AbsSimpleNumFieldElem, b::AbsSimpleNumFieldElem, p::Union{AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal})
representation_matrix(::NumFieldElem)
basis_matrix(::Vector{AbsSimpleNumFieldElem})
coefficients(::SimpleNumFieldElem)
coordinates(::NumFieldElem)
absolute_coordinates(::NumFieldElem)
coeff(::SimpleNumFieldElem, ::Int)
valuation(::NumFieldElem, ::Any)
torsion_unit_order(::AbsSimpleNumFieldElem, ::Int)
tr(::NumFieldElem)
absolute_tr(::NumFieldElem)
algebraic_split(::AbsSimpleNumFieldElem)
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

### Predicates

```@docs
is_integral(::NumFieldElem)
is_torsion_unit(::AbsSimpleNumFieldElem)
is_local_norm(::NumField, ::NumFieldElem, ::Any)
is_norm_divisible(::AbsSimpleNumFieldElem, ::ZZRingElem)
is_norm(::AbsSimpleNumField, ::ZZRingElem)
```

### Invariants

```@docs
norm(::NumFieldElem)
absolute_norm(::NumFieldElem)
minpoly(::NumFieldElem)
absolute_minpoly(::NumFieldElem)
charpoly(::NumFieldElem)
absolute_charpoly(::NumFieldElem)
norm(::NumFieldElem, ::NumField)
```
