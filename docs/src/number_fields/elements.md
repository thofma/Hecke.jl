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
    (L::NumberField)(c::Vector{NumFieldElem}) -> NumFieldElem
```

Given a number field $L/K$ of degree $d$ and a vector `c` length $d$, this constructs
the element `a` with `coordinates(a) == c`.

```jldoctest
julia> Qx, x = QQ["x"];

julia> K, a = NumberField(x^2 - 2, "a");

julia> K([1, 2])
2*a + 1

julia> L, b = radical_extension(3, a, "b")
(Relative number field over with defining polynomial x^3 - a
 over Number field over Rational Field with defining polynomial x^2 - 2, b)

julia> L([a, 1, 1//2])
1//2*b^2 + b + a
```


```@docs
quadratic_defect(a::NumFieldElem, p)
hilbert_symbol(a::nf_elem, b::nf_elem, p::Union{NfAbsOrdIdl, NfRelOrdIdl})
representation_matrix(::NumFieldElem)
basis_matrix(::Vector{nf_elem})
coefficients(::SimpleNumFieldElem)
coordinates(::NumFieldElem)
absolute_coordinates(::NumFieldElem)
coeff(::SimpleNumFieldElem, ::Int)
valuation(::NumFieldElem, ::Any)
torsion_unit_order(::nf_elem, ::Int)
tr(::NumFieldElem)
absolute_tr(::NumFieldElem)
algebraic_split(::nf_elem)
```

### Conjugates

```@docs
conjugates(::NumFieldElem, ::AcbField)
conjugates(::NumFieldElem)
conjugates_log(::nf_elem, ::Int)
conjugates_real(::nf_elem)
conjugates_complex(::nf_elem)
evaluate(::nf_elem, ::InfPlc)
conjugates_arb_log_normalise(::nf_elem)
minkowski_map(::nf_elem)
is_negative(::nf_elem, ::InfPlc)
```

### Predicates

```@docs
is_integral(::NumFieldElem)
is_torsion_unit(::nf_elem)
is_local_norm(::NumField, ::NumFieldElem, ::Any)
is_norm_divisible(::nf_elem, ::fmpz)
is_norm(::AnticNumberField, ::fmpz)
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
