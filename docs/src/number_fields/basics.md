## Creation of number fields

```@meta
CurrentModule = Hecke
```

### Creation of simple number fields
Number fields are mostly created using the function `NumberField`, of which
`number_field` is an alias. To create a simple number field, the following
functions can be used.

```@docs
NumberField(f::PolyElem{<:NumFieldElem}, s::String)
cyclotomic_field(n::Int)
wildanger_field(n::Int, B::fmpz)
radical_extension(n::Int, a::NumFieldElem)
```
---

Many of the constructors have arguments of type `Symbol` or `AbstractString`,
if used, they define the appearance in printing, and printing only.
The named parameter `check` can be `true` or `false`, the default being `true`.
This parameter controlls is the polynomial defining the number field is
tested for irreducibility or not. Given that this can be potentially 
very time consuming if the degree if large, one can disable this test. Note
however, that the behaviour of Hecke is undefined if a reducible polynomial
is used to define a *field*.

The named boolean parameter `cached` is inherited from the underlying Nemo
system. Two number fields defined using the same polynomial from the
identical polynomial ring and the same (identical) symbol/ string
will be identical if `cached == true` and different if `cached == false`.

#### Example

```@repl
using Hecke # hide
Qx, x = PolynomialRing(FlintQQ, "x");
K, a = NumberField(x^2 - 10, "a")
```

### Creation of non-simple number fields

```@docs
NumberField(::Vector{PolyElem{<:Union{NumFieldElem, fmpq}}}, ::String)
```
---

#### Example

```@repl
using Hecke # hide
Qx, x = PolynomialRing(FlintQQ, "x");
K, g = number_field([x^2-2, x^2-3, x^2-5])
g[1]^2
minpoly(g[1] + g[2])
```

### Conversion

```@docs
absolute_field(K::NumField)
```

```@docs
simple_extension(::NonSimpleNumField)
```

### Invariants

```@docs
basis(::SimpleNumField)
basis(::NonSimpleNumField)
issimple(::NumField)
isabsolute(::NumField)
degree(::NumField)
discriminant(::SimpleNumField)
absolute_discriminant(::SimpleNumField)
defining_polynomial(::SimpleNumField)
```
---

### Subfields

```@docs
issubfield(::SimpleNumField, ::SimpleNumField)
isisomorphic(::SimpleNumField, ::SimpleNumField)
```
---
