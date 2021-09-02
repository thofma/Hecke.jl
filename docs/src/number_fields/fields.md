# Number field operations

```@meta
CurrentModule = Hecke
DocTestSetup = quote
  using Hecke
end
```

## Creation of number fields

General number fields can be created using the function `NumberField`, of which
`number_field` is an alias. To create a simple number field given by a defining
polynomial or a non-simple number field given by defining polynomials, the
following functions can be used.

```@docs
NumberField(::DocuDummy)
NumberField(::DocuDummy2)
```

!!! tip
    Many of the constructors have arguments of type `Symbol` or
    `AbstractString`.  If used, they define the appearance in printing, and
    printing only.  The named parameter `check` can be `true` or `false`, the
    default being `true`.  This parameter controls whether the polynomials
    defining the number field are tested for irreducibility or not. Given that
    this can be potentially very time consuming if the degree if large, one can
    disable this test. Note however, that the behaviour of Hecke is undefined
    if a reducible polynomial is used to define a *field*.

    The named boolean parameter `cached` can be used to disable caching. Two
    number fields defined using the same polynomial from the identical
    polynomial ring and the same (identical) symbol/string will be identical if
    `cached == true` and different if `cached == false`.


For frequently used number fields like quadratic fields, cyclotomic fields
or radical extensions, the following functions are provided:

```@docs
cyclotomic_field(n::Int)
quadratic_field(d::fmpz)
wildanger_field(n::Int, B::fmpz)
radical_extension(n::Int, a::NumFieldElem)
rationals_as_number_field()
```

## Basic properties

```@docs
basis(::SimpleNumField)
basis(::NonSimpleNumField)
absolute_basis(::NumField)
defining_polynomial(::SimpleNumField)
defining_polynomials(::NonSimpleNumField)
absolute_primitive_element(::NumField)
component(::NonSimpleNumField, ::Int)
base_field(::NumField)
```

## Invariants

```@docs
degree(::NumField)
absolute_degree(::NumField)
signature(::NumField)
unit_group_rank(::NumField)
class_number(::AnticNumberField)
relative_class_number(::AnticNumberField)
regulator(::AnticNumberField)
discriminant(::SimpleNumField)
absolute_discriminant(::SimpleNumField)
```

## Predicates

```@docs
issimple(::NumField)
isabsolute(::NumField)
istotally_real(::NumField)
istotally_complex(::NumField)
iscm_field(::NumField)
iskummer_extension(::SimpleNumField)
isradical_extension(::SimpleNumField)
islinearly_disjoint(::SimpleNumField, ::SimpleNumField)
isweakly_ramified(::AnticNumberField, ::NfOrdIdl)
istamely_ramified(::AnticNumberField)
istamely_ramified(::AnticNumberField, p::Int)
isabelian(::NumField)
```

### Subfields

```@docs
issubfield(::SimpleNumField, ::SimpleNumField)
subfields(::SimpleNumField)
principal_subfields(::SimpleNumField)
compositum(::AnticNumberField, ::AnticNumberField)
embedding(::NumField, ::NumField)
normal_closure(::AnticNumberField)
relative_simple_extension(::NumField, ::NumField)
issubfield_normal(::AnticNumberField, ::AnticNumberField)
```

## Conversion

```@docs
simplify(::AnticNumberField)
absolute_simple_field(K::NumField)
simple_extension(::NonSimpleNumField)
simplified_simple_extension(::NonSimpleNumField)
```

## Morphisms

```@docs
isisomorphic(::SimpleNumField, ::SimpleNumField)
isinvolution(::NfToNfMor)
fixed_field(::NumFieldMor)
automorphisms(::NumField)
automorphism_group(::AnticNumberField)
complex_conjugation(::AnticNumberField)
```

## Galois theory

```@docs
normal_basis(::NumField)
decomposition_group(::AnticNumberField, ::NfOrdIdl, ::Map)
ramification_group(::AnticNumberField, ::NfOrdIdl, ::Int, ::Map)
inertia_subgroup(::AnticNumberField, ::NfOrdIdl, ::Map)
```

## Infinite places

```@docs
infinite_places(K::NumField)
real_places(K::AnticNumberField)
complex_places(K::AnticNumberField)
isreal(::Plc)
iscomplex(::Plc)
infinite_places_uniformizers(::AnticNumberField)
```

## Miscellaneous

```@docs
norm_equation(::AnticNumberField, ::Any)
lorenz_module(::AnticNumberField, ::Int)
kummer_failure(::nf_elem, ::Int, ::Int)
isdefining_polynomial_nice(::AnticNumberField)
```
