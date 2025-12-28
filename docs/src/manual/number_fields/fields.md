```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# Number field operations

## Creation of number fields

Number fields can be created using the `number_field` function.

To create a simple number field, one passes the defining polynomial directly to `number_field`. This returns the corresponding extension and a generator.

To create a non-simple number field, one passes a vector of defining polynomials to `number_field`. This returns the extension and a vector of generators.

```@docs
number_field(::DocuDummy)
number_field(::DocuDummy2)
```

!!! tip
    Many of the constructors here have an argument of type `VarName`.
    If this argument is used, it determines the appearance in printing and
    printing only.

    The named argument `check` can be set to `true` or `false` with the
    default being `true`. This parameter controls whether or not the extension
    defined by the given inputs is a field. Given that
    this can be potentially very time consuming if the degree is large, one can
    disable this test. Note, however, that the behaviour of Hecke is undefined
    if a reducible polynomial is used to define a *field*.

    The named boolean argument `cached` can be used to disable caching. Two
    number fields defined using the same polynomial from the identical
    polynomial ring and the same (identical) symbol/string will be identical if
    `cached == true` and different if `cached == false`.


For frequently used number fields like quadratic fields, cyclotomic fields
or radical extensions, the following functions are provided:

```@docs
cyclotomic_field(n::Int)
quadratic_field(d::ZZRingElem)
wildanger_field(n::Int, B::ZZRingElem)
radical_extension(n::Int, a::NumFieldElem)
```

Occasionally, algorithms written with Hecke may be written specifically to target generic number fields.
The default implementation of the rational numbers `QQ` utilizes a specialized wrapper for the FLINT `fmpq_t` type and is not implemented as a generic number field.
For cases of compatibility, we also provide a method for considering the rationals as a generic number field.

```@docs
rationals_as_number_field()
splitting_field
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
class_number(::AbsSimpleNumField)
relative_class_number(::AbsSimpleNumField)
regulator(::AbsSimpleNumField)
discriminant(::SimpleNumField)
absolute_discriminant(::SimpleNumField)
```

## Predicates

```@docs
is_simple(::NumField)
is_absolute(::NumField)
is_totally_real(::NumField)
is_totally_complex(::NumField)
is_cm_field(::NumField)
is_kummer_extension(::SimpleNumField)
is_radical_extension(::SimpleNumField)
is_linearly_disjoint(::SimpleNumField, ::SimpleNumField)
is_weakly_ramified(::AbsSimpleNumField, ::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
is_tamely_ramified(::AbsSimpleNumField)
is_tamely_ramified(::AbsSimpleNumField, p::Int)
is_abelian(::NumField)
```

### Subfields

```@docs
is_subfield(::SimpleNumField, ::SimpleNumField)
subfields(::SimpleNumField)
principal_subfields(::SimpleNumField)
compositum(::AbsSimpleNumField, ::AbsSimpleNumField)
embedding(::NumField, ::NumField)
normal_closure(::AbsSimpleNumField)
relative_simple_extension(::NumField, ::NumField)
is_subfield_normal(::AbsSimpleNumField, ::AbsSimpleNumField)
```

## Conversion

```@docs
simplify(::AbsSimpleNumField)
absolute_simple_field(K::NumField)
simple_extension(::NonSimpleNumField)
simplified_simple_extension(::NonSimpleNumField)
```

## Morphisms

```@docs
is_isomorphic(::SimpleNumField, ::SimpleNumField)
is_isomorphic_with_map(::SimpleNumField, ::SimpleNumField)
is_involution(::NumFieldHom{AbsSimpleNumField, AbsSimpleNumField})
fixed_field(::NumFieldHom)
automorphism_list(::NumField)
automorphism_group(::AbsSimpleNumField)
automorphism_group(::NumField, ::NumField)
complex_conjugation(::AbsSimpleNumField)
```

## Galois theory

```@docs
normal_basis(::NumField)
decomposition_group(::AbsSimpleNumField, ::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::Map)
ramification_group(::AbsSimpleNumField, ::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::Int, ::Map)
inertia_subgroup(::AbsSimpleNumField, ::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::Map)
```

## Infinite places

```@docs
infinite_places(K::NumField)
real_places(K::AbsSimpleNumField)
complex_places(K::AbsSimpleNumField)
is_real(::Plc)
is_complex(::Plc)
```

## Miscellaneous

```@docs
norm_equation(::AbsSimpleNumField, ::Any)
lorenz_module(::AbsSimpleNumField, ::Int)
kummer_failure(::AbsSimpleNumFieldElem, ::Int, ::Int)
is_defining_polynomial_nice(::AbsSimpleNumField)
```
