# Elements
```@meta
CurrentModule = Hecke
```


Elements in orders have two representations: they can be viewed as
elements in the $\mathbf Z^n$ giving the coefficients wrt to the order basis
where they are elements in. On the other hand, as every order is
in a field, they also have a representation as number field elements.
Since, asymptotically, operations are more efficient in the
field (due to fast polynomial arithmetic) than in the order, the primary
representation is that as a field element.

## Creation

Elements are constructed either as linear combinations of basis elements
or via explicit coercion. Elements will be of type `AbsNumFieldOrderElem`,
the type if actually parametrized by the type of the surrounding field and
the type of the field elements. E.g. the type of any element in any
order of an absolute simple field will be
`AbsNumFieldOrderElem{AbsSimpleNumField,AbsSimpleNumFieldElem}`


```@docs
AbsNumFieldOrder
```

## Basic properties

```@docs
parent(::NfOrdElem)
elem_in_nf(::NfOrdElem)
coordinates(::NfOrdElem)
discriminant(::Vector{NfOrdElem})
==(::NfOrdElem, ::NfOrdElem)
```

## Arithmetic

All the usual arithmetic operatinos are defined:

- `-(::NUmFieldOrdElem)`
- `+(::NumFieldOrderElem, ::NumFieldOrderElem)`
- `-(::NumFieldOrderElem, ::NumFieldOrderElem)`
- `*(::NumFieldOrderElem, ::NumFieldOrderElem)`
- `^(::NumFieldOrderElem, ::Int)`
- `mod(::AbsNumFieldOrderElem, ::Int)`
- `mod_sym(::NumFieldOrderElem, ::ZZRingElem)`
- `powermod(::AbsNumFieldOrderElem, ::ZZRingElem, ::Int)`

## Miscellaneous

```@docs
representation_matrix(::AbsNumFieldOrderElem)
representation_matrix(::NfOrdElem, ::AbsSimpleNumField)
tr(::NumFieldOrderElem)
norm(::NumFieldOrderElem)
absolute_norm(::AbsNumFieldOrderElem)
absolute_tr(::AbsNumFieldOrderElem)
rand(::NfOrd, ::Int)
minkowski_map(::NfOrdElem, ::Int)
conjugates_arb(::NfOrdElem, ::Int)
conjugates_arb_log(::NfOrdElem, ::Int)
t2(::NfOrdElem, ::Int)
minpoly(::NfOrdElem)
charpoly(::NfOrdElem)
factor(::NfOrdElem)
denominator(a::NumFieldElem, O::RelNumFieldOrder)
discriminant(::Vector{AbsNumFieldOrderElem})
```

