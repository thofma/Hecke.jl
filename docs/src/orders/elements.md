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
parent(::AbsNumFieldOrderElem{AbsSimpleNumField, AbsSimpleNumFieldElem})
elem_in_nf(::AbsNumFieldOrderElem{AbsSimpleNumField, AbsSimpleNumFieldElem})
coordinates(::AbsNumFieldOrderElem{AbsSimpleNumField, AbsSimpleNumFieldElem})
discriminant(::Vector{AbsNumFieldOrderElem{AbsSimpleNumField, AbsSimpleNumFieldElem}})
==(::AbsNumFieldOrderElem{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::AbsNumFieldOrderElem{AbsSimpleNumField, AbsSimpleNumFieldElem})
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
representation_matrix(::AbsNumFieldOrderElem{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::AbsSimpleNumField)
tr(::NumFieldOrderElem)
norm(::NumFieldOrderElem)
absolute_norm(::AbsNumFieldOrderElem)
absolute_tr(::AbsNumFieldOrderElem)
rand(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::Int)
minkowski_map(::AbsNumFieldOrderElem{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::Int)
conjugates_arb(::AbsNumFieldOrderElem{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::Int)
conjugates_arb_log(::AbsNumFieldOrderElem{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::Int)
t2(::AbsNumFieldOrderElem{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::Int)
minpoly(::AbsNumFieldOrderElem{AbsSimpleNumField, AbsSimpleNumFieldElem})
charpoly(::AbsNumFieldOrderElem{AbsSimpleNumField, AbsSimpleNumFieldElem})
factor(::AbsNumFieldOrderElem{AbsSimpleNumField, AbsSimpleNumFieldElem})
denominator(a::NumFieldElem, O::RelNumFieldOrder)
discriminant(::Vector{AbsNumFieldOrderElem})
```

