# Fractional ideals
```@meta
CurrentModule = Hecke
```


A fractional ideal in the number field $K$ is a $Z_K$-module $A$
such that there exists an integer $d>0$ which $dA$ is an (integral) ideal
in $Z_K$. Due to the Dedekind property of $Z_K$, the ideals for a
multiplicative group.

Fractional ideals are represented as an integral ideal and an additional
denominator. They are of type `AbsSimpleNumFieldOrderFractionalIdeal`.

## Creation

```@docs; canonical=false
fractional_ideal(::AbsSimpleNumFieldOrder, ::ZZMatrix)
fractional_ideal(::AbsSimpleNumFieldOrder, ::ZZMatrix, ::ZZRingElem)
fractional_ideal(::AbsSimpleNumFieldOrder, ::QQMatrix)
fractional_ideal(::AbsSimpleNumFieldOrder, ::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
fractional_ideal(::AbsSimpleNumFieldOrder, ::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::ZZRingElem)
fractional_ideal(::AbsSimpleNumFieldOrder, ::AbsSimpleNumFieldElem)
fractional_ideal(::AbsSimpleNumFieldOrder, ::AbsSimpleNumFieldOrderElem)
inv(::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
```

## Arithmetic

All the normal operations are provided as well.

```@docs; canonical=false
inv(::AbsSimpleNumFieldOrderFractionalIdeal)
integral_split(::AbsSimpleNumFieldOrderFractionalIdeal)
numerator(::RelNumFieldOrderFractionalIdeal)
denominator(::RelNumFieldOrderFractionalIdeal)
```

## Miscaellenous

```@docs; canonical=false
order(::AbsSimpleNumFieldOrderFractionalIdeal)
basis_matrix(::AbsSimpleNumFieldOrderFractionalIdeal)
basis_mat_inv(::AbsSimpleNumFieldOrderFractionalIdeal)
basis(::AbsSimpleNumFieldOrderFractionalIdeal)
norm(::AbsSimpleNumFieldOrderFractionalIdeal)
```

