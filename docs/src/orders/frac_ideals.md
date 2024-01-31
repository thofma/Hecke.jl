# Fractional ideals
```@meta
CurrentModule = Hecke
```


A fractional ideal in the number field $K$ is a $Z_K$-module $A$
such that there exists an integer $d>0$ which $dA$ is an (integral) ideal
in $Z_K$. Due to the Dedekind property of $Z_K$, the ideals for a
multiplicative group.

Fractional ideals are represented as an integral ideal and an additional
denominator. They are of type `AbsNumFieldOrderFractionalIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}`.

## Creation

```@docs
fractional_ideal(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::ZZMatrix)
fractional_ideal(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::ZZMatrix, ::ZZRingElem)
fractional_ideal(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::FakeFmpqMat)
fractional_ideal(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
fractional_ideal(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::ZZRingElem)
fractional_ideal(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::AbsSimpleNumFieldElem)
fractional_ideal(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::AbsNumFieldOrderElem{AbsSimpleNumField, AbsSimpleNumFieldElem})
inv(::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
```

## Arithmetic

All the normal operations are provided as well.

```@docs
inv(::AbsNumFieldOrderFractionalIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
integral_split(::AbsNumFieldOrderFractionalIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
numerator(::RelNumFieldOrderFractionalIdeal)
denominator(::RelNumFieldOrderFractionalIdeal)
```

## Miscaellenous

```@docs
order(::AbsNumFieldOrderFractionalIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
basis_matrix(::AbsNumFieldOrderFractionalIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
basis_mat_inv(::AbsNumFieldOrderFractionalIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
basis(::AbsNumFieldOrderFractionalIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
norm(::AbsNumFieldOrderFractionalIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
```

