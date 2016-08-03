```@meta
CurrentModule = Hecke
```

## Creation

```@docs
Order(::Array{nf_elem, 1}, ::Bool)
Order(::AnticNumberField, ::FakeFmpqMat, ::Bool)
EquationOrder(::AnticNumberField)
```

### Example

```@repl
using Hecke;
Qx, x = PolynomialRing(QQ, "x");
K, a = NumberField(x^2 - 2, "a");
O = EquationOrder(K)
```

## Basic properties

```@docs
signature(::NfOrd)
```

```@docs
degree(::NfOrd)
```

## Elements

## Ideals


