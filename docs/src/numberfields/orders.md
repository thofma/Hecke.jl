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
using Hecke; # hide
Qx, x = PolynomialRing(QQ, "x");
K, a = NumberField(x^2 - 2, "a");
O = EquationOrder(K)
```

!!! note 
    Internally there is a difference between arbitary orders and maximal orders.
    An order will be treated as a maximal order, that is, as the ring of integers,
    if it was computed in the following way.

```@docs
maximal_order(::AnticNumberField)
maximal_order(::AnticNumberField, ::Array{fmpz, 1})
make_maximal(::NfOrd)
```

```@repl
using Hecke; # hide
Qx, x = PolynomialRing(QQ, "x");
K, a = NumberField(x^2 - 2, "a");
R = EquationOrder(K)
S = make_maximal(R)
T = maximal_order(K)
basis_mat(S) == basis_mat(T)
```

## Basic properties

```@docs
signature(::NfOrd)
```

```@docs
degree(::NfOrd)
```

```@docs
norm_change_const(::NfOrd)
```

## Elements

## Ideals


