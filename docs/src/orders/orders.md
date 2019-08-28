# Orders
```@meta
CurrentModule = Hecke
```

Orders, ie. unitary subrings that are free $Z$-modules of rank
equal to the degree of the number field, are at the core of the
arithmetic of number fields. In Hecke, orders are always represented
using the module structure, be it the $Z$-module structure for orders
in absolute fields, of the structure as a module over the
maximal order of the base field in the case of relative extensions.
In this chapter we only deal with orders in absolute fields.
There are more general definitions of orders in number fields
available, but those are (currently) not implemented in Hecke.

Among all orders in a fixed field, there is a unique maximal one,
called the maximal order, or ring of integers of the field.
It is well known that this is the only order that is a Dedekind
domain, hence has a rich ideal structure as well.
The maximal order is also the integral closure of $Z$ in the number field
and can also be interpreted as a normalisation of any other order.

## Creation and basic properties

```@docs
Order(::AnticNumberField, ::Array{nf_elem, 1})
Order(::AnticNumberField, ::FakeFmpqMat)
Order(::NfOrdFracIdl)
EquationOrder(::AnticNumberField)
MaximalOrder(::AnticNumberField)
MaximalOrder(::NfOrd)
maximal_order(::AnticNumberField)
lll(::NfOrd)
```

By Chistov's fundamental theorem, the computation of the maximal order
is basically as hard as the factorisation of the discriminant. In order to
help the computer, Hecke also provides the following signatures:

```@docs
maximal_order(::AnticNumberField, ::Array{fmpz, 1})
```

It is also possible the execute the steps individually:

```@docs
pradical(::NfOrd, ::fmpz)
ring_of_multipliers(::NfOrdIdl)
```

### Example

```@repl
using Hecke; # hide
Qx, x = PolynomialRing(FlintQQ, "x");
K, a = NumberField(x^2 - 2, "a");
O = EquationOrder(K)
```

```@docs
parent(::NfOrd)
isequation_order(::NfOrd)
signature(::NfOrd)
nf(::NfOrd)
degree(::NfOrd)
basis(::NfOrd)
basis(::NfOrd, ::AnticNumberField)
basis_matrix(::NfOrd)
basis_mat_inv(::NfOrd)
discriminant(::NfOrd)
gen_index(::NfOrd)
index(::NfOrd)
isindex_divisor(::NfOrd, ::fmpz)
minkowski_mat(::NfOrd, ::Int)
in(::nf_elem, ::NfOrd)
denominator(::nf_elem, ::NfOrd)
norm_change_const(::NfOrd)
trace_matrix(::NfOrd)
+(::NfOrd, ::NfOrd)
poverorder(::NfOrd, ::fmpz)
pmaximal_overorder(::NfOrd, ::fmpz)
```

