# (Absolute) Orders
```@meta
CurrentModule = Hecke
```

Orders, ie. unitary subrings that are free $Z$-modules of rank
equal to the degree of the number field, are at the core of the
arithmetic of number fields. In Hecke, orders are always represented
using the module structure, be it the $Z$-module structure for orders
in absolute fields, of the structure as a module over the
maximal order of the base field in the case of relative extensions.
In this chapter we mainly deal with orders in absolute fields.
However, many functions apply in same way to relative extensions.
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
lll(::NfOrd)
any_order(K::AnticNumberField)
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
basis(::NfOrd)
basis(::NfOrd, ::AnticNumberField)
basis_matrix(::NfOrd)
basis_mat_inv(::NfOrd)
gen_index(::NfOrd)
isindex_divisor(::NfOrd, ::fmpz)
minkowski_matrix(::NfOrd, ::Int)
in(::nf_elem, ::NfOrd)
norm_change_const(::NfOrd)
trace_matrix(::NfOrd)
+(::NfOrd, ::NfOrd)
poverorder(::NfOrd, ::fmpz)
poverorders(::NfOrd, ::fmpz)
pmaximal_overorder(::NfOrd, ::fmpz)
```

## Invariants

```@docs
discriminant(::NfOrd)
degree(::NfOrd)
index(::NfOrd)
different(::NfOrd)
isgorenstein(::NfOrd)
isbass(::NfOrd)
zeta_log_residue(::NfOrd, ::Float64)
```

## Arithmetic

Progress and intermediate results of the functions mentioned here
can be obtained via `verbose_level`, supported are

- `ClassGroup`
- `UnitGroup`

All of the functions have a very similar interface: they return
an abelian group and a map converting elements of the group
into the objects required. The maps also
allow a point-wise inverse to server as the *discrete logarithm* map.
For more information on abelian group, see [here](@ref AbelianGroupLink), 
for ideals, [here](@ref NfOrdIdlLink).

```@docs
torsion_unit_group(::NfOrd)
unit_group(::NfOrd)
unit_group_fac_elem(::NfOrd)
sunit_group(I::Vector{NfOrdIdl})
sunit_group_fac_elem(I::Vector{NfOrdIdl})
sunit_mod_units_fac_elem(I::Vector{NfOrdIdl})
class_group(::NfOrd)
picard_group(::NfOrd)
narrow_class_group(::NfOrd)
```

For the processing of units, there are a couple of helper functions
also available:

```@docs
isindependent
```
