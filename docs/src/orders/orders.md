# Orders
```@meta
CurrentModule = Hecke
```

Orders, that is, unitary subrings that are free $\mathbf{Z}$-modules of rank
equal to the degree of the number field, are at the core of the
arithmetic of number fields. In Hecke, orders are always represented
using the module structure, be it the $\mathbf{Z}$-module structure for orders
of absolute numbers fields, or the structure as a module over the
maximal order of the base field in the case of relative number fields.
In this chapter we mainly deal with orders of absolute fields.
However, many functions apply in same way to relative extensions.
There are more general definitions of orders in number fields
available, but those are (currently) not implemented in Hecke.

Among all orders in a fixed field, there is a unique maximal order,
called the *maximal order*, or *ring of integers* of the number field.
It is well known that this is the only order that is a Dedekind
domain, hence has a rich ideal structure as well.
The maximal order is also the integral closure of $\mathbf{Z}$ in the number field
and can also be interpreted as a normalization of any other order.

## Creation and basic properties

```@docs
Order(::AbsSimpleNumField, ::Vector{AbsSimpleNumFieldElem})
Order(::AbsSimpleNumField, ::FakeFmpqMat)
Order(::AbsNumFieldOrderFractionalIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
EquationOrder(::AbsSimpleNumField)
MaximalOrder(::AbsSimpleNumField)
MaximalOrder(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
lll(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
any_order(K::AbsSimpleNumField)
```

### Example

```@repl
using Hecke; # hide
Qx, x = polynomial_ring(FlintQQ, "x");
K, a = number_field(x^2 - 2, "a");
O = EquationOrder(K)
```

```@docs
parent(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
signature(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
nf(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
basis(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
lll_basis(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
basis(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::AbsSimpleNumField)
pseudo_basis(::RelNumFieldOrder)
basis_pmatrix(::RelNumFieldOrder)
basis_nf(::RelNumFieldOrder)
inv_coeff_ideals(::RelNumFieldOrder)
basis_matrix(::AbsNumFieldOrder)
basis_mat_inv(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
gen_index(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
is_index_divisor(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::ZZRingElem)
minkowski_matrix(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::Int)
in(::AbsSimpleNumFieldElem, ::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
norm_change_const(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
trace_matrix(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
+(::AbsNumFieldOrder, ::AbsNumFieldOrder)
poverorder(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::ZZRingElem)
poverorders(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::ZZRingElem)
pmaximal_overorder(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::ZZRingElem)
pradical(::AbsNumFieldOrder, ::Union{Integer, ZZRingElem})
pradical(::RelNumFieldOrder, ::Union{Hecke.RelNumFieldOrderIdeal, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})
ring_of_multipliers(::AbsNumFieldOrderIdeal)

```

## Invariants

```@docs
discriminant(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
discriminant(::AbsNumFieldOrder)
reduced_discriminant(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
degree(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
index(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
different(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
codifferent(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
is_gorenstein(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
is_bass(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
is_equation_order(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
zeta_log_residue(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::Float64)
ramified_primes(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
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

- [`torsion_unit_group(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})`](@ref)
- [`unit_group(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})`](@ref)
- [`unit_group_fac_elem(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})`](@ref)
- [`sunit_group(::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})`](@ref)
- [`sunit_group_fac_elem(::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})`](@ref)
- [`sunit_mod_units_group_fac_elem(::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})`](@ref)
- [`class_group(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})`](@ref)
- [`picard_group(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})`](@ref)
- [`narrow_class_group(::AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})`](@ref)

For the processing of units, there are a couple of helper functions
also available:

```@docs
is_independent
```

## Predicates

```@docs
Hecke.is_contained(::AbsNumFieldOrder, ::AbsNumFieldOrder)
is_maximal(::AbsNumFieldOrder)
```

