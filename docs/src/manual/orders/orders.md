```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# Orders


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
order(::AbsSimpleNumField, ::Vector{AbsSimpleNumFieldElem})
order(::AbsSimpleNumField, ::QQMatrix)
equation_order(::AbsSimpleNumField)
maximal_order(::AbsSimpleNumField)
maximal_order(::AbsSimpleNumFieldOrder)
lll(::AbsSimpleNumFieldOrder)
any_order(K::AbsSimpleNumField)
```

### Example

```jldoctest
julia> Qx, x = polynomial_ring(QQ, :x);

julia> K, a = number_field(x^2 - 2, :a);

julia> O = equation_order(K)
Maximal order of number field of degree 2 over QQ
with basis [1, a]
```

```@docs
parent(::AbsSimpleNumFieldOrder)
signature(::AbsSimpleNumFieldOrder)
nf(::AbsSimpleNumFieldOrder)
basis(::AbsSimpleNumFieldOrder)
lll_basis(::AbsSimpleNumFieldOrder)
basis(::AbsSimpleNumFieldOrder, ::AbsSimpleNumField)
pseudo_basis(::RelNumFieldOrder)
basis_pmatrix(::RelNumFieldOrder)
basis_nf(::RelNumFieldOrder)
inv_coeff_ideals(::RelNumFieldOrder)
basis_matrix(::AbsNumFieldOrder)
basis_mat_inv(::AbsSimpleNumFieldOrder)
gen_index(::AbsSimpleNumFieldOrder)
is_index_divisor(::AbsSimpleNumFieldOrder, ::ZZRingElem)
minkowski_matrix(::AbsSimpleNumFieldOrder, ::Int)
in(::AbsSimpleNumFieldElem, ::AbsSimpleNumFieldOrder)
norm_change_const(::AbsSimpleNumFieldOrder)
trace_matrix(::AbsSimpleNumFieldOrder)
+(::AbsNumFieldOrder, ::AbsNumFieldOrder)
poverorder(::AbsSimpleNumFieldOrder, ::ZZRingElem)
poverorders(::AbsSimpleNumFieldOrder, ::ZZRingElem)
pmaximal_overorder(::AbsSimpleNumFieldOrder, ::ZZRingElem)
pradical(::AbsNumFieldOrder, ::Union{Integer, ZZRingElem})
pradical(::RelNumFieldOrder, ::Union{Hecke.RelNumFieldOrderIdeal, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})
ring_of_multipliers(::AbsNumFieldOrderIdeal)

```

## Invariants

```@docs
discriminant(::AbsNumFieldOrder)
reduced_discriminant(::AbsSimpleNumFieldOrder)
degree(::AbsSimpleNumFieldOrder)
index(::AbsSimpleNumFieldOrder)
different(::AbsSimpleNumFieldOrder)
codifferent(::AbsSimpleNumFieldOrder)
is_gorenstein(::AbsSimpleNumFieldOrder)
is_bass(::AbsSimpleNumFieldOrder)
is_equation_order(::AbsSimpleNumFieldOrder)
zeta_log_residue(::AbsSimpleNumFieldOrder, ::Float64)
ramified_primes(::AbsSimpleNumFieldOrder)
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
For more information on abelian groups, see [here](@ref AbelianGroupLink2),
for ideals, [here](@ref NfOrdIdlLink2).

- [`torsion_unit_group(::AbsSimpleNumFieldOrder)`](@ref)
- [`unit_group(::AbsSimpleNumFieldOrder)`](@ref)
- [`unit_group_fac_elem(::AbsSimpleNumFieldOrder)`](@ref)
- [`sunit_group(::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})`](@ref)
- [`sunit_group_fac_elem(::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})`](@ref)
- [`sunit_mod_units_group_fac_elem(::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})`](@ref)
- [`class_group(::AbsSimpleNumFieldOrder)`](@ref)
- [`picard_group(::AbsSimpleNumFieldOrder)`](@ref)
- [`narrow_class_group(::AbsSimpleNumFieldOrder)`](@ref)

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

