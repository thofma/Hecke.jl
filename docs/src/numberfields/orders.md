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
degree(::NfOrd)
norm_change_const(::NfOrd)
isequationorder(::NfOrd)
nf(::NfOrd)
basis(::NfOrd)
basis_mat(::NfOrd)
basis_mat_inv(::NfOrd)
discriminant(::NfOrd)
gen_index(::NfOrd)
index(::NfOrd)
isindex_divisor(::NfOrd, p::Int)
minkowski_mat(::NfOrd)
in(::nf_elem, ::NfOrd)
den(::nf_elem, ::NfOrd)
+(::NfOrd, ::NfOrd)
poverorder(::NfOrd, ::fmpz)
pmaximal_overorder(::NfOrd, ::fmpz)
```

## Elements

### Creation

```@docs
call(::NfOrdGen, ::nf_elem)
call(::NfOrdGen, ::fmpz)
call(::NfOrdGen, ::Array{fmpz, 1})
call(::NfOrdGen, ::Array{Int, 1})
call(::NfOrdGen)
```

### Basic properties

```@docs
parent(::NfOrdElem)
elem_in_nf(::NfOrdElem)
elem_in_basis(::NfOrdElem)
discriminant(::Array{NfOrdElem, 1})
==(::NfOrdElem, ::NfOrdElem)
zero(::NfOrd)
one(::NfOrd)
iszero(::NfOrdElem)
isone(::NfOrdElem)
```

### Arithmetic

```@docs
-(::NfOrdElem)
+(::NfOrdElem, ::NfOrdElem)
-(::NfOrdElem, ::NfOrdElem)
*(::NfOrdElem, ::NfOrdElem)
^(::NfOrdElem, ::Int)
mod(::NfOrdElem, ::Int)
powermod(::NfOrdElem, ::fmpz, ::Int)
```

### Miscallenous

```@docs
representation_mat(::NfOrdElem)
representation_mat(::NfOrdElem, ::AnticNumberField)
trace(::NfOrdElem)
norm(::NfOrdElem)
rand(::NfOrd, ::Int)
minkowski_map(::NfOrdElem, ::Int)
conjugates_arb(::NfOrdElem, ::Int)
conjugates_arb_log(::NfOrdElem, ::Int)
t2(::NfOrdElem, ::Int)
```

## Ideals

### Creation

```@docs
ideal(::NfOrdGen, ::Int)
ideal(::NfOrdGen, ::fmpz)
ideal(::NfOrdGen, ::fmpz_mat)
ideal(::NfOrdGen, ::NfOrdElem{NfOrdGen})
ring_of_multipliers(::NfOrdIdl)
*(::NfOrd, ::NfOrdElem)
```

### Arithmetic

```@docs
==(::NfOrdIdl, ::NfOrdIdl)
+(::NfOrdIdl, ::NfOrdIdl)
*(::NfOrdIdl, ::NfOrdIdl)
lcm(::NfOrdIdl, ::NfOrdIdl)
```

### Miscaellenous

```@docs
order(::NfOrdIdl)
basis(::NfOrdIdl)
basis_mat(::NfOrdIdl)
basis_mat_inv(::NfOrdIdl)
minimum(::NfOrdIdl)
norm(::NfOrdIdl)
in(::NfOrdElem, ::NfOrdIdl)
idempotents(::NfOrdIdl, ::NfOrdIdl)
mod(::NfOrdElem, ::NfOrdIdl)
pradical(::NfOrd, p::fmpz)
```

## Fractional ideals

### Creation

```@docs
frac_ideal(::NfOrdGen, ::fmpz_mat)
frac_ideal(::NfOrdGen, ::fmpz_mat, ::fmpz)
frac_ideal(::NfOrdGen, ::FakeFmpqMat)
frac_ideal(::NfOrdGen, ::NfOrdGenIdl)
frac_ideal(::NfOrdGen, ::NfOrdGenIdl, ::fmpz)
frac_ideal(::NfOrdGen, ::nf_elem)
frac_ideal(::NfOrdGen, ::NfOrdElem{NfOrdGen})
```

### Arithmetic
```@docs
==(::NfOrdFracIdl, ::NfOrdFracIdl)
```

### Miscaellenous

```@docs
order(::NfOrdFracIdl)
basis_mat(::NfOrdFracIdl)
basis_mat_inv(::NfOrdFracIdl)
basis(::NfOrdFracIdl)
norm(::NfOrdFracIdl)
```

