```@meta
CurrentModule = Hecke
```

## Creation

```@docs
Order(::AnticNumberField, ::Array{nf_elem, 1})
Order(::AnticNumberField, ::FakeFmpqMat)
Order(::NfOrdFracIdl)
EquationOrder(::AnticNumberField)
MaximalOrder(::AnticNumberField)
MaximalOrder(::NfOrd)
```

### Example

```@repl
using Hecke; # hide
Qx, x = PolynomialRing(FlintQQ, "x");
K, a = NumberField(x^2 - 2, "a");
O = EquationOrder(K)
```

## Basic properties

```@docs
parent(::NfOrd)
isequation_order(::NfOrd)
signature(::NfOrd)
nf(::NfOrd)
degree(::NfOrd)
basis(::NfOrd)
basis(::NfOrd, ::AnticNumberField)
basis_mat(::NfOrd)
basis_mat_inv(::NfOrd)
discriminant(::NfOrd)
gen_index(O::NfOrd)
index(O::NfOrd)
isindex_divisor(::NfOrd, ::fmpz)
minkowski_mat(::NfOrd, ::Int)
in(::nf_elem, ::NfOrd)
den(::nf_elem, ::NfOrd)
norm_change_const(::NfOrd)
trace_matrix(::NfOrd)
+(::NfOrd, ::NfOrd)
poverorder(::NfOrd, ::fmpz)
pmaximal_overorder(::NfOrd, ::fmpz)
```

## Elements

### Creation

```@docs
(O::NfOrd)(::nf_elem)
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
ideal(::NfOrd, ::Int)
ideal(::NfOrd, ::fmpz)
ideal(::NfOrd, ::fmpz_mat)
ideal(::NfOrd, ::NfOrdElem)
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
frac_ideal(::NfOrd, ::fmpz_mat)
frac_ideal(::NfOrd, ::fmpz_mat, ::fmpz)
frac_ideal(::NfOrd, ::FakeFmpqMat)
frac_ideal(::NfOrd, ::NfOrdIdl)
frac_ideal(::NfOrd, ::NfOrdIdl, ::fmpz)
frac_ideal(::NfOrd, ::nf_elem)
frac_ideal(::NfOrd, ::NfOrdElem)
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

