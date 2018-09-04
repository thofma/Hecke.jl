# Fractional ideals
```@meta
CurrentModule = Hecke
```


A fractional ideal in the number field $K$ is a $Z_K$-module $A$
such that there exists an integer $d>0$ wich $dA$ is an (integral) ideal
in $Z_K$. Due to the Dedekind property of $Z_K$, the ideals for a
multiplicative group.

Fractional ideals are represented as an integral ideal and an additional
denominator. They are of type `NfOrdFracIdl`.

## Creation

```@docs
frac_ideal(::NfOrd, ::fmpz_mat)
frac_ideal(::NfOrd, ::fmpz_mat, ::fmpz)
frac_ideal(::NfOrd, ::FakeFmpqMat)
frac_ideal(::NfOrd, ::NfOrdIdl)
frac_ideal(::NfOrd, ::NfOrdIdl, ::fmpz)
frac_ideal(::NfOrd, ::nf_elem)
frac_ideal(::NfOrd, ::NfOrdElem)
inv(::NfOrdIdl)
```

## Arithmetic
```@docs
==(::NfOrdFracIdl, ::NfOrdFracIdl)
inv(::NfOrdFracIdl)
integral_split(::NfOrdFracIdl)
```

## Miscaellenous

```@docs
order(::NfOrdFracIdl)
basis_mat(::NfOrdFracIdl)
basis_mat_inv(::NfOrdFracIdl)
basis(::NfOrdFracIdl)
norm(::NfOrdFracIdl)
```

