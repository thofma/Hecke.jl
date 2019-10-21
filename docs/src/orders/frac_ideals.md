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
fractional_ideal(::NfOrd, ::fmpz_mat)
fractional_ideal(::NfOrd, ::fmpz_mat, ::fmpz)
fractional_ideal(::NfOrd, ::FakeFmpqMat)
fractional_ideal(::NfOrd, ::NfOrdIdl)
fractional_ideal(::NfOrd, ::NfOrdIdl, ::fmpz)
fractional_ideal(::NfOrd, ::nf_elem)
fractional_ideal(::NfOrd, ::NfOrdElem)
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
basis_matrix(::NfOrdFracIdl)
basis_mat_inv(::NfOrdFracIdl)
basis(::NfOrdFracIdl)
norm(::NfOrdFracIdl)
```

