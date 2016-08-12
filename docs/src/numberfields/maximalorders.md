```@meta
CurrentModule = Hecke
```

## Ideals

```@docs
inv(::NfMaxOrdIdl)
valuation(::nf_elem, ::NfMaxOrdIdl)
valuation(::NfMaxOrdIdl, ::NfMaxOrdIdl)
isramified(::NfMaxOrd, ::Int)
prime_decomposition(::NfMaxOrd, ::Int)
prime_ideals_up_to(::NfMaxOrd, ::Int)
factor(::NfMaxOrdIdl)
divexact(::NfMaxOrdIdl, ::fmpz)
divexact(::NfMaxOrdIdl, ::NfMaxOrdIdl)
```

## Fractional ideals

```@docs
*(::NfMaxOrdFracIdl, ::NfMaxOrdFracIdl)
inv(::NfMaxOrdFracIdl)
```

## Class and unit group

```@docs
unit_rank(::NfOrd)
is_unit(::NfOrdElem)
is_torsion_unit(::NfOrdElem)
torsion_unit_order(::NfOrdElem)
torsion_units(::NfOrd)
torsion_units_gen(::NfOrd)
is_independent(::NfOrdElem)
regulator(::Array{NfOrdElem, 1})
unit_group(::NfMaxOrd)
```

## Residue rings

## Residue fields


