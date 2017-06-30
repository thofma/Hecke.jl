```@meta
CurrentModule = Hecke
```

## Ideals

```@docs
inv(::NfOrdIdl)
valuation(::nf_elem, ::NfOrdIdl)
valuation(::NfOrdIdl, ::NfOrdIdl)
isramified(::NfOrd, ::Int)
prime_decomposition(::NfOrd, ::Int)
prime_ideals_up_to(::NfOrd, ::Int)
factor(::NfOrdIdl)
divexact(::NfOrdIdl, ::fmpz)
divexact(::NfOrdIdl, ::NfOrdIdl)
```

## Fractional ideals

```@docs
*(::NfOrdFracIdl, ::NfOrdFracIdl)
inv(::NfOrdFracIdl)
```

## Class and unit group

```@docs
unit_rank(::NfOrd)
isunit(::NfOrdElem)
istorsion_unit(::NfOrdElem)
torsion_unit_order(::NfOrdElem)
torsion_units(::NfOrd)
torsion_units_gen(::NfOrd)
isindependent(::NfOrdElem)
regulator(::Array{NfOrdElem, 1})
unit_group(::NfOrd)
```

## Residue rings

## Residue fields


