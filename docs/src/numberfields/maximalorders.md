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
