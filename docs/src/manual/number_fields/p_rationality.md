```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# $p$-rationality

Hecke provides predicates for testing whether an absolute simple number field
is quasi-$p$-rational or $p$-rational for a given prime $p$.

## Quasi-$p$-rationality

```@docs
is_quasi_p_rational
```

## $p$-rationality

```@docs
is_p_rational
```

## Real cyclotomic fields

For maximal real subfields of cyclotomic fields, a specialized predicate is
available.

```@docs
is_real_cyclotomic_field_p_rational
```
