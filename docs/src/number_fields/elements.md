## Elements

```@meta
CurrentModule = Hecke
```

### Creation

```@docs
gen(::SimpleNumField)
gens(::NonSimpleNumField)
```

### Predicates

```@docs
isintegral(::NumFieldElem)
```

### Invariants

```@docs
norm(::NumFieldElem)
minpoly(::NumFieldElem)
absolute_minpoly(::NumFieldElem)
charpoly(::NumFieldElem)
absolute_charpoly(::NumFieldElem)
```

## Implicit Relative Extensions
Given two absolute fields $K$ and $k$ as well as an embedding $\phi:k \to K$
we can regard $K$ as an extension on $k$, hence invariante of $K$ can
be investigated relative to $k$ rathern than over $Q$.
Here we list functions achieving this without actually computing
$K$ as an extension of $k$.

```@docs
minimum(m::T, I::NfOrdIdl) where T<:(AbstractAlgebra.Map{Nemo.AnticNumberField,Nemo.AnticNumberField,S,T} where T where S)
norm(m::T, I::Hecke.NfAbsOrdIdl{Nemo.AnticNumberField,Nemo.nf_elem}) where T<:(AbstractAlgebra.Map{Nemo.AnticNumberField,Nemo.AnticNumberField,S,T} where T where S)
norm(m::T, a::nf_elem)  where T<:(AbstractAlgebra.Map{Nemo.AnticNumberField,Nemo.AnticNumberField,S,T} where T where S)
discriminant(m::Map, R::NfOrd)
```
