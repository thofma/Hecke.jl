# Function Fields

```@meta
CurrentModule = Hecke
```

## [Introduction](@id FunctionFieldsLink)

By definition, a (univariate) function field can be written as a finite extension of a rational
function field $k(x)$ for a field $k$ (commonly $k = \mathbb{Q}$ or $k = \mathbb{F}_p$).
In Hecke, a function field $L$ is currently defined as being a (univariate) rational function
field $k(x)$ or a finite extension thereof. In other words, the extension
is defined in the the following way:
 - We have $L = k(x)/(f)$, where $f \in k(x)[y]$ is an irreducible polynomial (*simple extension*)
We refer to $k(x)$ as the *base field* of the function field $L$.
We call $L$ an *absolute* function field if the base field is equal to the rational function field
$k(x)$.

