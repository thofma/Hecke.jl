# [Introduction](@id PMatLink)

```@meta
CurrentModule = Hecke
```


This chapter deals with pseudo-matrices.
We follow the common terminology and conventions introduced in
[Coh00](@cite), however, we operate on rows, not on columns.

Let $R$ be a Dedekind domain, typically, the maximal order of
some number field $K$, further fix some finite dimensional
$K$-vectorspace $V$ (with some basis), frequently $K^n$ or the $K$-structure of
some extension of $K$. Since in general $R$ is not a PID, the $R$-modules
in $V$ are usually not free, but still projective.

Any finitely generated $R$-module $M\subset V$
can be represented as a pseudo-matrix `PMat` as follows:
The structure theory of $R$-modules gives the existence of (fractional)
$R$-ideals $\mathfrak A_i$ and elements $\omega_i\in V$ such that
$$M = \sum \mathfrak A_i \omega_i$$
and the sum is direct.

Following Cohen we call modules of the form $\mathfrak A\omega$ for
some ideal $\mathfrak A$ and $\omega \in V$ a *pseudo element*.
A system $(\mathfrak A_i, \omega_i)$ is called a pseudo-generating
system for $M$ if $\langle \mathfrak A_i\omega_i|i\langle = M$.
A pseudo-generating system is called a pseudo-basis if the
$\omega_i$ are $K$-linear independent.

A *pseudo-matrix* $X$ is a tuple containing a vector of ideals
$\mathfrak A_i$ ($1\le i\le r$) and a matrix $U\in K^{r\times n}$.
The $i$-th row together with the $i$-th ideal defines
a pseudo-element, thus an $R$-module, all of them together
generate a module $M$.

A pseudo-matrix $X=((\mathfrak A_i)_i, U)$ is said to be in pseudo-hnf if
$U$ is essentially upper triangular. Similar to the classical
hnf, there is an algorithm that transforms any pseudo-matrix
into one in pseudo-hnf while maintaining the module.

## Creation

In general to create a `PMat` one has to specify a matrix and a vector of ideals:

```@docs
pseudo_matrix(m::AbstractAlgebra.MatElem{AbsSimpleNumFieldElem}, c::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})
pseudo_matrix(m::Generic.Mat{AbsSimpleNumFieldOrderElem}, c::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})
pseudo_matrix(m::Generic.Mat{AbsSimpleNumFieldElem})
```
(Those functions are also available as `pseudo_matrix`)
## Operations

```@docs
coefficient_ideals(M::PMat)
matrix(M::PMat)
base_ring(M::PMat)
pseudo_hnf(P::PMat{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal})
pseudo_hnf_with_transform(P::PMat{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal})
```

## Examples


