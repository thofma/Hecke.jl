```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# Introduction


This chapter deals with quadratic and hermitian spaces, and lattices there of.
Note that even though quadratic spaces/lattices are theoretically a special
case of hermitian spaces/lattices, a particular distinction is made here. As
a note for knowledgeable users, only methods regarding hermitian spaces/lattices
over _degree 1 and degree 2 extensions of number fields_ are implemented up to now.

## Definitions and vocabulary

We begin by collecting the necessary definitions and vocabulary.
The terminology follows mainly [Kir16]

### Quadratic and hermitian spaces

Let $K$ be a number field and let $E$ be a finitely generated etale algebra over
$K$ of dimension 1 or 2, i.e. $E=K$ or $E$ is a separable extension of $K$ of
degree 2. In both cases, $E/K$ is endowed with an $K$-linear involution
$\overline{\phantom{x}} \colon E \to E$ for which $K$ is the fixed field (in the
case $E=K$, this is simply the identity of $K$).

A *hermitian space* $V$ over $E/K$ is a finite-dimensional $E$-vector space,
together with a sesquilinear (with respect to the involution of $E/K$) morphism
$\Phi \colon V \times V \to E$. In the trivial case $E=K$, $\Phi$ is therefore
a $K$-bilinear morphism and we called $(V, \Phi)$ a *quadratic hermitian space*
over $K$.

We will always work with an implicit canonical basis $e_1, \ldots, e_n$ of $V$.
In view of this, hermitian spaces over $E/K$ are in bijection with hermitian
matrices with entries in $E$, with respect to the involution $\overline{\phantom{x}}$.
In particular, there is a bijection between quadratic hermitian spaces over $K$
and symmetric matrices with entries in $K$.
For any basis $B = (v_1, \ldots, v_n)$ of $(V, \Phi)$, we call the matrix
$G_B = (\Phi(v_i, v_j))_{1 \leq i, j \leq n} \in E^{n \times n}$ the *Gram matrix*
of $(V, \Phi)$ associated to $B$. If $B$ is the implicit fixed canonical basis
of $(V, \Phi)$, we simply talk about the Gram matrix of $(V, \Phi)$.

For a hermitian space $V$, we refer to the field $E$ as the *base ring* of $V$ and
to $\overline{\phantom{x}}$ as the *involution* of $V$. Meanwhile, the field $K$
is referred to as the *fixed field* of $V$.

By abuse of language, non-quadratic hermitian spaces are sometimes simply called
_hermitian spaces_ and, in contrast, quadratic hermitian spaces are called
_quadratic spaces_. In a general context, an arbitrary space (quadratic or
hermitian) is referred to as a _space_ throughout this chapter.

### Quadratic and hermitian lattices

Let $V$ be a space over $E/K$. A finitely generated $\mathcal O_E$-submodule $L$
of $V$ is called a *hermitian lattice*. By extension of vocabulary if $V$ is
quadratic (i.e. $E=K$), $L$ is called a *quadratic hermitian lattice*. We call
$V$ the *ambient space* of $L$ and $L\otimes_{\mathcal O_E} E$ the *rational span*
of $L$.

For a hermitian lattice $L$, we refer to $E$ as the *base field* of $L$ and to
the ring $\mathcal O_E$ as the *base ring* of $L$. We also call
$\overline{\phantom{x}} \colon E \to E$ the *involution* of $L$. Finally, we
refer to the field $K$ fixed by this involution as the *fixed field* of $L$ and
to $\mathcal O_K$ as the *fixed ring* of $L$.

Once again by abuse of language, non-quadratic hermitian lattices are sometimes
simply called _hermitian lattices_ and _quadratic lattices_ refer to quadratic
hermitian lattices. Therefore, in a general context, an arbitrary lattice is
referred to as a _lattice_ in this chapter.

## References

Many of the implemented algorithms for computing with quadratic and hermitian
lattices over number fields are based on the Magma implementation of Markus
Kirschmer, which can be found [here](http://www.math.rwth-aachen.de/~Markus.Kirschmer/magma/lat.html).

Most of the definitions and results are taken from:

[Kir16]
: Definite quadratic and hermitian forms with small class number. Habilitationsschrift. RWTH Aachen University, 2016.
[pdf](http://www.math.rwth-aachen.de/~Markus.Kirschmer/papers/herm.pdf)

[Kir19]
: Determinant groups of hermitian lattices over local fields, Archiv der Mathematik, 113 (2019), no. 4, 337--347.
[pdf](https://math.uni-paderborn.de/fileadmin/mathematik/AG-Computeralgebra/Publications-kirschmer/DETERMINANT_GROUPS_OF_HERMITIAN_LATTICES_OVER.pdf)

