# Introduction
```@meta
CurrentModule = Hecke
```


This chapter deals with quadratic and Hermitian spaces and lattices there of. 

## Definitions and vocabulary

We begin by collecting the necessary definitions and vocabulary. 
The terminology follows mainly [Kir16]

### Quadratic and Hermitian spaces

Let $E$ be a number field. A quadratic space is a finite-dimensional vector space
$V$ over $E$ together with a bilinear morphism $\Phi \colon V \times V \to E$.
We will always work with an implicit canonical basis $e_1,\dotsc,e_n$ of $V$.
In view of this, quadratic spaces are in bijection with symmetric matrices over $E$.
If $V$ is a quadratic space, we call the matrix $G = (\Phi(e_i, e_j))_{1 \leq i, j \leq n} \in E^{n \times n}$
the *Gram matrix* of $V$.

Let $E/K$ be an extension of number fields of degree two with non-trivial automorphism $\overline{\phantom{x}} E \to E$. A *Hermitian space* is a finite-dimensional vector space
$V$ over $E$ together with a sesquilinear (with respect to the involution $\overline{\phantom{x}}$) morphism $\Phi \colon V \times V \to K$.
We will always work with an implicit canonical basis $e_1,\dotsc,e_n$ of $V$.
In view of this, Hermitian spaces are in bijection with Hermitian matrices over $E$.
If $V$ is a Hermitian space, we call the matrix $G = (\Phi(e_i, e_j))_{1 \leq i, j \leq n} \in E^{n \times n}$
the *Gram matrix* of $V$. We call $\overline{\phantom{x}}$ the *involution* of $V$.

In both cases we refer to the field $E$ as the *base ring* $V$. In this chapter
we will refer to quadratic and Hermitian spaces also just as *spaces*. 
For Hermitian lattices, the field $K$ will be refered to as the *fixed field* of $V$.

### Quadratic and Hermitian lattices

Let $V$ be a space (either quadratic or Hermitian) with base field $E$.
A finitely generated $\mathcal O_E$-submodule $L$ of $V$ is called a *quadratic lattice* or *Hermitian lattice* respectively.
We call $V$ the *ambient space* of $L$ and $L\otimes_{\mathcal O_E} E$ the *rational span* of $L$.
The ring $\mathcal O_E$ will be referred to as the *base ring* of $L$.

## References

Many of the implemented algorithms for computing with quadratic and hermitian lattices
over number fields are based on the Magma implementation of Markus Kirschmer, which can
be found [here](http://www.math.rwth-aachen.de/~Markus.Kirschmer/magma/lat.html).

[Kir16]
: Definite quadratic and hermitian forms with small class number. Habilitationsschrift. RWTH Aachen University, 2016, [pdf](http://www.math.rwth-aachen.de/~Markus.Kirschmer/papers/herm.pdf)
