# Introduction
```@meta
CurrentModule = Hecke
```


This chapter deals with absolute number fields and orders there of. 
We follow the common terminology and conventions as e.g. used in
[Cohen1](@cite), [Cohen2](@cite), [PoZa](@cite) or [Marcus](@cite).

## Definitions and vocabulary

We begin by collecting the necessary definitions and vocabulary.  This is in
particular important for everything related to embeddings of number fields into
archimedean fields, since they are at least two (slighlty) different
normalizations.

### Number fields

By an absolute number field we mean finite extensions of $\mathbf Q$, which is
of type `AnticNumberField` and whose elements are of type `nf_elem`. Such an
absolute number field $K$ is always given in the form $K = \mathbf Q(\alpha) =
\mathbf Q[X]/(f)$, where $f \in \mathbf Q[X]$ is an irreducible polynomial.
See [here](@ref NumberFieldsLink) for more information on the different
types of fields supported.

We
call $(1,\alpha,\alpha^2,\dotsc,\alpha^{d-1})$, where $d$ is the degree $[K :
\mathbf Q]$ the *power basis* of $K$. If $\beta$ is any element of $K$, then
the *representation matrix* of $\beta$ is the matrix representing $K \to K,
\gamma \mapsto \beta \gamma$ with respect to the power basis, that is,

```math
\beta \cdot (1,\alpha,\dotsc,\alpha^{d-1}) = M_\alpha (1, \alpha, \dotsc, \alpha^{d-1}).
```

Let $(r,s)$ be the signature of $K$, that is, $K$ has $r$ real embeddings $\sigma_i \colon K \to \mathbf{R}$, $1 \leq i \leq r$, and $2s$ complex embeddings $\sigma_i \colon K \to \mathbf{C}$, $1 \leq i \leq 2s$.
In Hecke the complex embeddings are always ordered such that $\sigma_i = \overline{\sigma_{i+s}}$ for $r + 1 \leq i \leq r + s$.
The $\mathbf{Q}$-linear function
```math
\begin{gather*}
  K \longrightarrow \mathbf R^{d} \\
  \alpha \longmapsto \Bigl( \sigma_1(\alpha), \dotsc, \sigma_r(\alpha), \sqrt{2}\operatorname{Re}\bigl(\sigma_{r+1}(\alpha)\bigr), \sqrt{2}\operatorname{Im}\bigl(\sigma_{r+1}(\alpha)\bigr), \dotsc, \sqrt{2}\operatorname{Re}\bigl(\sigma_{r+s}(\alpha)\bigr), \sqrt{2}\operatorname{Im}\bigl(\sigma_{r+s}(\alpha)\bigr) \Bigr)
\end{gather*}
```
is called the *Minkowski map* (or *Minkowski embedding*).

### (Absolute) Orders

If $K = \mathbf Q(\alpha)$ is an absolute number field, then an *order* $\mathcal
O$ of $K$ is a subring of the ring of integers $\mathcal O_K$, which is free
of rank $[ K : \mathbf Q]$ as a $\mathbf Z$-module. The natural order $\mathbf
Z[\alpha]$ is called the *equation order* of $K$. In Hecke orders of absolute
number fields are constructed (implicitely) by specifying a $\mathbf Z$-basis,
which is refered to as the *basis* of $\mathcal O$. If
$(\omega_1,\dotsc,\omega_d)$ is the basis of $\mathcal O$, then the matrix $B
\in \operatorname{Mat}_{d \times d}(\mathbf Q)$ with

```math
\begin{pmatrix} \omega_1 \\ \vdots \\ \omega_d \end{pmatrix} = B \begin{pmatrix} 1 \\ \vdots \\ \alpha^{d - 1} \end{pmatrix}
```

is called the *basis matrix* of $\mathcal O$. We call $\det(B)$ the *generalized
index* of $\mathcal O$.  In case $\mathbf Z[\alpha] \subseteq \mathcal O$, the
determinant $\det(B)^{-1}$ is in fact equal to $[ \mathcal O : \mathbf Z[\alpha]]$
and is called the *index* of $\mathcal O$.
The matrix
```math
\begin{pmatrix} 
\sigma_1(\omega_1) & \dotsc & \sigma_r(\omega_1) & \sqrt{2}\operatorname{Re}(\sigma_{r+1}(\omega_1)) & \sqrt{2}\operatorname{Im}(\sigma_{r+1}(\omega_1)) & \dotsc & \sqrt{2}\operatorname{Im}(\sigma_{r+s}(\omega_1)) \\\\
\sigma_1(\omega_2) & \dotsc & \sigma_r(\omega_2) & \sqrt{2}\operatorname{Re}(\sigma_{r+1}(\omega_2)) & \sqrt{2}\operatorname{Im}(\sigma_{r+1}(\omega_2)) & \dotsc  & \sqrt{2}\operatorname{Im}(\sigma_{r+s}(\omega_2)) \\\\
\vdots & \ddots & \vdots & \vdots & \vdots & \ddots & \vdots\\\\
\sigma_1(\omega_d) & \dotsc & \sigma_r(\omega_d) & \sqrt{2}\operatorname{Re}(\sigma_{r+1}(\omega_d)) & \sqrt{2}\operatorname{Im}(\sigma_{r+2}(\omega_d)) & \dotsc & \sqrt{2}\operatorname{Im}(\sigma_{r+s}(\omega_d))
\end{pmatrix}
\in \operatorname{Mat}_{d\times d}(\mathbf R).
```
is called the *Minkowski matrix* of $\mathcal O$.


### (Relative) Orders

Orders in non-absolute number fields, so in relative extensions, are represented
differently. Let $K/k$ be a finite extension of number fields, then currently
we require any order in $K$ to contain $\mathcal o_k$, the ring
of integers in $k$. In this case, an order $\mathcal O$ in $K$ is a
finitly generated torsion free $\mathcal o_k$ module, as a ring,
the order is unitary and has $K$ as a fraction field.
Due to $\mathcal o_k$ in general not being a principal
ideal domain, the module structure is more complicated, see 
[here](@ref PMatLink) for details on pseudo-matrices, or [Cohen2](@cite),
Chapter 1 for an introduction.

In short, $\mathcal O$ is represented as $\sum \mathfrak A_i \omega_i$
for (fractional) $\mathcal o_k$ ideals $\mathfrak A_i\subset k$ and
$k$-linear independent elements $\omega_i\in K$. In general
it is impossible to have both $\mathfrak A_i$ integral and
$\omega_i \in \mathcal O$, thus coefficients will not be integral and/ or
generators not in the structure. However we retain unique presentations
and, due to the ideals are locally principal, almost all the
algorithms as in the absolute case.

As far as possible, the interaction and the interface for absolute orders
and relative orders is the same.

## Examples

Usually, to create an order, one starts with a field (or a polynomial):

```@repl 1
using Hecke; # hide
Qx, x = PolynomialRing(FlintQQ, "x");
K, a = NumberField(x^2 - 10, "a");
E = EquationOrder(K)
Z_K = MaximalOrder(K)
conductor(E)
E == Z_K
```

Once orders are created, we can play with elements and ideals:

```@repl 1
lp = prime_decomposition(Z_K, 2)
p = lp[1][1]
isprincipal(p)
fl, alpha = isprincipal(p^2)
norm(alpha)
```

It is possible to work with residue fields as well:

```@repl 1
Fp, mFp = ResidueField(Z_K, p)
[ mFp(x) for x = basis(Z_K)]
```


