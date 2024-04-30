### Number fields

By an absolute number field we mean finite extensions of $\mathbf Q$, which is
of type `AbsSimpleNumField` and whose elements are of type `AbsSimpleNumFieldElem`. Such an
absolute number field $K$ is always given in the form $K = \mathbf Q(\alpha) =
\mathbf Q[X]/(f)$, where $f \in \mathbf Q[X]$ is an irreducible polynomial.
See [here](@ref NumberFieldsLink2) for more information on the different
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

If $K = \mathbf Q(\alpha)$ is an absolute number field, then an *order* $\mathcal
O$ of $K$ is a subring of the ring of integers $\mathcal O_K$, which is free
of rank $[ K : \mathbf Q]$ as a $\mathbf Z$-module. The natural order $\mathbf
Z[\alpha]$ is called the *equation order* of $K$. In Hecke orders of absolute
number fields are constructed (implicitly) by specifying a $\mathbf Z$-basis,
which is referred to as the *basis* of $\mathcal O$. If
$(\omega_1,\dotsc,\omega_d)$ is the basis of $\mathcal O$, then the matrix $B
\in \operatorname{Mat}_{d \times d}(\mathbf Q)$ with


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


