```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# Introduction


This chapter deals with number fields and orders there of.
We follow the common terminology and conventions as e.g. used in
[Coh93](@cite), [Coh00](@cite), [PZ97](@cite) or [Mar18](@cite).

If $K$ is a number field, then an *order* $\mathcal
O$ of $K$ is a subring of the ring of integers $\mathcal O_K$ of $K$, which is free
of rank $[K : \mathbf Q]$ as a $\mathbf Z$-module. Depending on whether
$K$ is an absolute field or relative field, orders are treated differently.
As far as possible, the interaction and the interface for orders of absolute number fields
and of relative number fields is the same.

## Orders of absolute number fields

Assume that $K$ is defined as an absolute field.
An order $\mathcal O$ of such a field are constructed (implicitly) by
specifying a $\mathbf Z$-basis, which is referred to as the *basis* of $\mathcal
O$. If $(\omega_1,\dotsc,\omega_d)$ is the basis of $\mathcal O$ and
$(\alpha_1,\dotsc,\alpha_d)$ the basis of $K$, then the
matrix $B \in \operatorname{Mat}_{d \times d}(\mathbf Q)$ with
```math
\begin{pmatrix} \omega_1 \\ \vdots \\ \omega_d \end{pmatrix} = B \begin{pmatrix} \alpha_1 \\ \vdots \\ \alpha_d \end{pmatrix}
```
is the *basis matrix* of $K$.
If $K = \mathbf{Q}(\alpha) = \mathbf{Q}[x]/(f)$ is simple with $f \in
\mathbf{Z}[x]$, then natural order $\mathbf Z[\alpha] = \mathbf{Z}[x]/(f)$ is
called the *equation order* of $K$.

## Orders of relative number fields

Orders in non-absolute number fields, that is, relative extensions, are represented
differently. Let $L/K$ be a finite extension of number fields, then currently
we require any order in $L$ to contain $\mathcal O_K$, the ring
of integers of $K$. In this case, an order $\mathcal O$ in $L$ is a
finitly generated torsion-free module over the Dedekind domain $\mathcal O_K$. As a ring,
the order $\mathcal O$ is unitary and has $L$ as a fraction field.
Due to $\mathcal O_K$ in general not being a principal
ideal domain, the module structure is more complicated
and requires so called pseudo-matrices. See
[here](@ref PMatLink) for details on pseudo-matrices, or [Coh00](@cite),
Chapter 1 for an introduction.

In short, $\mathcal O$ is represented as $\sum \mathfrak a_i \omega_i$
with fractional $\mathcal O_K$ ideals $\mathfrak a_i\subset K$ and
$K$-linear independent elements $\omega_i\in L$. In general
it is impossible to have both $\mathfrak a_i$ integral and
$\omega_i \in \mathcal O$, thus coefficients will not be integral and/or
generators not in the structure.

## Examples

Usually, to create an order, one starts with a field (or a polynomial):

```jldoctest 1
julia> Qx, x = polynomial_ring(QQ, :x);

julia> K, a = number_field(x^2 - 10, :a);

julia> E = equation_order(K)
Order of number field of degree 2 over QQ
with Z-basis [1, a]

julia> Z_K = maximal_order(K)
Maximal order of number field of degree 2 over QQ
with basis [1, a]

julia> conductor(E)
<no 2-elts present>
basis_matrix
[1 0; 0 1]

julia> E == Z_K
true
```

Once orders are created, we can play with elements and ideals:

```jldoctest 1
julia> lp = prime_decomposition(Z_K, 2)
1-element Vector{Tuple{AbsSimpleNumFieldOrderIdeal, Int64}}:
 (<2, a>
Norm: 2
Minimum: 2
two normal wrt: 2, 2)

julia> p = lp[1][1]
<2, a>
Norm: 2
Minimum: 2
two normal wrt: 2

julia> is_principal(p)
false

julia> fl, alpha = is_principal_with_data(p^2)
(true, 2)

julia> norm(alpha)
4
```

It is possible to work with residue fields as well:

```jldoctest 1
julia> Fp, mFp = residue_field(Z_K, p)
(Prime field of characteristic 2, Map: E -> Fp)

julia> [mFp(x) for x = basis(Z_K)]
2-element Vector{FqFieldElem}:
 1
 0
```
