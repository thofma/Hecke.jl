# [Spaces](@id Spaces2)


```@meta
CurrentModule = Hecke
DocTestSetup = quote
  using Hecke
end
```

## Creation of spaces

```@docs
quadratic_space(::NumField, ::Int)
hermitian_space(::NumField, ::Int)
quadratic_space(::NumField, ::MatElem)
hermitian_space(::NumField, ::MatElem)
```

### Examples
Here are easy examples to see how these constructors work. We will keep the two
following spaces for the rest of this section:

```@repl 2
using Hecke # hide
K, a = cyclotomic_real_subfield(7);
Kt, t = K["t"];
E, b = number_field(t^2-a*t+1, "b");
Q = quadratic_space(K, K[0 1; 1 0])
H = hermitian_space(E, 3)
```
---

## Attributes
Let $(V, \Phi)$ be a space over $E/K$. We define its *dimension* to be its dimension
as a vector space over its base ring $E$ and its *rank* to be the rank of its Gram
matrix. If these two invariants agree, the space is said to be *regular*.

While dealing with lattices, one always works with regular ambient spaces.

The *determinant* $\text{det}(V, \Phi)$ of $(V, \Phi)$ is defined to be the
class of the determinant of its Gram matrix in $K^{\times}/N(E^{\times})$ (which
is similar to $K^{\times}/(K^{\times})^2$ in the quadratic case).
The *discriminant* $\text{disc}(V, \Phi)$ of $(V, \Phi)$ is defined to be
$(-1)^{(m(m-1)/2)}\text{det}(V, \Phi)$, where $m$ is the rank of $(V, \Phi)$.

```@docs
rank(::AbstractSpace)
dim(::AbstractSpace)
gram_matrix(::AbstractSpace)
involution(::AbstractSpace)
base_ring(::AbstractSpace)
fixed_field(::AbstractSpace)
det(::AbstractSpace)
discriminant(::AbstractSpace)
```

### Examples
So for instance, one could get the following information about the hermitian
space $H$:

```@repl 2
using Hecke # hide
K, a = cyclotomic_real_subfield(7);
Kt, t = K["t"];
E, b = number_field(t^2-a*t+1, "b");
H = hermitian_space(E, 3);
rank(H), dim(H)
gram_matrix(H)
involution(H)
base_ring(H)
fixed_field(H)
det(H), discriminant(H)
```
---

## Predicates
Let $(V, \Phi)$ be a hermitian space over $E/K$ (resp. quadratic space $K$).
We say that $(V, \Phi)$ is *definite* if $E/K$ is CM (resp. $K$ is totally
real) and if there exists an orthogonal basis of $V$ for which the diagonal
elements of the associated Gram matrix of $(V, \Phi)$ are either all totally
positive or all totally negative. In the former case, $V$ is said to be
*positive definite*, while in the latter case it is *negative definite*.
In all the other cases, we say that $V$ is *indefinite*.

```@docs
is_regular(::AbstractSpace)
is_quadratic(::AbstractSpace)
is_hermitian(::AbstractSpace)
is_positive_definite(::AbstractSpace)
is_negative_definite(::AbstractSpace)
is_definite(::AbstractSpace)
```

Note that the `is_hermitian` function tests whether the space is non-quadratic.

### Examples

```@repl 2
using Hecke # hide
K, a = cyclotomic_real_subfield(7);
Kt, t = K["t"];
E, b = number_field(t^2-a*t+1, "b");
Q = quadratic_space(K, K[0 1; 1 0]);
H = hermitian_space(E, 3);
is_regular(Q), is_regular(H)
is_quadratic(Q), is_hermitian(H)
is_definite(Q), is_positive_definite(H)
```
---

## Inner products and diagonalization

```@docs
gram_matrix(::AbstractSpace{T}, ::MatElem{S}) where {S, T}
gram_matrix(::AbstractSpace{T}, ::Vector{Vector{U}}) where {T, U}
inner_product(::AbstractSpace, ::Vector, ::Vector)
orthogonal_basis(::AbstractSpace)
diagonal(::AbstractSpace)
diagonal_with_transform(::AbstractSpace)
restrict_scalars(::AbstractSpace, ::QQField, ::FieldElem)
```

### Examples

```@repl 2
using Hecke # hide
K, a = cyclotomic_real_subfield(7);
Kt, t = K["t"];
E, b = number_field(t^2-a*t+1, "b");
Q = quadratic_space(K, K[0 1; 1 0]);
H = hermitian_space(E, 3);
gram_matrix(Q, K[1 1; 2 0])
gram_matrix(H, E[1 0 0; 0 1 0; 0 0 1])
inner_product(Q, K[1  1], K[0  2])
orthogonal_basis(H)
diagonal(Q), diagonal(H)
```
---

## Equivalence
Let $(V, \Phi)$ and $(V', \Phi')$ be spaces over the same extension $E/K$.
A *homomorphism of spaces* from $V$ to $V'$ is a $E$-linear mapping
$f \colon V \to V'$ such that for all $x,y \in V$, one has
```math
   \Phi'(f(x), f(y)) = \Phi(x,y).
```
An automorphism of spaces is called an *isometry* and a monomorphism is
called an *embedding*.

```@docs
hasse_invariant(::QuadSpace, p)
witt_invariant(::QuadSpace, p)
is_isometric(::AbstractSpace, ::AbstractSpace)
is_isometric(::AbstractSpace, ::AbstractSpace, p)
invariants(::QuadSpace)
```

### Examples
For instance, for the case of $Q$ and the totally ramified prime $\mathfrak p$
of $O_K$ above $7$, one can get:

```@repl 2
using Hecke # hide
K, a = cyclotomic_real_subfield(7);
Q = quadratic_space(K, K[0 1; 1 0]);
OK = maximal_order(K);
p = prime_decomposition(OK, 7)[1][1];
hasse_invariant(Q, p), witt_invariant(Q, p)
Q2 = quadratic_space(K, K[-1 0; 0 1]);
is_isometric(Q, Q2, p)
is_isometric(Q, Q2)
invariants(Q2)
```
---

## Embeddings
Let $(V, \Phi)$ and $(V', \Phi')$ be two spaces over the same extension $E/K$,
and let $\sigma \colon V \to V'$ be an $E$-linear morphism. $\sigma$ is called
a *representation* of $V$ into $V'$ if for all $x \in V$
```math
   \Phi'(\sigma(x), \sigma(x)) = \Phi(x,x).
```
In such a case, $V$ is said to be *represented* by $V'$ and $\sigma$ can be seen
as an embedding of $V$ into $V'$. This representation property can be also tested
locally with respect to the completions at some finite places. Note that in both
quadratic and hermitian cases, completions are taken at finite places of the fixed
field $K$.

```@docs
is_locally_represented_by(::AbstractSpace, ::AbstractSpace, p)
is_represented_by(::AbstractSpace, ::AbstractSpace)
```

### Examples
Still using the spaces $Q$ and $H$, we can decide whether some other spaces
embed respectively locally or globally into $Q$ or $H$:

```@repl 2
using Hecke # hide
K, a = cyclotomic_real_subfield(7);
Kt, t = K["t"];
E, b = number_field(t^2-a*t+1, "b");
Q = quadratic_space(K, K[0 1; 1 0]);
H = hermitian_space(E, 3);
OK = maximal_order(K);
p = prime_decomposition(OK, 7)[1][1];
Q2 = quadratic_space(K, K[-1 0; 0 1]);
H2 = hermitian_space(E, E[-1 0 0; 0 1 0; 0 0 -1]);
is_locally_represented_by(Q2, Q, p)
is_represented_by(Q2, Q)
is_locally_represented_by(H2, H, p)
is_represented_by(H2, H)
```
---

## Categorical constructions
One can construct direct sums of spaces of the same kind. Since those are also
direct products, they are called biproducts in this context. Depending on the user
usage, one of the following three methods can be called to obtain the direct
sum of a finite collection of spaces. Note that the corresponding copies
of the original spaces in the direct sum are pairwise orthogonal.

```@docs
direct_sum(::Vector{AbstractSpace})
direct_product(::Vector{AbstractSpace})
biproduct(::Vector{AbstractSpace})
```

### Example

```@repl 2
using Hecke # hide
E, b = cyclotomix_field_as_cm_extensions(7);
H = hermitian_space(E, 3);
H2 = hermitian_space(E, E[-1 0 0; 0 1 0; 0 0 -1]);
H3, inj, proj = biproduct(H, H2)
is_one(matrix(compose(inj[1], proj[1])))
is_zero(matrix(compose(inj[1], proj[2])))
```
## Orthogonality operations

```@docs
orthogonal_complement(::AbstractSpace, ::MatElem)
orthogonal_projection(::AbstractSpace, ::MatElem)
```

### Example

```@repl 2
using Hecke # hide
K, a = cyclotomic_real_subfield(7);
Kt, t = K["t"];
Q = quadratic_space(K, K[0 1; 1 0]);
orthogonal_complement(Q, matrix(K, 1, 2, [1 0]))
```
---

## Isotropic spaces
Let $(V, \Phi)$ be a space over $E/K$ and let $\mathfrak p$ be a place in $K$.
$V$ is said to be *isotropic* locally at $\mathfrak p$ if
there exists an element $x \in V_{\mathfrak p}$ such that
$\Phi_{\mathfrak p}(x,x) = 0$, where $\Phi_{\mathfrak p}$ is the continuous
extension of $\Phi$ to $V_{\mathfrak p} \times V_{\mathfrak p}$.

```@docs
is_isotropic(::AbstractSpace, p)
```
### Example

```@repl 2
using Hecke # hide
K, a = cyclotomic_real_subfield(7);
Kt, t = K["t"];
E, b = number_field(t^2-a*t+1, "b");
H = hermitian_space(E, 3);
OK = maximal_order(K);
p = prime_decomposition(OK, 7)[1][1];
is_isotropic(H, p)
```
---

## Hyperbolic spaces

Let $(V, \Phi)$ be a space over $E/K$ and let $\mathfrak p$ be a prime ideal
of $\mathcal O_K$. $V$ is said to be *hyperbolic* locally at $\mathfrak p$ if
the completion $V_{\mathfrak p}$ of $V$ can be decomposed as an orthogonal sum
of hyperbolic planes. The hyperbolic plane is the space $(H, \Psi)$ of rank 2
over $E/K$ such that there exists a basis $e_1, e_2$ of $H$ such that
$\Psi(e_1, e_1) = \Psi(e_2, e_2) = 0$ and $\Psi(e_1, e_2) = 1$.

```@docs
is_locally_hyperbolic(::HermSpace, ::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
```

### Example

```@repl 2
using Hecke # hide
K, a = cyclotomic_real_subfield(7);
Kt, t = K["t"];
E, b = number_field(t^2-a*t+1, "b");
H = hermitian_space(E, 3);
OK = maximal_order(K);
p = prime_decomposition(OK, 7)[1][1];
is_locally_hyperbolic(H, p)
```

