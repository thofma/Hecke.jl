```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# [Spaces](@id Spaces2)

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

```jldoctest
julia> K, a = cyclotomic_real_subfield(7);

julia> Kt, t = K[:t];

julia> E, b = number_field(t^2-a*t+1, :b);

julia> Q = quadratic_space(K, K[0 1; 1 0])
Quadratic space of dimension 2
  over maximal real subfield of cyclotomic field of order 7
with gram matrix
[0   1]
[1   0]

julia> H = hermitian_space(E, 3)
Hermitian space of dimension 3
  over relative number field with defining polynomial t^2 - (z_7 + 1/z_7)*t + 1
    over number field with defining polynomial $^3 + $^2 - 2*$ - 1
      over rational field
with gram matrix
[1   0   0]
[0   1   0]
[0   0   1]
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

```jldoctest
julia> K, a = cyclotomic_real_subfield(7);

julia> Kt, t = K[:t];

julia> E, b = number_field(t^2-a*t+1, :b);

julia> H = hermitian_space(E, 3);

julia> rank(H), dim(H)
(3, 3)

julia> gram_matrix(H)
[1   0   0]
[0   1   0]
[0   0   1]

julia> involution(H)
Map
  from relative number field of degree 2 over K
  to relative number field of degree 2 over K

julia> base_ring(H)
Relative number field with defining polynomial t^2 - (z_7 + 1/z_7)*t + 1
  over number field with defining polynomial $^3 + $^2 - 2*$ - 1
    over rational field

julia> fixed_field(H)
Number field with defining polynomial $^3 + $^2 - 2*$ - 1
  over rational field

julia> det(H), discriminant(H)
(1, -1)
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

```jldoctest
julia> K, a = cyclotomic_real_subfield(7);

julia> Kt, t = K[:t];

julia> E, b = number_field(t^2-a*t+1, :b);

julia> Q = quadratic_space(K, K[0 1; 1 0]);

julia> H = hermitian_space(E, 3);

julia> is_regular(Q), is_regular(H)
(true, true)

julia> is_quadratic(Q), is_hermitian(H)
(true, true)

julia> is_definite(Q), is_positive_definite(H)
(false, true)
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

```jldoctest
julia> K, a = cyclotomic_real_subfield(7);

julia> Kt, t = K[:t];

julia> E, b = number_field(t^2-a*t+1, :b);

julia> Q = quadratic_space(K, K[0 1; 1 0]);

julia> H = hermitian_space(E, 3);

julia> gram_matrix(Q, K[1 1; 2 0])
[2   2]
[2   0]

julia> gram_matrix(H, E[1 0 0; 0 1 0; 0 0 1])
[1   0   0]
[0   1   0]
[0   0   1]

julia> inner_product(Q, K[1  1], K[0  2])
[2]

julia> orthogonal_basis(H)
[1   0   0]
[0   1   0]
[0   0   1]

julia> diagonal(Q), diagonal(H)
(AbsSimpleNumFieldElem[1, -1], AbsSimpleNumFieldElem[1, 1, 1])
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

```jldoctest
julia> K, a = cyclotomic_real_subfield(7);

julia> Q = quadratic_space(K, K[0 1; 1 0]);

julia> OK = maximal_order(K);

julia> p = prime_decomposition(OK, 7)[1][1];

julia> hasse_invariant(Q, p), witt_invariant(Q, p)
(1, 1)

julia> Q2 = quadratic_space(K, K[-1 0; 0 1]);

julia> is_isometric(Q, Q2, p)
true

julia> is_isometric(Q, Q2)
true

julia> invariants(Q2)
(2, 0, -1, Dict{AbsSimpleNumFieldOrderIdeal, Int64}(), Tuple{InfPlc{AbsSimpleNumField, AbsSimpleNumFieldEmbedding}, Int64}[(Infinite place corresponding to (Complex embedding corresponding to -1.80 of K), 1), (Infinite place corresponding to (Complex embedding corresponding to -0.45 of K), 1), (Infinite place corresponding to (Complex embedding corresponding to 1.25 of K), 1)])
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

```jldoctest
julia> K, a = cyclotomic_real_subfield(7);

julia> Kt, t = K[:t];

julia> E, b = number_field(t^2-a*t+1, :b);

julia> Q = quadratic_space(K, K[0 1; 1 0]);

julia> H = hermitian_space(E, 3);

julia> OK = maximal_order(K);

julia> p = prime_decomposition(OK, 7)[1][1];

julia> Q2 = quadratic_space(K, K[-1 0; 0 1]);

julia> H2 = hermitian_space(E, E[-1 0 0; 0 1 0; 0 0 -1]);

julia> is_locally_represented_by(Q2, Q, p)
true

julia> is_represented_by(Q2, Q)
true

julia> is_locally_represented_by(H2, H, p)
true

julia> is_represented_by(H2, H)
false
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

```jldoctest
julia> E, b = cyclotomic_field_as_cm_extension(7);

julia> H = hermitian_space(E, 3);

julia> H2 = hermitian_space(E, E[-1 0 0; 0 1 0; 0 0 -1]);

julia> H3, inj, proj = biproduct(H, H2)
(Hermitian space of dimension 6, AbstractSpaceMor[Map: hermitian space -> hermitian space, Map: hermitian space -> hermitian space], AbstractSpaceMor[Map: hermitian space -> hermitian space, Map: hermitian space -> hermitian space])

julia> is_one(matrix(compose(inj[1], proj[1])))
true

julia> is_zero(matrix(compose(inj[1], proj[2])))
true
```
## Orthogonality operations

```@docs
orthogonal_complement(::AbstractSpace, ::MatElem)
orthogonal_projection(::AbstractSpace, ::MatElem)
```

### Example

```jldoctest
julia> K, a = cyclotomic_real_subfield(7);

julia> Kt, t = K[:t];

julia> Q = quadratic_space(K, K[0 1; 1 0]);

julia> orthogonal_complement(Q, matrix(K, 1, 2, [1 0]))
[1   0]
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

```jldoctest
julia> K, a = cyclotomic_real_subfield(7);

julia> Kt, t = K[:t];

julia> E, b = number_field(t^2-a*t+1, :b);

julia> H = hermitian_space(E, 3);

julia> OK = maximal_order(K);

julia> p = prime_decomposition(OK, 7)[1][1];

julia> is_isotropic(H, p)
true
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

```jldoctest
julia> K, a = cyclotomic_real_subfield(7);

julia> Kt, t = K[:t];

julia> E, b = number_field(t^2-a*t+1, :b);

julia> H = hermitian_space(E, 3);

julia> OK = maximal_order(K);

julia> p = prime_decomposition(OK, 7)[1][1];

julia> is_locally_hyperbolic(H, p)
false
```

