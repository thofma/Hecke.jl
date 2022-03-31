# Spaces
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

### Example
Here are easy examples to see how these constructors work. We will keep the two 
following spaces for the rest of this section:

```repl 2
using Hecke # hide
K, a = CyclotomicRealSubfield(7);
Kt, t = K["t"];
E, b = number_field(t^2-a*t+1, "b");
Q = quadratic_space(K, K[0 1; 1 0])
H = hermitian_space(E, 3)
```
---

## Attributes
Let $(V, \Phi)$ be a space over $E/K$. We define its *dimension* to be its dimension
as a vector base over its base ring $E$ and its *rank* to be the rank of its Gram 
matrix. If these two invariants agree, the space is said to be *regular*. 

While dealing with lattices, one always works with regular ambient spaces.

The *determinant* $\textnormal{det}(V, \Phi)$ of $(V, \Phi)$ is defined to be the 
class of the determinant of its Gram matrix in $K^{\ times}/N(E^{\ times})$ (which 
is similar to $K^{\times}/(K^{\times})^2$ in the quadratic case). 
The *discriminant* $\textnormal{disc}(V, \Phi)$ of $(V, \Phi)$ is defined to be 
$(-1)^(m(m-1)/2)\textnormal{det}(V, \Phi)$, where $m$ is the rank of $(V, \Phi).

```@docs
rank(::AbsSpace)
dim(::AbsSpace)
gram_matrix(::AbsSpace)
involution(::AbsSpace)
base_ring(::AbsSpace)
fixed_field(::AbsSpace)
det(::AbsSpace)
discriminant(::AbsSpace)
```

### Example 
So for instance, one could get the following information about the hermitian 
space $H$: 

```repl 2
using Hecke # hide
K, a = CyclotomicRealSubfield(7) # hide
Kt, t = K["t"] #hide
E, b = number_field(t^2-a*t+1, "b") # hide
H = hermitian_space(E, 3) # hide
rank(H), dim(H)
gram_matrix(H)
involution(H)
base_ring(H)
fixed_field(H)
det(H), discriminant(H)
```
---

## Predicates
Let $(V, \ Phi)$ be a hermitian space over $E/K$ (resp. quadratic space $K$). 
We say that $(V, \ Phi)$ is *definite* if $E/K$ is CM (resp. $K$ is totally 
real) and if there exists an orthogonal basis of $V$ for which the diagonal 
elements of the associated Gram matrix of $(V, \ Phi)$ are either all totally 
positive or all totally negative. In the former case, $V$ is said to be 
*positive definite*, while in the latter case it is *negative definite*. 
In all the other cases, we say that $V$ is *indefinite*.

```@docs
isregular(::AbsSpace)
isquadratic(::AbsSpace)
ishermitian(::AbsSpace)
ispositive_definite(::AbsSpace)
isnegative_definite(::AbsSpace)
isdefinite(::AbsSpace)
```

Note that the `ishermitian` function tests whether the space is non-quadratic.

### Example 

```repl 2
using Hecke # hide
K, a = CyclotomicRealSubfield(7) # hide
Kt, t = K["t"] #hide
E, b = number_field(t^2-a*t+1, "b") # hide
Q = quadratic_space(K, K[0 1; 1 0]) # hide
H = hermitian_space(E, 3) # hide
isregular(Q), isregular(H)
isquadratic(Q), ishermitian(H)
isdefinite(Q), ispositive_definite(H)
```
---

## Inner products and diagonalization

```@docs
gram_matrix(::AbsSpace{T}, ::MatElem{S}) where {S, T}
gram_matrix(::AbsSpace{T}, ::Vector{Vector{U}}) where {T, U}
inner_product(::AbsSpace, ::Vector, ::Vector)
orthogonal_basis(::AbsSpace)
diagonal(::AbsSpace)
```

### Example 

```repl 2
using Hecke # hide
K, a = CyclotomicRealSubfield(7) # hide
Kt, t = K["t"] #hide
E, b = number_field(t^2-a*t+1, "b") # hide
Q = quadratic_space(K, K[0 1; 1 0]) # hide
H = hermitian_space(E, 3) # hide
gram_matrix(Q, K[1 1; 2 0])
gram_matrix(H, E[1 0 0; 0 1 0; 0 0 1])
inner_product(Q, [1, 1], [0, 2])
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
isisometric(::AbsSpace, ::AbsSpace)
isisometric(::AbsSpace, ::AbsSpace, p)
invariants(::QuadSpace)
```

### Example 
For instance, for the case of $Q$ and the totally ramified prime $\mathfrak 
p$ of $O_K$ above $7$, one gets:

```repl 2
using Hecke # hide
K, a = CyclotomicRealSubfield(7) # hide
Q = quadratic_space(K, K[0 1; 1 0]) # hide
OK = maximal_order(K);
p = prime_decomposition(OK, 7)[1][1];
hasse_invariant(Q, p), witt_invariant(Q, p)
Q2 = quadratic_space(K, K[-1 0; 0 1]);
isisometric(Q, Q2, p)
isisometric(Q, Q2)
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

```docs
islocally_represented_by(::AbsSpace, ::AbsSpace, p)
isrepresented_by(::AbsSpace, ::AbsSpace)
```

### Example 
Still using the spaces $Q$ and $H$, we can decide whether some other spaces
embed respectively locally or globally into $Q$ or $H$:
 
```repl 2
using Hecke # hide
K, a = CyclotomicRealSubfield(7) # hide
Kt, t = K["t"] #hide
E, b = number_field(t^2-a*t+1, "b") # hide
Q = quadratic_space(K, K[0 1; 1 0]) # hide
H = hermitian_space(E, 3) # hide
OK = maximal_order(K);
p = prime_decomposition(OK, 7)[1][1];
Q2 = quadratic_space(K, K[-1 0; 0 1]);
H2 = hermitian_space(E, E[-1 0 0; 0 1 0; 0 0 -1]);
islocally_represented_by(Q2, Q, p)
isrepresented_by(Q2, Q)
islocally_represented_by(H2, H, p)
isrepresented_by(H2, H)
```
---

## Orthogonality operations

```@docs
orthogonal_complement(::AbsSpace, ::MatElem)
orthogonal_sum(::AbsSpace, ::AbsSpace)
```

### Example 

```repl 2
using Hecke # hide
K, a = CyclotomicRealSubfield(7) # hide
Kt, t = K["t"] #hide
E, b = number_field(t^2-a*t+1, "b") # hide
Q = quadratic_space(K, K[0 1; 1 0]) # hide
H = hermitian_space(E, 3) # hide
H2 = hermitian_space(E, E[-1 0 0; 0 1 0; 0 0 -1]) # hide
orthogonal_complement(Q, matrix(K, 1, 2, [1 0]))
H3, map1, map2 = orthogonal_sum(H, H2);
H3
map1
map2
```
---

## Isotropic spaces
Let $(V, \Phi)$ be a space over $E/K$ and let $\mathfrak p$ be a prime ideal 
of $\mathcal O_K$. $V$ is said to be *isotropic* locally at $\mathfrak p$ if
there exists an element $x \in V_{\mathfrak p}$ such that 
$\Phi_{\mathfrak p}(x,x) = 0$, where $\Phi_{\mathfrak p}$ is the continuous 
extension of $\Phi$ to $V_{\mathfrak p} \times V_{\mathfrak p}$.

```@docs
isisotropic(::AbsSpace, p)
```
### Example 

```repl 2
using Hecke # hide
K, a = CyclotomicRealSubfield(7) # hide
Kt, t = K["t"] #hide
E, b = number_field(t^2-a*t+1, "b") # hide
H = hermitian_space(E, 3) # hide
OK = maximal_order(K);
p = prime_decomposition(OK, 7)[1][1];
isisotropic(H, p)
```
---

## Hyperbolic spaces

Let $(V, \Phi)$ be a space over $E/K$ and let $\mathfrak p$ be a prime ideal 
of $\mathcal O_K$. $V$ is said to be *hyperbolic* locally at $\mathfrak p$ if
the completion $V_{\mathfrak p}$ of $V$ can be decomposed as an orthogonal sum 
of dimension 2 spaces with Gram matrices of the form 
$\begin{pmatrix}0&1\\1&0\end{pmatrix}$.

```@docs
islocally_hyperbolic(::HermSpace, ::NfOrdIdl)
```

### Example 

```repl 2
using Hecke # hide
K, a = CyclotomicRealSubfield(7) # hide
Kt, t = K["t"] #hide
E, b = number_field(t^2-a*t+1, "b") # hide
H = hermitian_space(E, 3) # hide
OK = maximal_order(K) #hide
p = prime_decomposition(OK, 7)[1][1] #hide
islocally_hyperbolic(H, p)
```

