# Lattices
```@meta
CurrentModule = Hecke
DocTestSetup = quote
    using Hecke
  end
```

## Creation of lattices

### Inside a given ambient space

```@docs
lattice(::AbsSpace)
lattice(::AbsSpace, ::PMat)
lattice(::AbsSpace, ::MatElem)
lattice(::AbsSpace, ::Vector)
```

### Quadratic lattice over a number field

```@docs
quadratic_lattice(::Field)
quadratic_lattice(::Field, ::PMat)
quadratic_lattice(::Field, ::MatElem)
quadratic_lattice(::Field, ::Vector)
```

### Hermitian lattice over a degree 2 extension

```@docs
hermitian_lattice(::NumField)
hermitian_lattice(::NumField, ::PMat)
hermitian_lattice(::NumField, ::MatElem)
hermitian_lattice(::NumField, ::Vector)
```

#### Examples
The two following examples will be used all along this section:

```@repl 2
using Hecke # hide
K, a = rationals_as_number_field();
Kt, t = K["t"];
g = t^2 + 7;
E, b = NumberField(g, "b");
D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);
gens = Vector{nf_elem}[map(K, [1, 1, 0]), map(K, [1, 0, 1]), map(K, [2, 0, 0])];
Lquad = quadratic_lattice(K, gens, gram = D)
D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]);
gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [2, -1, 0, 0]), map(E, [-3, 0, -1, 0]), map(E, [0, 0, 0, -1]), map(E, [b, 0, 0, 0])];
Lherm = hermitian_lattice(E, gens, gram = D)
```

Note that the format used here is the one given by the internal function
`Hecke.to_hecke()` which prints REPL commands to get back the input lattice.

```@repl 2
using Hecke # hide
K, a = rationals_as_number_field();
Kt, t = K["t"];
g = t^2 + 7;
E, b = NumberField(g, "b");
D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]);
gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [2, -1, 0, 0]), map(E, [-3, 0, -1, 0]), map(E, [0, 0, 0, -1]), map(E, [b, 0, 0, 0])];
Lherm = hermitian_lattice(E, gens, gram = D);
Hecke.to_hecke(Lherm)
```

Finally, one can access some databases in which are stored several quadratic and
hermitian lattices. Up to now, these are not automatically available while running
Hecke. It can nonethelss be used in the following way:

```@repl 2
using Hecke # hide
qld = Hecke.quadratic_lattice_database()
lattice(qld, 1)
hlb = Hecke.hermitian_lattice_database()
lattice(hlb, 426)
```

---

## Ambient space and rational span

```@docs
ambient_space(::AbsLat)
rational_span(::AbsLat)
basis_matrix_of_rational_span(::AbsLat)
gram_matrix_of_rational_span(::AbsLat)
diagonal_of_rational_span(::AbsLat)
```

### Examples

```@repl 2
using Hecke # hide
K, a = rationals_as_number_field();
Kt, t = K["t"];
g = t^2 + 7;
E, b = NumberField(g, "b");
D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);
gens = Vector{nf_elem}[map(K, [1, 1, 0]), map(K, [1, 0, 1]), map(K, [2, 0, 0])];
Lquad = quadratic_lattice(K, gens, gram = D);
D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]);
gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [2, -1, 0, 0]), map(E, [-3, 0, -1, 0]), map(E, [0, 0, 0, -1]), map(E, [b, 0, 0, 0])];
Lherm = hermitian_lattice(E, gens, gram = D);
ambient_space(Lherm)
rational_span(Lquad)
basis_matrix_of_rational_span(Lherm)
gram_matrix_of_rational_span(Lherm)
diagonal_of_rational_span(Lquad)
```

---

## Rational equivalence

```@docs
hasse_invariant(L::QuadLat, p)
witt_invariant(L::QuadLat, p)
is_rationally_isometric(::AbsLat, ::AbsLat, ::NfAbsOrdIdl)
is_rationally_isometric(L::AbsLat, M::AbsLat)
```

### Examples
For now and for the rest of this section, the examples will include the new lattice
`Lquad2` which is quadratic. Moreover, all the completions are going to be done at
the prime ideal $p = 7*\mathcal O_K$.

```@repl hecke
using Hecke # hide
K, a = rationals_as_number_field();
D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);
gens = Vector{nf_elem}[map(K, [1, 1, 0]), map(K, [1, 0, 1]), map(K, [2, 0, 0])];
Lquad = quadratic_lattice(K, gens, gram = D);
D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);
gens = Vector{nf_elem}[map(K, [-35, 25, 0]), map(K, [30, 40, -20]), map(K, [5, 10, -5])];
Lquad2 = quadratic_lattice(K, gens, gram = D)
OK = maximal_order(K);
p = prime_decomposition(OK, 7)[1][1]
hasse_invariant(Lquad, p), witt_invariant(Lquad, p)
is_rationally_isometric(Lquad, Lquad2, p)
is_rationally_isometric(Lquad, Lquad2)
```

---

## Attributes
Let $L$ be a lattice over $E/K$. We call a *pseudo-basis* of $L$ any sequence
of pairs $(\mathfrak A_i, x_i)_{1 \leq i \leq n}$ where the $\mathfrak A_i$'s
are fractional (left) ideals of $\mathcal O_E$ and $(x_i)_{1 \leq i \leq n}$
is a basis of the rational span of $L$, and such that

```math
   L = \bigoplus_{i = 1}^n \mathfrak A_ix_i.
```

Note that a pseudo-basis is not unique. Given a pseudo-basis
$(\mathfrak A_i, x_i)_{1 \leq i \leq n}$ of $L$, we define the corresponding
*pseudo-matrix* of $L$ to be the datum consisting of a list of  *coefficient ideals*
corresponding to the ideals $\mathfrak A_i$'s and a matrix whose _rows_ are the
coordinates of the $x_i$'s in the canonical basis of the ambient space of $L$
(conversely, given any such pseudo-matrix, one can define the corresponding pseudo-basis).

```@docs
rank(L::AbsLat)
degree(L::AbsLat)
discriminant(::AbsLat)
base_field(::AbsLat)
base_ring(::AbsLat)
fixed_field(::AbsLat)
fixed_ring(::AbsLat)
involution(::AbsLat)
pseudo_matrix(::AbsLat)
pseudo_basis(::AbsLat)
coefficient_ideals(::AbsLat)
absolute_basis_matrix(::AbsLat)
absolute_basis(::AbsLat)
generators(L::AbsLat; minimal::Bool = false)
gram_matrix_of_generators(::AbsLat; minimal::Bool = false)
```

### Examples

```@repl 2
using Hecke # hide
K, a = rationals_as_number_field();
Kt, t = K["t"];
g = t^2 + 7;
E, b = NumberField(g, "b");
D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]);
gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [2, -1, 0, 0]), map(E, [-3, 0, -1, 0]), map(E, [0, 0, 0, -1]), map(E, [b, 0, 0, 0])];
Lherm = hermitian_lattice(E, gens, gram = D);
rank(Lherm), degree(Lherm)
discriminant(Lherm)
base_field(Lherm)
base_ring(Lherm)
fixed_field(Lherm)
fixed_ring(Lherm)
involution(Lherm)
pseudo_matrix(Lherm)
pseudo_basis(Lherm)
coefficient_ideals(Lherm)
absolute_basis_matrix(Lherm)
absolute_basis(Lherm)
generators(Lherm)
gram_matrix_of_generators(Lherm)
```
---

## Module operations
Let $L$ be a lattice over $E/K$ inside the space $(V, \Phi)$. The *dual lattice*
of $L$ is defined to be the following lattice over $E/K$ in $(V, \Phi)$:

```math
   L^{\#} = \left\{ x \in V \mid \Phi(x,L) \subseteq \mathcal O_E \right\}.
```

For any fractional (left) ideal $\mathfrak a$ of $\mathcal O_E$, one can define
the lattice $\mathfrak aL$ to be the lattice over $E/K$, in the same space $(V, \Phi)$,
obtained by rescaling the coefficient ideals of a pseudo-basis of $L$ by $\mathfrak a$.
In another flavour, for any non-zero element $a \in K$, one defines the *rescaled lattice*
$L^a$ to be the lattice over $E/K$ with the same underlying module as $L$ (i.e. the same
pseudo-bases) but in space $(V, a\Phi)$.

```@docs
Base.:(+)(::AbsLat, ::AbsLat)
intersect(::AbsLat, ::AbsLat)
Base.:(*)(::NumFieldElem, ::AbsLat)
Base.:(*)(::NumFieldOrdIdl, ::AbsLat)
Base.:(*)(::NumFieldOrdFracIdl, ::AbsLat)
rescale(::AbsLat, ::NumFieldElem)
dual(::AbsLat)
```

### Examples

```@repl 2
using Hecke # hide
K, a = rationals_as_number_field();
D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);
gens = Vector{nf_elem}[map(K, [1, 1, 0]), map(K, [1, 0, 1]), map(K, [2, 0, 0])];
Lquad = quadratic_lattice(K, gens, gram = D);
D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);
gens = Vector{nf_elem}[map(K, [-35, 25, 0]), map(K, [30, 40, -20]), map(K, [5, 10, -5])];
Lquad2 = quadratic_lattice(K, gens, gram = D);
OK = maximal_order(K);
p = prime_decomposition(OK, 7)[1][1];
pseudo_matrix(Lquad + Lquad2)
pseudo_matrix(intersect(Lquad, Lquad2))
pseudo_matrix(p*Lquad)
ambient_space(rescale(Lquad,3*a))
pseudo_matrix(Lquad)
```

---

## Invariants
Let $L$ be a lattice over $E/K$, in the space $(V, \Phi)$. We define:
- the *norm* $\mathfrak n(L)$ of $L$ to be the ideal of $\mathcal O_K$ generated
  by the squares $\left\{\Phi(x,x) \mid x \in L \right\}$;
- the *scale* $\mathfrak s(L)$ of $L$ to be the set
  $\Phi(L,L) = \left\{\Phi(x,y) \mid x,y \in L \right\}$;
- the *volume* $\mathfrak v(L)$ of $L$ to be the index ideal

```math
   \lbrack L^{\#} \colon L \rbrack_{\mathcal O_E} := \langle \left\{ \sigma \mid \sigma \in \text{Hom}_{\mathcal O_E}(L^{\#}, L) \right\} \rangle_{\mathcal O_E}.
```

Note that these are fractional ideals of $\mathcal O_E$.

```@docs
norm(::AbsLat)
scale(L::AbsLat)
volume(L::AbsLat)
```

### Examples

```@repl 2
using Hecke # hide
K, a = rationals_as_number_field();
Kt, t = K["t"];
g = t^2 + 7;
E, b = NumberField(g, "b");
D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]);
gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [2, -1, 0, 0]), map(E, [-3, 0, -1, 0]), map(E, [0, 0, 0, -1]), map(E, [b, 0, 0, 0])];
Lherm = hermitian_lattice(E, gens, gram = D);
norm(Lherm)
scale(Lherm)
volume(Lherm)
```
---

## Predicates
Let $L$ be a lattice over $E/K$. It is said to be *integral* if its scale is an
integral ideal, i.e. it is contained in $\mathcal O_E$. Moreover, if $\mathfrak p$
is a prime ideal in $\mathcal O_K$, then $L$ is said to be *modular* (resp.
*locally modular at $\mathfrak p$*) if there exists a fractional ideal $\mathfrak a$
of $\mathcal O_E$ (resp. an integer $v$) such that $\mathfrak aL^{\#} = L$ (resp.
$\mathfrak p^vL_{\mathfrak p}^{\#} = L_{\mathfrak p}$).

```@docs
is_integral(::AbsLat)
is_modular(::AbsLat)
is_modular(::AbsLat, p)
is_positive_definite(L::AbsLat)
is_negative_definite(L::AbsLat)
is_definite(L::AbsLat)
can_scale_totally_positive(L::AbsLat)
```

### Examples

```@repl 2
using Hecke # hide
K, a = rationals_as_number_field();
Kt, t = K["t"];
g = t^2 + 7;
E, b = NumberField(g, "b");
D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]);
gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [2, -1, 0, 0]), map(E, [-3, 0, -1, 0]), map(E, [0, 0, 0, -1]), map(E, [b, 0, 0, 0])];
Lherm = hermitian_lattice(E, gens, gram = D);
OK = maximal_order(K);
is_integral(Lherm)
is_modular(Lherm)[1]
p = prime_decomposition(OK, 7)[1][1];
is_modular(Lherm, p)
is_positive_definite(Lherm)
can_scale_totally_positive(Lherm)
```
---

## Local properties

```@docs
local_basis_matrix(L::AbsLat, p; type::Symbol = :any)
jordan_decomposition(L::AbsLat, p::NfOrdIdl)
is_isotropic(::AbsLat, p)
```

### Examples

```@repl 2
using Hecke # hide
K, a = rationals_as_number_field();
D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);
gens = Vector{nf_elem}[map(K, [1, 1, 0]), map(K, [1, 0, 1]), map(K, [2, 0, 0])];
Lquad = quadratic_lattice(K, gens, gram = D);
OK = maximal_order(K);
p = prime_decomposition(OK, 7)[1][1];
local_basis_matrix(Lquad, p)
jordan_decomposition(Lquad, p)
is_isotropic(Lquad, p)
```

---

## Automorphisms for definite lattices
Let $L$ and $L'$ be two lattices over the same extension $E/K$, inside their
respective ambient spaces $(V, \Phi)$ and $(V', \Phi')$. Similarly to homomorphisms
of spaces, we define a *homomorphism of lattices* from $L$ to $L'$ to be an $E$-module
homomorphism $f \colon L \to L'$ such that for all $x,y \in L$, one has

```math
   \Phi'(f(x), f(y)) = \Phi(x,y).
```

Again, any automorphism of lattices is called an *isometry* and any monomorphism is
called an *embedding*. We refer to the set of isometries from a lattice $L$ to itself
as the *automorphism group of $L$*.

```@docs
automorphism_group_order(::AbsLat)
automorphism_group_generators(::AbsLat)
```

### Examples

```@repl 2
using Hecke # hide
K, a = rationals_as_number_field();
Kt, t = K["t"];
g = t^2 + 7;
E, b = NumberField(g, "b");
D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);
gens = Vector{nf_elem}[map(K, [1, 1, 0]), map(K, [1, 0, 1]), map(K, [2, 0, 0])];
Lquad = quadratic_lattice(K, gens, gram = D);
is_definite(Lquad)
automorphism_group_order(Lquad)
automorphism_group_generators(Lquad)
```

---

## Isometry

```@docs
is_isometric(::AbsLat, ::AbsLat)
is_locally_isometric(::AbsLat, ::AbsLat, p::NfOrdIdl)
```

### Examples

```@repl 2
using Hecke # hide
K, a = rationals_as_number_field();
D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);
gens = Vector{nf_elem}[map(K, [1, 1, 0]), map(K, [1, 0, 1]), map(K, [2, 0, 0])];
Lquad = quadratic_lattice(K, gens, gram = D);
D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);
gens = Vector{nf_elem}[map(K, [-35, 25, 0]), map(K, [30, 40, -20]), map(K, [5, 10, -5])];
Lquad2 = quadratic_lattice(K, gens, gram = D);
OK = maximal_order(K);
p = prime_decomposition(OK, 7)[1][1];
is_isometric(Lquad, Lquad2)
is_locally_isometric(Lquad, Lquad2, p)
```

---

## Maximal integral lattices

```@docs
is_maximal_integral(::AbsLat, p)
is_maximal_integral(::AbsLat)
is_maximal(::AbsLat, p)
maximal_integral_lattice(::AbsLat, p)
maximal_integral_lattice(::AbsLat)
maximal_integral_lattice(::AbsSpace)
```

### Examples

```@repl 2
using Hecke # hide
K, a = rationals_as_number_field();
Kt, t = K["t"];
g = t^2 + 7;
E, b = NumberField(g, "b");
D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]);
gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [2, -1, 0, 0]), map(E, [-3, 0, -1, 0]), map(E, [0, 0, 0, -1]), map(E, [b, 0, 0, 0])];
Lherm = hermitian_lattice(E, gens, gram = D);
OK = maximal_order(K);
p = prime_decomposition(OK, 7)[1][1];
is_maximal_integral(Lherm, p)
is_maximal_integral(Lherm)
is_maximal(Lherm, p)
pseudo_basis(maximal_integral_lattice(Lherm, p))
pseudo_basis(maximal_integral_lattice(Lherm))
pseudo_basis(maximal_integral_lattice(ambient_space(Lherm)))
```

