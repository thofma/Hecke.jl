# Genera for hermitian lattices
```@meta
CurrentModule = Hecke
DocTestSetup = quote
    using Hecke
  end
```

## Local genus symbols

_Definition 8.3.1 ([Kir16])_
Let $L$ be a hermitian lattice over $E/K$ and let $\mathfrak p$ be a prime
ideal of $\mathcal O_K$. Let $\mathfrak P$ be the largest ideal of $\mathcal O_E$
over $\mathfrak p$ being invariant under the involution of $E$. We suppose that

```math
   L_{\mathfrak p} = \perp_{i=1}^tL_i
```
with for all $1 \leq i \leq t$, $\mathfrak s(L_i) = \mathfrak P^{s_i}$ for a strictly
increasing sequence of integers $s_1 < \ldots < s_t$. Then, the *local genus symbol*
$g(L, \mathfrak p)$ of $L_{\mathfrak p}$ is defined to be:
  - if $\mathfrak p$ is _good_, i.e. non ramified and non dyadic,

```math
   g(L, \mathfrak p) := [(s_1, r_1, d_1), \ldots, (s_t, r_t, d_t)]
```

  where $d_i = 1$ if the determinant (resp. discriminant) of $L_i$ is a norm
  in $K_{\mathfrak p}^{\times}$, and $d_i = -1$ otherwise, and
  $r_i := \text{rank}(L_i)$ for all i;
  - if $\mathfrak p$ is _bad_,

```math
   g(L, \mathfrak p) := [(s_1, r_1, d_1, n_1), \ldots, (s_t, r_t, d_t, n_t)]
```

  where for all i, $n_i := \text{ord}_{\mathfrak p}(\mathfrak n(L_i))$

Note that we define the scale and the norm of the lattice $L_i$ ($1 \leq i \leq n$)
defined over the extension of local fields $E_{\mathfrak P}/K_{\mathfrak p}$
similarly to the ones of $L$, by extending by continuity the sesquilinear form
of the ambient space of $L$ to the completion. Regarding the determinant (resp.
discriminant), it is defined as the determinant of the Gram matrix associated
to a basis of $L_i$ relatively to the extension of the sesquilinear form
(resp. $(-1)^{(m(m-1)/2}$ times the determinant, where $m$ is the rank of $L_i$).

We call any tuple in $g := g(L, \mathfrak p) = [g_1, \ldots, g_t]$ a *Jordan block*
of $g$ since it corresponds to invariants of a Jordan block of the completion of
the lattice $L$ at $\mathfrak p$. For any such block $g_i$, we call respectively
$s_i, r_i, d_i, n_i$ the *scale*, the *rank*, the *determinant class* (resp.
*discriminant class*) and the *norm* of $g_i$. Note that the norm is necessary
only when the prime ideal is bad.

We say that two hermitian lattices $L$ and $L'$ over $E/K$ are in the same local
genus at $\mathfrak p$ if $g(L, \mathfrak p) = g(L', \mathfrak p)$.

### Creation of local genus symbols

There are two ways of creating a local genus symbol for hermitian lattices:
  - either abstractly, by choosing the extension $E/K$, the prime ideal $\mathfrak p$
    of $\mathcal O_K$, the Jordan blocks `data` and the type of the $d_i$'s (either
    determinant class `:det` or discriminant class `:disc`);

```julia
   genus(HermLat, E::NumField, p::NfOrdIdl, data::Vector; type::Symbol = :det,
                                                          check::Bool = false)
                                                             -> LocalGenusHerm
```
  - or by constructing the local genus symbol of the completion of a hermitian
    lattice $L$ over $E/K$ at a prime ideal $\mathfrak p$ of $\mathcal O_K$.

```julia
   genus(L::HermLat, p::NfOrdIdl) -> LocalGenusHerm
```

#### Examples
We will construct two examples for the rest of this section. Note that the prime
chosen here is bad.

```@repl 2
using Hecke # hide
Qx, x = QQ["x"];
K, a = NumberField(x^2 - 2, "a");
Kt, t  = K["t"];
E, b = NumberField(t^2 - a, "b");
OK = maximal_order(K);
p = prime_decomposition(OK, 2)[1][1];
g1 = genus(HermLat, E, p, [(0, 1, 1, 0), (2, 2, -1, 1)], type = :det)
D = matrix(E, 3, 3, [5//2*a - 4, 0, 0, 0, a, a, 0, a, -4*a + 8]);
gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [1, 0, 0]), map(E, [a, 0, 0]), map(E, [b, 0, 0]), map(E, [a*b, 0, 0]), map(E, [0, 1, 0]), map(E, [0, a, 0]), map(E, [0, b, 0]), map(E, [0, a*b, 0]), map(E, [0, 0, 1]), map(E, [0, 0, a]), map(E, [0, 0, b]), map(E, [0, 0, a*b])];
L = hermitian_lattice(E, gens, gram = D);
g2 = genus(L, p)
```

---

### Attributes

```@docs
length(::LocalGenusHerm)
base_field(::LocalGenusHerm)
prime(::LocalGenusHerm)
```

#### Examples

```@repl 2
using Hecke # hide
Qx, x = QQ["x"];
K, a = NumberField(x^2 - 2, "a");
Kt, t  = K["t"];
E, b = NumberField(t^2 - a, "b");
OK = maximal_order(K);
p = prime_decomposition(OK, 2)[1][1];
g1 = genus(HermLat, E, p, [(0, 1, 1, 0), (2, 2, -1, 1)], type = :det);
length(g1)
base_field(g1)
prime(g1)
```

---

### Invariants

```@docs
scale(::LocalGenusHerm, ::Int)
scales(::LocalGenusHerm)
rank(::LocalGenusHerm, ::Int)
rank(::LocalGenusHerm)
ranks(::LocalGenusHerm)
det(::LocalGenusHerm, ::Int)
det(::LocalGenusHerm)
dets(::LocalGenusHerm)
discriminant(::LocalGenusHerm, ::Int)
discriminant(::LocalGenusHerm)
norm(::LocalGenusHerm, ::Int)
norms(::LocalGenusHerm)
```

#### Examples

```@repl 2
using Hecke # hide
Qx, x = QQ["x"];
K, a = NumberField(x^2 - 2, "a");
Kt, t  = K["t"];
E, b = NumberField(t^2 - a, "b");
OK = maximal_order(K);
p = prime_decomposition(OK, 2)[1][1];
D = matrix(E, 3, 3, [5//2*a - 4, 0, 0, 0, a, a, 0, a, -4*a + 8]);
gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [1, 0, 0]), map(E, [a, 0, 0]), map(E, [b, 0, 0]), map(E, [a*b, 0, 0]), map(E, [0, 1, 0]), map(E, [0, a, 0]), map(E, [0, b, 0]), map(E, [0, a*b, 0]), map(E, [0, 0, 1]), map(E, [0, 0, a]), map(E, [0, 0, b]), map(E, [0, 0, a*b])];
L = hermitian_lattice(E, gens, gram = D);
g2 = genus(L, p);
scales(g2)
ranks(g2)
dets(g2)
norms(g2)
rank(g2), det(g2), discriminant(g2)
```

---

### Predicates

```@docs
is_ramified(::LocalGenusHerm)
is_split(::LocalGenusHerm)
is_inert(::LocalGenusHerm)
is_dyadic(::LocalGenusHerm)
```

#### Examples

```@repl 2
using Hecke # hide
Qx, x = QQ["x"];
K, a = NumberField(x^2 - 2, "a");
Kt, t  = K["t"];
E, b = NumberField(t^2 - a, "b");
OK = maximal_order(K);
p = prime_decomposition(OK, 2)[1][1];
g1 = genus(HermLat, E, p, [(0, 1, 1, 0), (2, 2, -1, 1)], type = :det);
is_ramified(g1), is_split(g1), is_inert(g1), is_dyadic(g1)
```

---

### Local uniformizer

```@docs
uniformizer(::LocalGenusHerm)
```

#### Example

```@repl 2
using Hecke # hide
Qx, x = QQ["x"];
K, a = NumberField(x^2 - 2, "a");
Kt, t  = K["t"];
E, b = NumberField(t^2 - a, "b");
OK = maximal_order(K);
p = prime_decomposition(OK, 2)[1][1];
g1 = genus(HermLat, E, p, [(0, 1, 1, 0), (2, 2, -1, 1)], type = :det);
uniformizer(g1)
```

---

### Determinant representatives
Let $g$ be a local genus symbol for hermitian lattices. Its determinant class, or the
determinant class of its Jordan blocks, are given by $\pm 1$, depending on whether the
determinants are local norms or not. It is possible to get a representative of this
determinant class in terms of powers of the uniformizer of $g$.

```@docs
det_representative(::LocalGenusHerm, ::Int)
det_representative(::LocalGenusHerm)
```

#### Examples

```@repl 2
using Hecke # hide
Qx, x = QQ["x"];
K, a = NumberField(x^2 - 2, "a");
Kt, t  = K["t"];
E, b = NumberField(t^2 - a, "b");
OK = maximal_order(K);
p = prime_decomposition(OK, 2)[1][1];
g1 = genus(HermLat, E, p, [(0, 1, 1, 0), (2, 2, -1, 1)], type = :det);
det_representative(g1)
det_representative(g1,2)
```

---

### Gram matrices

```@docs
gram_matrix(::LocalGenusHerm, ::Int)
gram_matrix(::LocalGenusHerm)
```

#### Examples

```@repl 2
using Hecke # hide
Qx, x = QQ["x"];
K, a = NumberField(x^2 - 2, "a");
Kt, t  = K["t"];
E, b = NumberField(t^2 - a, "b");
OK = maximal_order(K);
p = prime_decomposition(OK, 2)[1][1];
D = matrix(E, 3, 3, [5//2*a - 4, 0, 0, 0, a, a, 0, a, -4*a + 8]);
gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [1, 0, 0]), map(E, [a, 0, 0]), map(E, [b, 0, 0]), map(E, [a*b, 0, 0]), map(E, [0, 1, 0]), map(E, [0, a, 0]), map(E, [0, b, 0]), map(E, [0, a*b, 0]), map(E, [0, 0, 1]), map(E, [0, 0, a]), map(E, [0, 0, b]), map(E, [0, 0, a*b])];
L = hermitian_lattice(E, gens, gram = D);
g2 = genus(L, p);
gram_matrix(g2)
gram_matrix(g2,1)
```

---
---

## Global genus symbols
Let $L$ be a hermitian lattice over $E/K$. Let $P(L)$ be the set of all prime 
ideals of $\mathcal O_K$ which are bad (ramified or dyadic), which are dividing
the scale of $L$ or which are dividing the volume of $L$. Let $S(E/K)$ be the
set of real infinite places of $K$ which split into complex places in $E$. We
define the *global genus symbol* $G(L)$ of $L$ to be the datum consisting of the
local genus symbols of $L$ at each prime of $P(L)$ and the signatures (i.e. the
negative index of inertia) of the Gram matrix of the rational span of $L$ at
each place in $S(E/K)$.

Note that prime ideals in $P(L)$ which don't ramify correspond to those for which
the corresponding completions of $L$ are not unimodular.

We say that two lattice $L$ and $L'$ over $E/K$ are in the same genus, if
$G(L) = G(L')$.
 
### Creation of global genus symbols
Similarly, there are two ways of constructing a global genus symbol for hermitian
lattices:
  - either abstractly, by choosing the extension $E/K$, the set of local genus
    symbols `S` and the signatures `signatures` at the places in $S(E/K)$. Note
    that this requires the given invariants to satisfy the product formula for Hilbert
    symbols.
```julia
   genus(S::Vector{LocalGenusHerm}, signatures) -> GenusHerm
```
  Here `signatures` can be a dictionary with keys the infinite places and values
  the corresponding signatures, or a collection of tuples of the type
  `(::InfPlc, ::Int)`;

  - or by constructing the global genus symbol of a given hermitian lattice $L$.
```julia
   genus(L::HermLat) -> GenusHerm
```

#### Examples
As before, we will construct two different global genus symbols for hermitian
lattices, which we will use for the rest of this section.

```@repl 2
using Hecke # hide
Qx, x = QQ["x"];
K, a = NumberField(x^2 - 2, "a");
Kt, t  = K["t"];
E, b = NumberField(t^2 - a, "b");
OK = maximal_order(K);
p = prime_decomposition(OK, 2)[1][1];
g1 = genus(HermLat, E, p, [(0, 1, 1, 0), (2, 2, -1, 1)], type = :det);
infp = infinite_places(E)
SEK = unique([r.base_field_place for r in infp if isreal(r.base_field_place) && !isreal(r)]);
length(SEK)
G1 = genus([g1], [(SEK[1], 1)])
D = matrix(E, 3, 3, [5//2*a - 4, 0, 0, 0, a, a, 0, a, -4*a + 8]);
gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [1, 0, 0]), map(E, [a, 0, 0]), map(E, [b, 0, 0]), map(E, [a*b, 0, 0]), map(E, [0, 1, 0]), map(E, [0, a, 0]), map(E, [0, b, 0]), map(E, [0, a*b, 0]), map(E, [0, 0, 1]), map(E, [0, 0, a]), map(E, [0, 0, b]), map(E, [0, 0, a*b])];
L = hermitian_lattice(E, gens, gram = D);
G2 = genus(L)
```

---

### Attributes

```@docs
base_field(::GenusHerm)
primes(::GenusHerm)
signatures(::GenusHerm)
rank(::GenusHerm)
```

#### Examples

```@repl 2
using Hecke # hide
Qx, x = QQ["x"];
K, a = NumberField(x^2 - 2, "a");
Kt, t  = K["t"];
E, b = NumberField(t^2 - a, "b");
OK = maximal_order(K);
p = prime_decomposition(OK, 2)[1][1];
D = matrix(E, 3, 3, [5//2*a - 4, 0, 0, 0, a, a, 0, a, -4*a + 8]);
gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [1, 0, 0]), map(E, [a, 0, 0]), map(E, [b, 0, 0]), map(E, [a*b, 0, 0]), map(E, [0, 1, 0]), map(E, [0, a, 0]), map(E, [0, b, 0]), map(E, [0, a*b, 0]), map(E, [0, 0, 1]), map(E, [0, 0, a]), map(E, [0, 0, b]), map(E, [0, 0, a*b])];
L = hermitian_lattice(E, gens, gram = D);
G2 = genus(L);
base_field(G2)
primes(G2)
signatures(G2)
rank(G2)
```

---

### Mass
_Definition 4.2.1 [Kir16]_
Let $L$ be a hermitian lattice over $E/K$, and suppose that $L$ is definite. In
particular, the automorphism group of $L$ is finite. Let $L_1, \ldots, L_n$ be
a set of representatives of isometry classes in the genus of $L$. This means that
if $L'$ is a lattice over $E/K$ in the genus of $L$ (i.e. they are in the same genus),
then $L'$ is isometric to one of the $L_i$'s, and these representatives are pairwise
non-isometric. Then we define the *mass* of the genus $G(L)$ of $L$ to be
```math
   \textnormal{mass}(G(L)) := \sum_{i=1}^n\frac{1}{\#\textnormal{Aut}(L_i)}.
```
Note that since $L$ is definite, any lattice in the genus of $L$ is also definite, and the
definition makes sense.

```@docs
mass(::HermLat)
```

#### Example

```@repl 2
using Hecke # hide
Qx, x = PolynomialRing(FlintQQ, "x");
f = x^2 - 2;
K, a = NumberField(f, "a", cached = false);
Kt, t = PolynomialRing(K, "t");
g = t^2 + 1;
E, b = NumberField(g, "b", cached = false);
D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1]);
gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [(-3*a + 7)*b + 3*a, (5//2*a - 1)*b - 3//2*a + 4, 0]), map(E, [(3004*a - 4197)*b - 3088*a + 4348, (-1047//2*a + 765)*b + 5313//2*a - 3780, (-a - 1)*b + 3*a - 1]), map(E, [(728381*a - 998259)*b + 3345554*a - 4653462, (-1507194*a + 2168244)*b - 1507194*a + 2168244, (-5917//2*a - 915)*b - 4331//2*a - 488])];
L = hermitian_lattice(E, gens, gram = D);
mass(L)
```

---
---

## Representatives of a genus

```@docs
representative(::LocalGenusHerm)
Base.in(::HermLat, ::LocalGenusHerm)
representative(::GenusHerm)
Base.in(::HermLat, ::GenusHerm)
representatives(::GenusHerm)
genus_representatives(::HermLat)
```

### Examples

```@repl 2
using Hecke # hide
Qx, x = QQ["x"];
K, a = NumberField(x^2 - 2, "a");
Kt, t  = K["t"];
E, b = NumberField(t^2 - a, "b");
OK = maximal_order(K);
p = prime_decomposition(OK, 2)[1][1];
g1 = genus(HermLat, E, p, [(0, 1, 1, 0), (2, 2, -1, 1)], type = :det);
infp = infinite_places(E);
SEK = unique([r.base_field_place for r in infp if isreal(r.base_field_place) && !isreal(r)]);
G1 = genus([g1], [(SEK[1], 1)]);
L1 = representative(g1)
L1 in g1
L2 = representative(G1)
L2 in G1, L2 in g1
length(genus_representatives(L1))
length(representatives(G1))
```

---

## Sum of genera

```@docs
orthogonal_sum(::LocalGenusHerm, ::LocalGenusHerm)
orthogonal_sum(::GenusHerm, ::GenusHerm)
```

### Examples

```@repl 2
using Hecke # hide
Qx, x = QQ["x"];
K, a = NumberField(x^2 - 2, "a");
Kt, t  = K["t"];
E, b = NumberField(t^2 - a, "b");
OK = maximal_order(K);
p = prime_decomposition(OK, 2)[1][1];
g1 = genus(HermLat, E, p, [(0, 1, 1, 0), (2, 2, -1, 1)], type = :det);
infp = infinite_places(E);
SEK = unique([r.base_field_place for r in infp if isreal(r.base_field_place) && !isreal(r)]);
G1 = genus([g1], [(SEK[1], 1)]);
D = matrix(E, 3, 3, [5//2*a - 4, 0, 0, 0, a, a, 0, a, -4*a + 8]);
gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [1, 0, 0]), map(E, [a, 0, 0]), map(E, [b, 0, 0]), map(E, [a*b, 0, 0]), map(E, [0, 1, 0]), map(E, [0, a, 0]), map(E, [0, b, 0]), map(E, [0, a*b, 0]), map(E, [0, 0, 1]), map(E, [0, 0, a]), map(E, [0, 0, b]), map(E, [0, 0, a*b])];
L = hermitian_lattice(E, gens, gram = D);
g2 = genus(L, p);
G2 = genus(L);
orthogonal_sum(g1, g2)
orthogonal_sum(G1, G2)
```

---

## Enumeration of genera

```@docs
local_genera_hermitian(E, p, ::Int, ::Int, ::Int)
genera_hermitian(E, rank, signatures, determinant, max_scale = nothing)
```

### Examples

```@repl 2
using Hecke # hide
K, a = CyclotomicRealSubfield(8, "a");
Kt, t = K["t"];
E, b = number_field(t^2 - a * t + 1);
p = prime_decomposition(maximal_order(K), 2)[1][1];
local_genera_hermitian(E, p, 4, 2, 4)
infp = infinite_places(E);
SEK = unique([r.base_field_place for r in infp if isreal(r.base_field_place) && !isreal(r)]);
genera_hermitian(E, 3, Dict(SEK[1] => 1, SEK[2] => 1), 30 * maximal_order(E))
```

