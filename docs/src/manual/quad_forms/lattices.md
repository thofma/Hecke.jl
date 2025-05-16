```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# Lattices


## Creation of lattices

### Inside a given ambient space

```@docs
lattice(::AbstractSpace)
lattice(::AbstractSpace, ::PMat)
lattice(::AbstractSpace, ::MatElem)
lattice(::AbstractSpace, ::Vector)
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

```jldoctest; filter = r".*"
julia> K, a = rationals_as_number_field();

julia> Kt, t = K[:t];

julia> g = t^2 + 7;

julia> E, b = number_field(g, :b);

julia> D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);

julia> gens = Vector{AbsSimpleNumFieldElem}[map(K, [1, 1, 0]), map(K, [1, 0, 1]), map(K, [2, 0, 0])];

julia> Lquad = quadratic_lattice(K, gens, gram = D)
Quadratic lattice of rank 3 and degree 3
  over maximal order of number field of degree 1 over QQ
  with basis [1]

julia> D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]);

julia> gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [2, -1, 0, 0]), map(E, [-3, 0, -1, 0]), map(E, [0, 0, 0, -1]), map(E, [b, 0, 0, 0])];

julia> Lherm = hermitian_lattice(E, gens, gram = D)
Hermitian lattice of rank 4 and degree 4
  over relative maximal order of Relative number field of degree 2 over K
  with pseudo-basis
  (1, 1//1 * <1, 1>)
  (b + 1, 1//2 * <1, 1>)
```

Note that the format used here is the one given by the internal function
`Hecke.to_hecke()` which prints REPL commands to get back the input lattice.

```jldoctest; filter = r".*"
julia> K, a = rationals_as_number_field();

julia> Kt, t = K[:t];

julia> g = t^2 + 7;

julia> E, b = number_field(g, :b);

julia> D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]);

julia> gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [2, -1, 0, 0]), map(E, [-3, 0, -1, 0]), map(E, [0, 0, 0, -1]), map(E, [b, 0, 0, 0])];

julia> Lherm = hermitian_lattice(E, gens, gram = D);

julia> Hecke.to_hecke(Lherm)
Qx, x = polynomial_ring(QQ, :x)
f = x - 1
K, a = number_field(f, :a, cached = false)
Kt, t = polynomial_ring(K, :t)
g = t^2 + 7
E, b = number_field(g, :b, cached = false)
D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [2, -1, 0, 0]), map(E, [-3, 0, -1, 0]), map(E, [0, 0, 0, -1]), map(E, [b, 0, 0, 0])]
L = hermitian_lattice(E, gens, gram = D)
```

Finally, one can access some databases in which are stored several quadratic and
hermitian lattices. Up to now, these are not automatically available while running
Hecke. It can nonetheless be used in the following way:

```jldoctest; filter = r".*"
julia> qld = Hecke.quadratic_lattice_database()
Quadratic lattices of rank >= 3 with class number 1 or 2
Author: Markus Kirschmer
Source: http://www.math.rwth-aachen.de/~Markus.Kirschmer/forms/
Version: 0.0.1
Number of lattices: 30250

julia> lattice(qld, 1)
Quadratic lattice of rank 3 and degree 3
  over maximal order of number field of degree 1 over QQ
  with basis [1]

julia> hlb = Hecke.hermitian_lattice_database()
Hermitian lattices of rank >= 3 with class number 1 or 2
Author: Markus Kirschmer
Source: http://www.math.rwth-aachen.de/~Markus.Kirschmer/forms/
Version: 0.0.1
Number of lattices: 570

julia> lattice(hlb, 426)
Hermitian lattice of rank 4 and degree 4
  over relative maximal order of Relative number field of degree 2 over number field
  with pseudo-basis
  (1, 1//1 * <1, 1>)
  (b + 1, 1//2 * <1, 1>)
```

---

## Ambient space and rational span

```@docs
ambient_space(::AbstractLat)
rational_span(::AbstractLat)
basis_matrix_of_rational_span(::AbstractLat)
gram_matrix_of_rational_span(::AbstractLat)
diagonal_of_rational_span(::AbstractLat)
```

### Examples

```jldoctest; filter = r".*"
julia> K, a = rationals_as_number_field();

julia> Kt, t = K[:t];

julia> g = t^2 + 7;

julia> E, b = number_field(g, :b);

julia> D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);

julia> gens = Vector{AbsSimpleNumFieldElem}[map(K, [1, 1, 0]), map(K, [1, 0, 1]), map(K, [2, 0, 0])];

julia> Lquad = quadratic_lattice(K, gens, gram = D);

julia> D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]);

julia> gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [2, -1, 0, 0]), map(E, [-3, 0, -1, 0]), map(E, [0, 0, 0, -1]), map(E, [b, 0, 0, 0])];

julia> Lherm = hermitian_lattice(E, gens, gram = D);

julia> ambient_space(Lherm)
Hermitian space of dimension 4
  over relative number field with defining polynomial t^2 + 7
    over number field with defining polynomial x - 1
      over rational field
with gram matrix
[1   0   0   0]
[0   1   0   0]
[0   0   1   0]
[0   0   0   1]

julia> rational_span(Lquad)
Quadratic space of dimension 3
  over number field of degree 1 over QQ
with gram matrix
[2   2   2]
[2   4   2]
[2   2   4]

julia> basis_matrix_of_rational_span(Lherm)
[1   0   0   0]
[5   1   0   0]
[3   0   1   0]
[0   0   0   1]

julia> gram_matrix_of_rational_span(Lherm)
[1    5    3   0]
[5   26   15   0]
[3   15   10   0]
[0    0    0   1]

julia> diagonal_of_rational_span(Lquad)
3-element Vector{AbsSimpleNumFieldElem}:
 2
 2
 2
```

---

## Rational equivalence

```@docs
hasse_invariant(L::QuadLat, p)
witt_invariant(L::QuadLat, p)
is_rationally_isometric(::AbstractLat, ::AbstractLat, ::AbsNumFieldOrderIdeal)
is_rationally_isometric(L::AbstractLat, M::AbstractLat)
```

### Examples
For now and for the rest of this section, the examples will include the new lattice
`Lquad2` which is quadratic. Moreover, all the completions are going to be done at
the prime ideal $p = 7*\mathcal O_K$.

```jldoctest; filter = r".*"
julia> K, a = rationals_as_number_field();

julia> D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);

julia> gens = Vector{AbsSimpleNumFieldElem}[map(K, [1, 1, 0]), map(K, [1, 0, 1]), map(K, [2, 0, 0])];

julia> Lquad = quadratic_lattice(K, gens, gram = D);

julia> D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);

julia> gens = Vector{AbsSimpleNumFieldElem}[map(K, [-35, 25, 0]), map(K, [30, 40, -20]), map(K, [5, 10, -5])];

julia> Lquad2 = quadratic_lattice(K, gens, gram = D)
Quadratic lattice of rank 3 and degree 3
  over maximal order of number field of degree 1 over QQ
  with basis [1]

julia> OK = maximal_order(K);

julia> p = prime_decomposition(OK, 7)[1][1]
<7, 7>
Norm: 7
Minimum: 7
principal generator 7
two normal wrt: 7

julia> hasse_invariant(Lquad, p), witt_invariant(Lquad, p)
(1, 1)

julia> is_rationally_isometric(Lquad, Lquad2, p)
true

julia> is_rationally_isometric(Lquad, Lquad2)
true
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
rank(L::AbstractLat)
degree(L::AbstractLat)
discriminant(::AbstractLat)
base_field(::AbstractLat)
base_ring(::AbstractLat)
fixed_field(::AbstractLat)
fixed_ring(::AbstractLat)
involution(::AbstractLat)
pseudo_matrix(::AbstractLat)
pseudo_basis(::AbstractLat)
coefficient_ideals(::AbstractLat)
absolute_basis_matrix(::AbstractLat)
absolute_basis(::AbstractLat)
generators(L::AbstractLat; minimal::Bool = false)
gram_matrix_of_generators(::AbstractLat; minimal::Bool = false)
```

### Examples

```jldoctest; filter = r".*"
julia> K, a = rationals_as_number_field();

julia> Kt, t = K[:t];

julia> g = t^2 + 7;

julia> E, b = number_field(g, :b);

julia> D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]);

julia> gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [2, -1, 0, 0]), map(E, [-3, 0, -1, 0]), map(E, [0, 0, 0, -1]), map(E, [b, 0, 0, 0])];

julia> Lherm = hermitian_lattice(E, gens, gram = D);

julia> rank(Lherm), degree(Lherm)
(4, 4)

julia> discriminant(Lherm)
Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <7, 7>) * [1 0]
(1//2 * <7, 7>) * [0 1]

julia> base_field(Lherm)
Relative number field with defining polynomial t^2 + 7
  over number field with defining polynomial x - 1
    over rational field

julia> base_ring(Lherm)
Relative maximal order of Relative number field of degree 2 over K
with pseudo-basis
(1, 1//1 * <1, 1>)
(b + 1, 1//2 * <1, 1>)

julia> fixed_field(Lherm)
Number field with defining polynomial x - 1
  over rational field

julia> fixed_ring(Lherm)
Maximal order of number field of degree 1 over QQ
with basis [1]

julia> involution(Lherm)
Map
  from relative number field of degree 2 over K
  to relative number field of degree 2 over K

julia> pseudo_matrix(Lherm)
Pseudo-matrix over Relative maximal order of Relative number field of degree 2 over K
with pseudo-basis
(1, 1//1 * <1, 1>)
(b + 1, 1//2 * <1, 1>)
Fractional ideal with row [1 0 0 0]
Fractional ideal with row [5 1 0 0]
Fractional ideal with row [3 0 1 0]
Fractional ideal with row [0 0 0 1]

julia> pseudo_basis(Lherm)
4-element Vector{Tuple{Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}, Hecke.RelNumFieldOrderFractionalIdeal{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal, Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}}}:
 ([1, 0, 0, 0], Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <7, 28>) * [1 0]
(1//2 * <1, 1>) * [6 1])
 ([5, 1, 0, 0], Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//2 * <1, 1>) * [0 1])
 ([3, 0, 1, 0], Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//2 * <1, 1>) * [0 1])
 ([0, 0, 0, 1], Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//2 * <1, 1>) * [0 1])

julia> coefficient_ideals(Lherm)
4-element Vector{Hecke.RelNumFieldOrderFractionalIdeal{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal, Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}}:
 Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <7, 28>) * [1 0]
(1//2 * <1, 1>) * [6 1]
 Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//2 * <1, 1>) * [0 1]
 Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//2 * <1, 1>) * [0 1]
 Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//2 * <1, 1>) * [0 1]

julia> absolute_basis_matrix(Lherm)
[            7               0               0               0]
[1//2*b + 7//2               0               0               0]
[            5               1               0               0]
[5//2*b + 5//2   1//2*b + 1//2               0               0]
[            3               0               1               0]
[3//2*b + 3//2               0   1//2*b + 1//2               0]
[            0               0               0               1]
[            0               0               0   1//2*b + 1//2]

julia> absolute_basis(Lherm)
8-element Vector{Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}}:
 [7, 0, 0, 0]
 [1//2*b + 7//2, 0, 0, 0]
 [5, 1, 0, 0]
 [5//2*b + 5//2, 1//2*b + 1//2, 0, 0]
 [3, 0, 1, 0]
 [3//2*b + 3//2, 0, 1//2*b + 1//2, 0]
 [0, 0, 0, 1]
 [0, 0, 0, 1//2*b + 1//2]

julia> generators(Lherm)
4-element Vector{Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}}:
 [2, -1, 0, 0]
 [-3, 0, -1, 0]
 [0, 0, 0, -1]
 [b, 0, 0, 0]

julia> gram_matrix_of_generators(Lherm)
[  5     -6   0   -2*b]
[ -6     10   0    3*b]
[  0      0   1      0]
[2*b   -3*b   0      7]
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
Base.:(+)(::AbstractLat, ::AbstractLat)
Base.:(*)(::NumFieldElem, ::AbstractLat)
Base.:(*)(::NumFieldOrderIdeal, ::AbstractLat)
Base.:(*)(::NumFieldOrderFractionalIdeal, ::AbstractLat)
rescale(::AbstractLat, ::NumFieldElem)
dual(::AbstractLat)
intersect(::AbstractLat, ::AbstractLat)
primitive_closure(::AbstractLat, ::AbstractLat)
orthogonal_submodule(::AbstractLat, ::AbstractLat)
```

### Examples

```jldoctest; filter = r".*"
julia> K, a = rationals_as_number_field();

julia> D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);

julia> gens = Vector{AbsSimpleNumFieldElem}[map(K, [1, 1, 0]), map(K, [1, 0, 1]), map(K, [2, 0, 0])];

julia> Lquad = quadratic_lattice(K, gens, gram = D);

julia> D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);

julia> gens = Vector{AbsSimpleNumFieldElem}[map(K, [-35, 25, 0]), map(K, [30, 40, -20]), map(K, [5, 10, -5])];

julia> Lquad2 = quadratic_lattice(K, gens, gram = D);

julia> OK = maximal_order(K);

julia> p = prime_decomposition(OK, 7)[1][1];

julia> pseudo_matrix(Lquad + Lquad2)
Pseudo-matrix over Maximal order of number field of degree 1 over QQ
with basis [1]
1//1 * <2, 2> with row [1 0 0]
1//1 * <1, 1> with row [1 1 0]
1//1 * <1, 1> with row [1 0 1]

julia> pseudo_matrix(intersect(Lquad, Lquad2))
Pseudo-matrix over Maximal order of number field of degree 1 over QQ
with basis [1]
1//1 * <10, 10> with row [1 0 0]
1//1 * <25, 25> with row [1//5 1 0]
1//1 * <5, 5> with row [0 3 1]

julia> pseudo_matrix(p*Lquad)
Pseudo-matrix over Maximal order of number field of degree 1 over QQ
with basis [1]
1//1 * <14, 126> with row [1 0 0]
1//1 * <7, 7> with row [1 1 0]
1//1 * <7, 7> with row [1 0 1]

julia> ambient_space(rescale(Lquad,3*a))
Quadratic space of dimension 3
  over number field of degree 1 over QQ
with gram matrix
[6   0   0]
[0   6   0]
[0   0   6]

julia> pseudo_matrix(Lquad)
Pseudo-matrix over Maximal order of number field of degree 1 over QQ
with basis [1]
1//1 * <2, 2> with row [1 0 0]
1//1 * <1, 1> with row [1 1 0]
1//1 * <1, 1> with row [1 0 1]
```

## Categorical constructions
Given finite collections of lattices, one can construct their direct sums, which
are also direct products in this context. They are also sometimes called biproducts.
Depending on the user usage, it is possible to call one of the following functions.

```@docs
direct_sum(::Vector{AbstractLat})
direct_product(::Vector{AbstractLat})
biproduct(::Vector{AbstractLat})
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

```@docs
norm(::AbstractLat)
scale(L::AbstractLat)
volume(L::AbstractLat)
```

### Examples

```jldoctest; filter = r".*"
julia> K, a = rationals_as_number_field();

julia> Kt, t = K[:t];

julia> g = t^2 + 7;

julia> E, b = number_field(g, :b);

julia> D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]);

julia> gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [2, -1, 0, 0]), map(E, [-3, 0, -1, 0]), map(E, [0, 0, 0, -1]), map(E, [b, 0, 0, 0])];

julia> Lherm = hermitian_lattice(E, gens, gram = D);

julia> norm(Lherm)
1//1 * <1, 1>
Norm: 1
Minimum: 1
principal generator 1
basis_matrix
[1]
two normal wrt: 2

julia> scale(Lherm)
Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//2 * <1, 1>) * [0 1]

julia> volume(Lherm)
Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <7, 7>) * [1 0]
(1//2 * <7, 7>) * [0 1]
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
is_integral(::AbstractLat)
is_modular(::AbstractLat)
is_modular(::AbstractLat, p)
is_positive_definite(L::AbstractLat)
is_negative_definite(L::AbstractLat)
is_definite(L::AbstractLat)
can_scale_totally_positive(L::AbstractLat)
```

### Examples

```jldoctest; filter = r".*"
julia> K, a = rationals_as_number_field();

julia> Kt, t = K[:t];

julia> g = t^2 + 7;

julia> E, b = number_field(g, :b);

julia> D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]);

julia> gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [2, -1, 0, 0]), map(E, [-3, 0, -1, 0]), map(E, [0, 0, 0, -1]), map(E, [b, 0, 0, 0])];

julia> Lherm = hermitian_lattice(E, gens, gram = D);

julia> OK = maximal_order(K);

julia> is_integral(Lherm)
true

julia> is_modular(Lherm)[1]
false

julia> p = prime_decomposition(OK, 7)[1][1];

julia> is_modular(Lherm, p)
(false, 0)

julia> is_positive_definite(Lherm)
true

julia> can_scale_totally_positive(Lherm)
(true, 1)
```
---

## Local properties

```@docs
local_basis_matrix(L::AbstractLat, p; type::Symbol = :any)
jordan_decomposition(L::AbstractLat, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
is_isotropic(::AbstractLat, p)
```

### Examples

```jldoctest; filter = r".*"
julia> K, a = rationals_as_number_field();

julia> D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);

julia> gens = Vector{AbsSimpleNumFieldElem}[map(K, [1, 1, 0]), map(K, [1, 0, 1]), map(K, [2, 0, 0])];

julia> Lquad = quadratic_lattice(K, gens, gram = D);

julia> OK = maximal_order(K);

julia> p = prime_decomposition(OK, 7)[1][1];

julia> local_basis_matrix(Lquad, p)
[1   0   0]
[1   1   0]
[1   0   1]

julia> jordan_decomposition(Lquad, p)
(AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem}[[1 0 0; 0 1 0; 0 0 1]], AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem}[[2 0 0; 0 2 0; 0 0 2]], [0])

julia> is_isotropic(Lquad, p)
true
```

---

## Automorphisms for definite lattices
Let $L$ and $L'$ be two lattices over the same extension $E/K$, inside their
respective ambient spaces $(V, \Phi)$ and $(V', \Phi')$. Similarly to homomorphisms
of spaces, we define a *homomorphism of lattices* from $L$ to $L'$ to be an
$\mathcal{O}_E$-module$ homomorphism $f \colon L \to L'$ such that for all
$x,y \in L$, one has

```math
   \Phi'(f(x), f(y)) = \Phi(x,y).
```

Again, any automorphism of lattices is called an *isometry* and any monomorphism is
called an *embedding*. We refer to the set of isometries from a lattice $L$ to itself
as the *automorphism group of $L$*.

```@docs
automorphism_group_order(::AbstractLat)
automorphism_group_generators(::AbstractLat)
```

### Examples

```jldoctest; filter = r".*"
julia> K, a = rationals_as_number_field();

julia> Kt, t = K[:t];

julia> g = t^2 + 7;

julia> E, b = number_field(g, :b);

julia> D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);

julia> gens = Vector{AbsSimpleNumFieldElem}[map(K, [1, 1, 0]), map(K, [1, 0, 1]), map(K, [2, 0, 0])];

julia> Lquad = quadratic_lattice(K, gens, gram = D);

julia> is_definite(Lquad)
true

julia> automorphism_group_order(Lquad)
48

julia> automorphism_group_generators(Lquad)
6-element Vector{AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem}}:
 [-1 0 0; 0 -1 0; 0 0 -1]
 [1 0 0; 0 -1 0; 0 0 -1]
 [1 0 0; 0 0 -1; 0 -1 0]
 [0 -1 0; 0 0 -1; 1 0 0]
 [1 0 0; 0 1 0; 0 0 -1]
 [0 1 0; 1 0 0; 0 0 1]
```

---

## Isometry

```@docs
is_isometric(::AbstractLat, ::AbstractLat)
is_isometric_with_isometry(::AbstractLat, ::AbstractLat)
is_locally_isometric(::AbstractLat, ::AbstractLat, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
```

### Examples

```jldoctest; filter = r".*"
julia> K, a = rationals_as_number_field();

julia> D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);

julia> gens = Vector{AbsSimpleNumFieldElem}[map(K, [1, 1, 0]), map(K, [1, 0, 1]), map(K, [2, 0, 0])];

julia> Lquad = quadratic_lattice(K, gens, gram = D);

julia> D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2]);

julia> gens = Vector{AbsSimpleNumFieldElem}[map(K, [-35, 25, 0]), map(K, [30, 40, -20]), map(K, [5, 10, -5])];

julia> Lquad2 = quadratic_lattice(K, gens, gram = D);

julia> OK = maximal_order(K);

julia> p = prime_decomposition(OK, 7)[1][1];

julia> is_isometric(Lquad, Lquad2)
false

julia> is_locally_isometric(Lquad, Lquad2, p)
true
```

---

## Maximal integral lattices

```@docs
is_maximal_integral(::AbstractLat, p)
is_maximal_integral(::AbstractLat)
is_maximal(::AbstractLat, p)
maximal_integral_lattice(::AbstractLat, p)
maximal_integral_lattice(::AbstractLat)
maximal_integral_lattice(::AbstractSpace)
```

### Examples

```jldoctest; filter = r".*"
julia> K, a = rationals_as_number_field();

julia> Kt, t = K[:t];

julia> g = t^2 + 7;

julia> E, b = number_field(g, :b);

julia> D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]);

julia> gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [2, -1, 0, 0]), map(E, [-3, 0, -1, 0]), map(E, [0, 0, 0, -1]), map(E, [b, 0, 0, 0])];

julia> Lherm = hermitian_lattice(E, gens, gram = D);

julia> OK = maximal_order(K);

julia> p = prime_decomposition(OK, 7)[1][1];

julia> is_maximal_integral(Lherm, p)
(false, Hermitian lattice of rank 4 and degree 4)

julia> is_maximal_integral(Lherm)
(false, Hermitian lattice of rank 4 and degree 4)

julia> is_maximal(Lherm, p)
(false, Hermitian lattice of rank 4 and degree 4)

julia> pseudo_basis(maximal_integral_lattice(Lherm, p))
4-element Vector{Tuple{Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}, Hecke.RelNumFieldOrderFractionalIdeal{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal, Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}}}:
 ([1, 0, 0, 0], Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//2 * <1, 1>) * [0 1])
 ([0, 1, 0, 0], Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//2 * <1, 1>) * [0 1])
 ([2, 4, 1, 0], Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//14 * <1, 1>) * [6 1])
 ([4, 5, 0, 1], Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//14 * <1, 1>) * [6 1])

julia> pseudo_basis(maximal_integral_lattice(Lherm))
4-element Vector{Tuple{Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}, Hecke.RelNumFieldOrderFractionalIdeal{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal, Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}}}:
 ([1, 0, 0, 0], Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//2 * <1, 1>) * [0 1])
 ([0, 1, 0, 0], Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//2 * <1, 1>) * [0 1])
 ([2, 4, 1, 0], Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//14 * <1, 1>) * [6 1])
 ([3, 2, 0, 1], Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//14 * <1, 1>) * [6 1])

julia> pseudo_basis(maximal_integral_lattice(ambient_space(Lherm)))
4-element Vector{Tuple{Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}, Hecke.RelNumFieldOrderFractionalIdeal{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal, Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}}}:
 ([1, 0, 0, 0], Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//2 * <1, 1>) * [0 1])
 ([0, 1, 0, 0], Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//2 * <1, 1>) * [0 1])
 ([2, 4, 1, 0], Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//14 * <1, 1>) * [6 1])
 ([4, 5, 0, 1], Fractional ideal of
Relative maximal order with pseudo-basis (1) * 1//1 * <1, 1>, (b + 1) * 1//2 * <1, 1>
with basis pseudo-matrix
(1//1 * <1, 1>) * [1 0]
(1//14 * <1, 1>) * [6 1])
```

