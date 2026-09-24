```@meta
CurrentModule = Hecke.EmbeddedModules
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```

# Embedded modules

An embedded module is an $R$-module contained in $S^n$, where $R$ and $S$ are
commutative rings and $R$ embeds into $S$. In particular, $S$ may be $R$ itself
or an overring such as the fraction field of $R$. Typical examples are
$\mathbf Z$-modules in $\mathbf Q^n$ and modules over a polynomial ring or a
Dedekind domain inside a corresponding ambient module.

The aim is to provide a ring-agnostic interface for working with such modules.
Users of the interface should be able to construct modules, test membership and
containment, obtain bases and coordinates, and perform operations such as sums
and intersections without having to know how the module is represented.

Internally, the appropriate representation depends on the coefficient ring.
Modules over principal ideal domains can be described by ordinary matrices and
computed using suitable normal forms, such as Hermite or Popov forms, while
modules over Dedekind domains require pseudo-matrices and pseudo-Hermite normal
forms. `EmbeddedModule` hides these matrix and pseudo-matrix details behind a
common interface so that higher-level code can be written independently of
this distinction.

Matrices in this interface act on the right: their rows are generators or
basis elements of the embedded module.

## Construction

```@docs
embedded_module
```

Here `R` is the coefficient ring, `S` is an overring of `R`, and the rows of
`G` generate an $R$-module in $S^n$. The case `R === S` is allowed. For a
principal ideal domain, `G` is an ordinary matrix. For a Dedekind domain, it is
a pseudo-matrix whose coefficient ideals specify the multiples allowed for
each row.

By default the rows of `G` are only assumed to generate the module. A basis is
computed and cached when it is first needed. Setting `is_basis_matrix = true`
declares that `G` is already a basis matrix or a pseudo-basis matrix. For a
full-rank module, `inverse` can be used to supply the inverse of that basis
matrix and avoid computing it later.

The optional `overstructure` identifies the ambient mathematical object whose
coordinates are represented by $S^n$. For example, an order lattice uses its
ambient algebra as the overstructure. It does not affect the module itself,
but it is used when deciding whether two embedded modules are compatible.

```@example embedded_modules_integer
using Hecke

M = Hecke.embedded_module(ZZ, QQ, QQ[2 0; 0 3])

@assert Hecke.ring(M) === ZZ
@assert Hecke.overring(M) === QQ
@assert Hecke.overstructure(M) === nothing
@assert Hecke.ambient_rank(M) == 2
nothing
```

The zero module in $S^n$ can be constructed without first creating an empty
matrix:

```@example embedded_modules_integer
Z = Hecke.zero_embedded_module(ZZ, QQ, 2)
@assert rank(Z) == 0
@assert Hecke.ambient_rank(Z) == 2
nothing
```

## Elements and coordinates

An `EmbeddedModuleElem` can store both coordinates with respect to a module
basis and coordinates in the ambient space. Either representation is computed
from the other when needed and then cached.

The low-level constructors `_element_from_coordinates` and
`_element_from_ambient_coordinates` are useful to code that wraps embedded
modules in a higher-level structure. The former takes a vector over $R$; the
latter takes a vector over $S$ and, by default, checks that it belongs to the
module. Passing `check = false` skips this membership check and should only be
done when containment is already known.

```@example embedded_modules_integer
a = Hecke._element_from_coordinates(M, ZZRingElem[2, -1])
@assert parent(a) === M
@assert coordinates(a) == ZZRingElem[2, -1]
@assert Hecke.ambient_coordinates(a) == QQFieldElem[4, -3]

b = Hecke._element_from_ambient_coordinates(M, QQFieldElem[4, 6])
@assert coordinates(b) == ZZRingElem[2, 2]
nothing
```

Ambient vectors can be tested for membership directly. Their entries must
belong to the ambient ring.

```@example embedded_modules_integer
@assert QQFieldElem[4, 6] in M
@assert !(QQFieldElem[1, 0] in M)
nothing
```

For a Dedekind domain, a `PseudoElement` pairs an ambient element with a
fractional coefficient ideal. Membership of such a pseudo-element means that
all coefficient-ideal multiples of the element lie in the embedded module. The
functions `element` and `fractional_ideal` return its two components.

## Bases and generators

The input generators and the computed basis are intentionally separate. This
allows construction to remain cheap and lets the implementation choose the
normal-form algorithm appropriate for `R`.

| Function | Meaning |
|:--|:--|
| `generator_matrix(M)` | the original generating matrix or pseudo-matrix |
| `basis_matrix(M)` | a cached basis matrix or pseudo-basis matrix |
| `rank(M)` | the rank of the module over `ring(M)` |
| `ambient_rank(M)` | the dimension $n$ of the ambient space $S^n$ |
| `has_full_rank(M)` | whether `rank(M) == ambient_rank(M)` |
| `basis_matrix_inverse(M)` | the inverse of a full-rank basis matrix |

For PID coefficients, `basis_matrix(M)` is a matrix over `overring(M)`.
`basis_matrix_components(M)` gives an integral numerator matrix over `ring(M)`
and a common denominator. For Dedekind coefficients, `basis_matrix(M)` returns
a pseudo-matrix; its matrix and coefficient ideals can be accessed with
`matrix` and `coefficient_ideals`.

```@example embedded_modules_integer
@assert rank(M) == 2
@assert Hecke.has_full_rank(M)
@assert basis_matrix(M) == QQ[2 0; 0 3]
@assert Hecke.basis_matrix_components(M) == (ZZ[2 0; 0 3], ZZ(1))
nothing
```

## Containment and set-theoretic operations

Two embedded modules are compatible when they have identical coefficient
rings, ambient rings, and overstructures, and have the same ambient rank. The
overstructures are compared by identity. Use `is_compatible(M, N)` to test this
condition.

The common interface provides:

- `x in M` for element membership;
- `issubset(N, M)` for module containment;
- `M + N` for the sum;
- `intersect(M, N)` for the intersection;
- `M == N` for equality as embedded modules; and
- `index(N, M)` for the index $[M:N]$ when `N` is contained in `M` and both
  have the same rank. The index operation is currently implemented for PID
  coefficients.

Except for equality, binary module operations require compatible operands and
throw an error otherwise. The resulting sum and intersection retain the common
overstructure.

```@example embedded_modules_integer
N = Hecke.embedded_module(ZZ, QQ, QQ[4 0; 0 6])

@assert Hecke.is_compatible(M, N)
@assert issubset(N, M)
@assert M + N == M
@assert intersect(M, N) == N
@assert Hecke.index(N, M) == 4
nothing
```

## Quotients

If `N` is contained in `M`, then `quo(M, N)` returns a finitely generated
module representing $M/N$ together with a map from `M` to the quotient. The map
accepts `EmbeddedModuleElem` objects and supports taking preimages.

When $M/N$ is a vector space over the residue field $R/(p)$,
`quotient_vector_space(M, N, p)` returns that vector space, the quotient map,
and the residue-field map. In particular, all invariant factors of $M/N$ must
be associated to the prime element `p`.

```@example embedded_modules_integer
Q, MtoQ = quo(M, N)
x = Hecke._element_from_coordinates(M, ZZRingElem[1, 0])
y = Hecke._element_from_coordinates(M, ZZRingElem[2, 0])
@assert !iszero(MtoQ(x))
@assert iszero(MtoQ(y))

V, MtoV, ZZtoF = Hecke.quotient_vector_space(M, N, ZZ(2))
@assert dim(V) == 2
@assert !iszero(MtoV(x))
@assert iszero(MtoV(y))
nothing
```

## Examples

The same interface applies to polynomial rings and degree localizations. The
choice of normal form is hidden from the caller.

```@example embedded_modules_function_fields
using Hecke

K, x = rational_function_field(QQ, "x")
R = parent(numerator(x))

M = Hecke.embedded_module(R, K, K[x 0; 0 1])
@assert typeof(x)[x, x + 1] in M
@assert !(typeof(x)[K(1), K(0)] in M)

Rinf = localization(K, degree)
Minf = Hecke.embedded_module(Rinf, K, K[1//x 0; 0 1])
@assert typeof(x)[inv(x), (x + 1)//x] in Minf
@assert !(typeof(x)[K(1), K(0)] in Minf)
nothing
```

Over a Dedekind domain, construction uses a pseudo-matrix, but accessors and
set-theoretic operations have the same interface. See also
[Pseudo-matrices](@ref PMatLink).

```@example embedded_modules_dedekind
using Hecke

K, = quadratic_field(5)
O = maximal_order(K)
P = pseudo_matrix(identity_matrix(K, 2))
M = Hecke.embedded_module(O, K, P)

v = elem_type(K)[K(1), K(0)]
w = elem_type(K)[K(1)//2, K(0)]
@assert Hecke._pseudo_element(v, O) in M
@assert !(Hecke._pseudo_element(w, O) in M)

N = Hecke.embedded_module(O, K, 2*basis_matrix(M))
@assert M + N == M
@assert intersect(M, N) == N
nothing
```
