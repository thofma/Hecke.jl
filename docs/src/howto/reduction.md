# Reduction of polynomials over number fields modulo a prime ideal

Given a polynomial $f \in K[x]$ and a prime ideal $\mathfrak p$ of $\mathcal O_K$,
we want to determine the reduction $\bar f \in F[x]$, where $F = \mathcal O_K/\mathfrak p$
is the residue field.
Concretely, we want to reduce the polynomial
``f = x^3 + (1 + ζ_7 + ζ_7^2)x^2 + (23 + 55ζ_7^5)x + (ζ_7 + 77)/2``
over ``\mathbf{Q}(\zeta_7)``.
We begin by defining the cyclotomic field and the polynomial.

```@repl 1
using Hecke # hide
K, ζ = cyclotomic_field(7);
Kx, x = K['x'];
f = x^3 + (1 + ζ + ζ^2)*x^2 + (23 + 55ζ^5)x + (ζ + 77)//2
```

Next we determine the ring of integers ``\mathcal O_K`` and a prime ideal
``\mathfrak p`` lying above the prime ``p = 29``.

```@repl 1
OK = maximal_order(K);
p = 29;
frakp = prime_decomposition(OK, p)[1][1]
```

We can now determine the residue field ``F = \mathcal{O}_K/\mathfrak p`` and
the canonical map ``\mathcal O_K \to F``.

```@repl 1
F, reduction_map_OK = residue_field(OK, frakp);
F
reduction_map_OK
```

Not that the reduction map has domain ``\mathcal O_K`` and thus cannot be applied
to elements of ``K``. We can extend it to the set of ``\mathfrak p``-integral elements
by invoking the `extend` function.
Not that the domain of the extended map will be the whole ``K``, but the map
will throw an error when applied to elements which are not ``\mathfrak p``-integral.

```@repl 1
reduction_map_extended = extend(reduction_map_OK, K)
reduction_map_extended(K(1//3))
reduction_map_extended(K(1//29))
```

Finally we can reduce ``f`` modulo ``\mathfrak p``, which we obtain by applying
the reduction map to the coefficients.

```@repl 1
fbar = map_coefficients(reduction_map_extended, f)
base_ring(fbar) === F
```
