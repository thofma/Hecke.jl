```@meta
CurrentModule = Hecke
DocTestSetup = Hecke.doctestsetup()
```
# Reduction of polynomials over number fields modulo a prime ideal

Given a polynomial $f \in K[x]$ and a prime ideal $\mathfrak p$ of $\mathcal O_K$,
we want to determine the reduction $\bar f \in F[x]$, where $F = \mathcal O_K/\mathfrak p$
is the residue field.
Concretely, we want to reduce the polynomial
``f = x^3 + (1 + ζ_7 + ζ_7^2)x^2 + (23 + 55ζ_7^5)x + (ζ_7 + 77)/2``
over ``\mathbf{Q}(\zeta_7)``.
We begin by defining the cyclotomic field and the polynomial.

```jldoctest 1
julia> K, ζ = cyclotomic_field(7);

julia> Kx, x = K[:x];

julia> f = x^3 + (1 + ζ + ζ^2)*x^2 + (23 + 55ζ^5)x + (ζ + 77)//2
x^3 + (z_7^2 + z_7 + 1)*x^2 + (55*z_7^5 + 23)*x + 1//2*z_7 + 77//2
```

Next we determine the ring of integers ``\mathcal O_K`` and a prime ideal
``\mathfrak p`` lying above the prime ``p = 29``.

```jldoctest 1
julia> OK = maximal_order(K);

julia> p = 29;

julia> frakp = prime_decomposition(OK, p)[1][1]
<29, z_7 + 22>
Norm: 29
Minimum: 29
two normal wrt: 29
```

We can now determine the residue field ``F = \mathcal{O}_K/\mathfrak p`` and
the canonical map ``\mathcal O_K \to F``.

```jldoctest 1
julia> F, reduction_map_OK = residue_field(OK, frakp);

julia> F
Prime field of characteristic 29

julia> reduction_map_OK
Map
  from maximal order of cyclotomic field of order 7
  with basis [1, z_7, z_7^2, z_7^3, z_7^4, z_7^5]
  to prime field of characteristic 29
```

Not that the reduction map has domain ``\mathcal O_K`` and thus cannot be applied
to elements of ``K``. We can extend it to the set of ``\mathfrak p``-integral elements
by invoking the `extend` function.
Not that the domain of the extended map will be the whole ``K``, but the map
will throw an error when applied to elements which are not ``\mathfrak p``-integral.

```jldoctest 1
julia> reduction_map_extended = extend(reduction_map_OK, K)
Map
  from cyclotomic field of order 7
  to prime field of characteristic 29

julia> reduction_map_extended(K(1//3))
10

julia> reduction_map_extended(K(1//29))
ERROR: Element not p-integral
[...]
```

Finally we can reduce ``f`` modulo ``\mathfrak p``, which we obtain by applying
the reduction map to the coefficients.

```jldoctest 1
julia> fbar = map_coefficients(reduction_map_extended, f)
x^3 + 28*x^2 + 4*x + 13

julia> base_ring(fbar) === F
true
```
