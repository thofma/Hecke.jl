```@meta
CurrentModule = Hecke
DocTestSetup = Hecke.doctestsetup()
```

# Construct a residue field

```jldoctest 1
julia> Qx, x = QQ[:x];

julia> K, a = number_field(x^2 - 10, :a);

julia> OK = ring_of_integers(K);

julia> P, = prime_ideals_over(OK, 2);

julia> Fp, mFp = residue_field(OK, P)
(Prime field of characteristic 2, Map: OK -> Fp)

julia> [mFp(x) for x = basis(OK)]
2-element Vector{FqFieldElem}:
 1
 0
```
