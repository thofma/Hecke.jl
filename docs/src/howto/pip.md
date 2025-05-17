```@meta
CurrentModule = Hecke
DocTestSetup = Hecke.doctestsetup()
```

# Test if an ideal is principal

```jldoctest 1; filter = r"true,*"
julia> Qx, x = QQ[:x];

julia> K, a = number_field(x^2 - 10, :a);

julia> OK = ring_of_integers(K);

julia> P, = prime_ideals_over(OK, 2);

julia> basis_matrix(P)
[2   0]
[0   1]

julia> is_principal(P)
false

julia> is_principal(P^2)
true

julia> is_principal_with_data(P^2)
(true, 2)
```
