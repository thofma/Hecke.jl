```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```

# Ideals

## Creation of ideals

Ideals of finite rings can be constructed using the `ideal` method with a mandator `side` keyword argument to specify if a left, right, or two-sided ideal is to be constructed.

```jldoctest
julia> R, f = finite_ring(matrix_algebra(GF(2), 2));

julia> a = R([1, 0, 0, 0]); # this is the elementary matrix e12

julia> I = ideal(R, a; side = :left);

julia> I = ideal(R, a; side = :left);

julia> additive_generators(I)
2-element Vector{FiniteRingElem}:
 Finite ring element [1, 0, 0, 0]
 Finite ring element [0, 1, 0, 0]

julia> J = ideal(R, a; side = :right);

julia> additive_generators(J)
2-element Vector{FiniteRingElem}:
 Finite ring element [0, 0, 1, 0]
 Finite ring element [1, 0, 0, 0]

julia> K = ideal(R, a; side = :twosided);

julia> additive_generators(K)
4-element Vector{FiniteRingElem}:
 Finite ring element [0, 1, 0, 0]
 Finite ring element [0, 0, 1, 0]
 Finite ring element [0, 0, 0, 1]
 Finite ring element [1, 0, 0, 0]
```

## Radical

```@docs
radical(::FiniteRing)
```

## Quotient rings

Given a two-sided ideal, one can construct the quotient ring (as a finite ring) using the `quo` method:

```jldoctest
julia> R, = finite_ring(GF(2)[small_group(4, 2)]);

julia> J = radical(R);

julia> S, RtoS = quo(R, J);

julia> S
Finite ring with additive group
  isomorphic to Z/2
  and with 1 generator and 1 relation
```
