```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```

# Basics

Finite rings and their elements implement the ring interface.
We document the methods that are unique to finite rings.

## Creation of finite rings

```@docs
finite_ring(::Vector{<:IntegerUnion}, ::Vector{ZZMatrix})
finite_ring(::Vector{<:IntegerUnion}, ::Array)
finite_ring(::AbstractAssociativeAlgebra)
finite_ring(::AbstractAlgebra.Generic.MatRing{FiniteRingElem})
```

## Properties

```@docs
additive_generators(::FiniteRing)
number_of_additive_generators(::FiniteRing)
elementary_divisors(::FiniteRing)
```

## Maximal quotient rings

```@docs
maximal_p_quotient_ring(::FiniteRing, ::IntegerUnion)
```

## Decomposition

```@docs
central_primitive_idempotents(::FiniteRing)
decompose_into_indecomposable_rings(::FiniteRing)
is_indecomposable(::FiniteRing)
```

## Creaton of elements

Elements of finite rings can be constructed by specifying the coordinates with respect to the additive additive generators or as linear combinations of the additive generators:

```jldoctest
julia> R = finite_ring([6, 6], [ZZ[1 0; 0 0], ZZ[0 0; 0 1]]); # Z/6Z x Z/6Z

julia> x = R([1, 2])
Finite ring element [1, 2]

julia> e1, e2 = additive_generators(R);

julia> y = e1 + 2 * e2;

julia> x == y
true
```

## Conversion to other structures

Finite rings of prime characteristic can be converted to algebras using the `isomorphism` method:

```jldoctest
julia> R, = finite_ring(GF(2)[small_group(8, 3)]);

julia> S = matrix_ring(R, 2);

julia> T, = finite_ring(S);

julia> f = isomorphism(MatAlgebra, R)
Map
  from finite ring
  to matrix algebra of dimension 8 over Prime field of characteristic 2

julia> f = isomorphism(StructureConstantAlgebra, R)
Map
  from finite ring
  to structure constant algebra of dimension 8 over GF(2)
```
