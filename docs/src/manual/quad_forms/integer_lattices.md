```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# Integer Lattices

An integer lattice $L$ is a finitely generated $\mathbb{Z}$-submodule of a quadratic
vector space $V = \mathbb{Q}^n$ over the rational numbers.
Integer lattices are also known as quadratic forms over the integers.
We will refer to them as $\mathbb{Z}$-lattices.

A $\mathbb{Z}$-lattice $L$ has the type `ZZLat`. It is given in terms of
its ambient quadratic space $V$ together with a basis matrix $B$ whose rows span $L$,
i.e. $L = \mathbb{Z}^r B$ where $r$ is the ($\mathbb{Z}$-module) rank of $L$.

To access $V$ and $B$ see [`ambient_space(L::ZZLat)`](@ref) and [`basis_matrix(L::ZZLat)`](@ref).


## Creation of integer lattices

### From a gram matrix

```@docs
integer_lattice(B::QQMatrix)
```

### In a quadratic space

```@docs
lattice(V::QuadSpace{QQField, QQMatrix}, B::MatElem;)
```

### Special lattices

```@docs
root_lattice(::Symbol, ::Int)
hyperbolic_plane_lattice(n::Union{Int64, ZZRingElem})
integer_lattice(S::Symbol, n::Union{Int64, ZZRingElem})
leech_lattice
k3_lattice
mukai_lattice(::Symbol)
hyperkaehler_lattice(::Symbol)
```

### From a genus
Integer lattices can be created as representatives of a genus.
See ([`representative(L::ZZGenus)`](@ref))

### Rescaling the Quadratic Form

```@docs
rescale(::ZZLat, ::RationalUnion)
```

## Attributes

```@docs
ambient_space(L::ZZLat)
basis_matrix(L::ZZLat)
gram_matrix(L::ZZLat)
rational_span(L::ZZLat)
```

## Invariants
```@docs
rank(L::ZZLat)
det(L::ZZLat)

scale(L::ZZLat)
norm(L::ZZLat)
iseven(L::ZZLat)
is_integral(L::ZZLat)

is_primary_with_prime(L::ZZLat)
is_primary(L::ZZLat, p::Union{Integer, ZZRingElem})
is_elementary_with_prime(L::ZZLat)
is_elementary(L::ZZLat, p::Union{Integer, ZZRingElem})
```

### The Genus

For an integral lattice
The genus of an integer lattice collects its local invariants.
[`genus(::ZZLat)`](@ref)
```@docs
mass(L::ZZLat)
genus_representatives(L::ZZLat)
```

### Real invariants
```@docs
signature_tuple(L::ZZLat)
is_positive_definite(L::ZZLat)
is_negative_definite(L::ZZLat)
is_definite(L::ZZLat)
```

## Isometries
```@docs
automorphism_group_generators(L::ZZLat)
automorphism_group_order(L::ZZLat)
is_isometric(L::ZZLat, M::ZZLat)
is_locally_isometric(L::ZZLat, M::ZZLat, p::Int)
```
# Root lattices
```@docs
root_lattice_recognition(L::ZZLat)
root_lattice_recognition_fundamental(L::ZZLat)
ADE_type(G::MatrixElem)
coxeter_number(ADE::Symbol, n)
highest_root(ADE::Symbol, n)
```

## Module operations
Most module operations assume that the lattices live in the same ambient space.
For instance only lattices in the same ambient space compare.

```@docs
Base.:(==)(L1::ZZLat, L2::ZZLat)
is_sublattice(M::ZZLat, N::ZZLat)
is_sublattice_with_relations(M::ZZLat, N::ZZLat)
+(M::ZZLat, N::ZZLat)
Base.:(*)(a::RationalUnion, L::ZZLat)
intersect(M::ZZLat, N::ZZLat)
Base.in(v::Vector, L::ZZLat)
Base.in(v::QQMatrix, L::ZZLat)
primitive_closure(M::ZZLat, N::ZZLat)
is_primitive(M::ZZLat, N::ZZLat)
is_primitive(::ZZLat, ::Union{Vector, QQMatrix})
divisibility(::ZZLat, ::Union{Vector, QQMatrix})
```

## Embeddings

### Categorical constructions
```@docs
direct_sum(x::Vector{ZZLat})
direct_product(x::Vector{ZZLat})
biproduct(x::Vector{ZZLat})
```

### Orthogonal sublattices
```@docs
orthogonal_submodule(::ZZLat, ::ZZLat)
irreducible_components(::ZZLat)
```

### Dual lattice
```@docs
dual(L::ZZLat)
```

### Discriminant group
See [`discriminant_group(L::ZZLat)`](@ref).

### Overlattices
```@docs
glue_map(L::ZZLat, S::ZZLat, R::ZZLat; check=true)
overlattice(glue_map::TorQuadModuleMap)
local_modification(M::ZZLat, L::ZZLat, p)
maximal_integral_lattice(L::ZZLat)
```

### Sublattices defined by endomorphisms
```@docs
kernel_lattice(L::ZZLat, f::MatElem)
invariant_lattice(L::ZZLat, G::Vector{<:MatElem})
coinvariant_lattice(::ZZLat, ::Union{MatElem, Vector{<:MatElem}})
```

### Computing embeddings
```@docs
embed(S::ZZLat, G::ZZGenus)
embed_in_unimodular(::ZZLat, ::IntegerUnion, ::IntegerUnion)
```

## LLL, Short and Close Vectors

### LLL and indefinite LLL
```@docs
lll(L::ZZLat; same_ambient::Bool = true)
```
### Short Vectors
```@docs
short_vectors
shortest_vectors
short_vectors_iterator
minimum(L::ZZLat)
kissing_number(L::ZZLat)
```

### Short Vectors affine

```@docs
enumerate_quadratic_triples
short_vectors_affine(::ZZLat, ::QQMatrix, ::RationalUnion, ::RationalUnion)
short_vectors_affine(::QQMatrix, ::QQMatrix, ::RationalUnion, ::RationalUnion)
```

### Close Vectors
```@docs
close_vectors(L::ZZLat, v::Vector, arg...; kw...)
```
---
