# Integer Lattices
```@meta
CurrentModule = Hecke
DocTestSetup = quote
    using Hecke
  end
```
An integer lattice $L$ is a finitely generated $\mathbb{Z}$-submodule of a quadratic
vector space $V = \mathbb{Q}^n$ over the rational numbers.
Integer lattices are also known as quadratic forms over the integers.
We will refer to them as $\mathbb{Z}$-lattices.

A $\mathbb{Z}$-lattice $L$ has the type `ZLat`. It is given in terms of
its ambient quadratic space $V$ together with a basis matrix $B$ whose rows span $L$,
i.e. $L = \mathbb{Z}^r B$ where $r$ is the ($\mathbb{Z}$-module) rank of $L$.

To access $V$ and $B$ see [`ambient_space(L::ZLat)`](@ref) and [`basis_matrix(L::ZLat)`](@ref).


## Creation of integer lattices

### From a gram matrix

```@docs
Zlattice(B::fmpq_mat)
```

### In a quadratic space

```@docs
lattice(V::QuadSpace{FlintRationalField, fmpq_mat}, B::MatElem;)
```

### Special lattices

```@docs
root_lattice(::Symbol, ::Int)
hyperbolic_plane_lattice(n::Union{Int64, fmpz})
Zlattice(S::Symbol, n::Union{Int64, fmpz})
```

### From a genus
Integer lattices can be created as representatives of a genus.
See ([`representative(L::ZGenus)`](@ref))

### Rescaling the Quadratic Form

```@docs
rescale(::ZLat, ::Any)
```

## Attributes

```@docs
ambient_space(L::ZLat)
basis_matrix(L::ZLat)
gram_matrix(L::ZLat)
rational_span(L::ZLat)
base_ring(::ZLat)
base_field(::ZLat)
```

## Invariants
```@docs
rank(L::ZLat)
det(L::ZLat)

scale(L::ZLat)
norm(L::ZLat)
iseven(L::ZLat)
is_integral(L::ZLat)

is_primary_with_prime(L::ZLat)
is_primary(L::ZLat, p::Union{Integer, fmpz})
is_elementary_with_prime(L::ZLat)
is_elementary(L::ZLat, p::Union{Integer, fmpz})
```

### The Genus

For an integral lattice
The genus of an integer lattice collects its local invariants.
[`genus(::ZLat)`](@ref)
```@docs
mass(L::ZLat)
genus_representatives(L::ZLat)
```

### Real invariants
```@docs
signature_tuple(L::ZLat)
is_positive_definite(L::ZLat)
is_negative_definite(L::ZLat)
is_definite(L::ZLat)
```

## Isometries
```@docs
automorphism_group_generators(L::ZLat)
automorphism_group_order(L::ZLat)
is_isometric(L::ZLat, M::ZLat)
is_locally_isometric(L::ZLat, M::ZLat, p::Int)
```
# Root lattice recognition
```@docs
root_lattice_recognition(L::ZLat)
root_lattice_recognition_fundamental(L::ZLat)
ADE_type(G::MatrixElem)
```

## Module operations
Most module operations assume that the lattices live in the same ambient space.
For instance only lattices in the same ambient space compare.

```@docs
Base.:(==)(L1::ZLat, L2::ZLat)
is_sublattice(M::ZLat, N::ZLat)
is_sublattice_with_relations(M::ZLat, N::ZLat)
+(M::ZLat, N::ZLat)
Base.:(*)(a, L::ZLat)
intersect(M::ZLat, N::ZLat)
Base.in(v::Vector, L::ZLat)
Base.in(v::fmpq_mat, L::ZLat)
primitive_closure(M::ZLat, N::ZLat)
is_primitive(M::ZLat, N::ZLat)
```

## Embeddings

### Orthogonal sublattices
```@docs
orthogonal_sum(::ZLat, ::ZLat)
orthogonal_submodule(::ZLat, ::ZLat)
```

### Dual lattice
```@docs
dual(L::ZLat)
```

### Discriminant group
See [`discriminant_group(L::ZLat)`](@ref).

### Overlattices
```@docs
glue_map(L::ZLat, S::ZLat, R::ZLat; check=true)
overlattice(glue_map::TorQuadModMor)
local_modification(M::ZLat, L::ZLat, p)
maximal_integral_lattice(L::ZLat)
```

### Sublattices defined by endomorphisms
```@docs
kernel_lattice(L::ZLat, f::MatElem; ambient_representation::Bool = true)
invariant_lattice(L::ZLat, G::Vector{<:MatElem};
                           ambient_representation::Bool = true)
```

## LLL, Short and Close Vectors

### LLL and indefinite LLL
```@docs
lll(L::ZLat; same_ambient::Bool = true)
```
### Short Vectors
```@docs
short_vectors
shortest_vectors
short_vectors_iterator
minimum(L::ZLat)
kissing_number(L::ZLat)
```

### Close Vectors
```@docs
close_vectors(L::ZLat, v::Vector, arg...; kw...)
```
---
