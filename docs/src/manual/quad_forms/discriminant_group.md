```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# Discriminant Groups

## Torsion Quadratic Modules
A torsion quadratic module is the quotient
$M/N$ of two quadratic integer lattices $N \subseteq M$ in the quadratic
space $(V,\Phi)$.
It inherits a bilinear form

$$b: M/N \times M/N \to \mathbb{Q} / n \mathbb{Z}$$

as well as a quadratic form

$$q: M/N \to \mathbb{Q} / m \mathbb{Z}.$$

where $n \mathbb{Z} = \Phi(M,N)$ and
$m \mathbb{Z} = 2n\mathbb{Z} + \sum_{x \in N} \mathbb{Z} \Phi (x,x)$.

```@docs
torsion_quadratic_module(M::ZZLat, N::ZZLat)
```

### The underlying Type
```@docs
TorQuadModule
```

Most of the functionality mirrors that of `AbGrp` its elements and homomorphisms.
Here we display the part that is specific to elements of torsion quadratic modules.

### Attributes

```@docs
abelian_group(T::TorQuadModule)
cover(T::TorQuadModule)
relations(T::TorQuadModule)
value_module(T::TorQuadModule)
value_module_quadratic_form(T::TorQuadModule)
gram_matrix_bilinear(T::TorQuadModule)
gram_matrix_quadratic(T::TorQuadModule)
modulus_bilinear_form(T::TorQuadModule)
modulus_quadratic_form(T::TorQuadModule)
```

### Elements

```@docs
quadratic_product(a::TorQuadModuleElem)
inner_product(a::TorQuadModuleElem, b::TorQuadModuleElem)
```

### Lift to the cover
```@docs
lift(a::TorQuadModuleElem)
representative(::TorQuadModuleElem)
```

### Orthogonal submodules
```@docs
orthogonal_submodule(T::TorQuadModule, S::TorQuadModule)
```

### Isometry
```@docs
is_isometric_with_isometry(T::TorQuadModule, U::TorQuadModule)
is_anti_isometric_with_anti_isometry(T::TorQuadModule, U::TorQuadModule)
```

### Primary and elementary modules
```@docs
is_primary_with_prime(T::TorQuadModule)
is_primary(T::TorQuadModule, p::Union{Integer, ZZRingElem})
is_elementary_with_prime(T::TorQuadModule)
is_elementary(T::TorQuadModule, p::Union{Integer, ZZRingElem})
```

### Smith normal form
```@docs
snf(T::TorQuadModule)
is_snf(T::TorQuadModule)
```

## Discriminant Groups
See [Nik79](@cite) for the general theory of discriminant groups.
They are particularly useful to work with primitive embeddings of
integral integer quadratic lattices.

### From a lattice

```@docs
discriminant_group(::ZZLat)
```

### From a matrix

```@docs
torsion_quadratic_module(q::QQMatrix)
```

### Rescaling the form
```@docs
rescale(T::TorQuadModule, k::RingElement)
```

### Invariants

```@docs
is_degenerate(T::TorQuadModule)
is_semi_regular(T::TorQuadModule)
radical_bilinear(T::TorQuadModule)
radical_quadratic(T::TorQuadModule)
normal_form(T::TorQuadModule; partial=false)
```

### Genus
```@docs
genus(T::TorQuadModule, signature_pair::Tuple{Int, Int})
brown_invariant(T::TorQuadModule)
is_genus(T::TorQuadModule, signature_pair::Tuple{Int, Int})
```

### Categorical constructions
```@docs
direct_sum(x::Vector{TorQuadModule})
direct_product(x::Vector{TorQuadModule})
biproduct(x::Vector{TorQuadModule})
```

### Submodules
```@docs
submodules(::TorQuadModule)
stable_submodules(::TorQuadModule, ::Vector{TorQuadModuleMap})
```
