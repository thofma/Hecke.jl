# Discriminant Groups
```@meta
CurrentModule = Hecke
DocTestSetup = quote
    using Hecke
  end
```

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

```@docs; canonical=false
torsion_quadratic_module(M::ZZLat, N::ZZLat)
```

### The underlying Type
```@docs; canonical=false
TorQuadModule
```

Most of the functionality mirrors that of `AbGrp` its elements and homomorphisms.
Here we display the part that is specific to elements of torsion quadratic modules.

### Attributes

```@docs; canonical=false
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

```@docs; canonical=false
quadratic_product(a::TorQuadModuleElem)
inner_product(a::TorQuadModuleElem, b::TorQuadModuleElem)
```

### Lift to the cover
```@docs; canonical=false
lift(a::TorQuadModuleElem)
representative(::TorQuadModuleElem)
```

### Orthogonal submodules
```@docs; canonical=false
orthogonal_submodule(T::TorQuadModule, S::TorQuadModule)
```

### Isometry
```@docs; canonical=false
is_isometric_with_isometry(T::TorQuadModule, U::TorQuadModule)
is_anti_isometric_with_anti_isometry(T::TorQuadModule, U::TorQuadModule)
```

### Primary and elementary modules
```@docs; canonical=false
is_primary_with_prime(T::TorQuadModule)
is_primary(T::TorQuadModule, p::Union{Integer, ZZRingElem})
is_elementary_with_prime(T::TorQuadModule)
is_elementary(T::TorQuadModule, p::Union{Integer, ZZRingElem})
```

### Smith normal form
```@docs; canonical=false
snf(T::TorQuadModule)
is_snf(T::TorQuadModule)
```

## Discriminant Groups
See [Nik79](@cite) for the general theory of discriminant groups.
They are particularly useful to work with primitive embeddings of
integral integer quadratic lattices.

### From a lattice

```@docs; canonical=false
discriminant_group(::ZZLat)
```

### From a matrix

```@docs; canonical=false
torsion_quadratic_module(q::QQMatrix)
```

### Rescaling the form
```@docs; canonical=false
rescale(T::TorQuadModule, k::RingElement)
```

### Invariants

```@docs; canonical=false
is_degenerate(T::TorQuadModule)
is_semi_regular(T::TorQuadModule)
radical_bilinear(T::TorQuadModule)
radical_quadratic(T::TorQuadModule)
normal_form(T::TorQuadModule; partial=false)
```

### Genus
```@docs; canonical=false
genus(T::TorQuadModule, signature_pair::Tuple{Int, Int})
brown_invariant(T::TorQuadModule)
is_genus(T::TorQuadModule, signature_pair::Tuple{Int, Int})
```

### Categorical constructions
```@docs; canonical=false
direct_sum(x::Vector{TorQuadModule})
direct_product(x::Vector{TorQuadModule})
biproduct(x::Vector{TorQuadModule})
```

### Submodules
```@docs; canonical=false
submodules(::TorQuadModule)
stable_submodules(::TorQuadModule, ::Vector{TorQuadModuleMap})
```
