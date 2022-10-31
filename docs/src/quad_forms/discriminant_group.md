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

```@docs
torsion_quadratic_module(M::ZLat, N::ZLat)
```

### The underlying Type
```@docs
TorQuadMod
```

Most of the functionality mirrors that of `AbGrp` its elements and homomorphisms.
Here we display the part that is specific to elements of torsion quadratic modules.
### Attributes

```@docs
abelian_group(T::TorQuadMod)
cover(T::TorQuadMod)
relations(T::TorQuadMod)
value_module(T::TorQuadMod)
value_module_quadratic_form(T::TorQuadMod)
gram_matrix_bilinear(T::TorQuadMod)
gram_matrix_quadratic(T::TorQuadMod)
modulus_bilinear_form(T::TorQuadMod)
modulus_quadratic_form(T::TorQuadMod)
```

### Elements

```@docs
quadratic_product(a::TorQuadModElem)
inner_product(a::TorQuadModElem, b::TorQuadModElem)
```

### Lift to the cover
```@docs
lift(a::TorQuadModElem)
representative(::TorQuadModElem)
```

### Orthogonal submodules
```@docs
orthogonal_submodule(T::TorQuadMod, S::TorQuadMod)
```

### Isometry
```@docs
is_isometric_with_isometry(T::TorQuadMod, U::TorQuadMod)
is_anti_isometric_with_anti_isometry(T::TorQuadMod, U::TorQuadMod)
```

### Primary and elementary modules
```docs
is_primary_with_prime(T::TorQuadMod)
is_primary(T::TorQuadMod, p::Union{Integer, fmpz})
is_elementary_with_prime(T::TorQuadMod)
is_elementary(T::TorQuadMod, p::Union{Integer, fmpz})
```

## Discriminant Groups
See [Nikulin79](@cite) for the general theory of discriminant groups.
They are particularly useful to work with primitive embeddings of
integral integer quadratic lattices.

### From a lattice

```@docs
discriminant_group(::ZLat)
```

### From a Matrix

```@docs
torsion_quadratic_module(q::fmpq_mat)
```
### Rescaling the form
```@docs
rescale(T::TorQuadMod, k::RingElement)
```

### Invariants

```@docs
is_degenerate(T::TorQuadMod)
is_semi_regular(T::TorQuadMod)
radical_bilinear(T::TorQuadMod)
radical_quadratic(T::TorQuadMod)

normal_form(T::TorQuadMod; partial=false)
```

### Genus
```@docs
genus(T::TorQuadMod, signature_pair::Tuple{Int, Int})
brown_invariant(T::TorQuadMod)
is_genus(T::TorQuadMod, signature_pair::Tuple{Int, Int})
```
