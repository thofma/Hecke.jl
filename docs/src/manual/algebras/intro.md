```@meta
CurrentModule = Hecke
```

# [Introduction](@id Algebras)

!!! note
    The functions described in this section are experimental. While the overall
    functionality provided will stay the same, names of specific functions or
    conventions for the return values might change in future versions.

This section describes the functionality for finite-dimensional associative
algebras (or just *algebras* for short). Since different applications have different requirements, 
the following types of algebras are implemented:
- structure constant algebras,
- matrix algebras,
- group algebras,
- quaternion algebras.

These share a common interface encompassing a wide range of functions, which is
indicated by the use of the type `AbstractAssociativeAlgebra` in the signature.
