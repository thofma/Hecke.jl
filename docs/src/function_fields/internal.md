```@meta
CurrentModule = Hecke
```
Function fields, in Hecke, come in several
different types:
 - `RationalFunctionField`: a field of the form $k(x)$ for a field $k$.
 - `FunctionField`: a finite extension of a rational function field given by
    a polynomial.

Function fields with the type `FunctionField` are referred to as simple
fields in the rest of this document. They are also referred to as being
absolute.

## Absolute Simple Fields

Internally function fields of type `FunctionField` are essentially
represented as a unvariate quotient with the arithmetic provided by the
AbstractAlgebra and Nemo packages. As they are defined generically for all
AbstractAlgebra, Nemo and Hecke fields $k$ the function field type is
implemented in AbstractAlgebra.

