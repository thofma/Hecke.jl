```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# [Introduction](@id Associative Algebras)

!!! warning
    The functions described in this section are currently experimental. While the overall
    functionality provided will stay the same, names of specific functions or
    conventions for the values returned by these functions might change in future versions.

Hecke provides functionality for finite-dimensional associatve algebras in the form of the abstract type `AbstractAssociativeAlgebra`.
The `AbstractAssociativeAlgebra` type is an extension (sub-type) of the abstract type `NCRing` provided by the [AbstractAlgebra.jl](https://nemocas.github.io/AbstractAlgebra.jl/stable/) package, and makes use of the [ring interface](https://nemocas.github.io/AbstractAlgebra.jl/stable/ring_interface/) documented there.

Currently, a large number of object constructors, and their methods, provide support for working with finite associative $R$-algebras for most commutative rings $R$.
However, there are functions in this library that make sense only in the restricted setting of finite associative $R$-algebras where $R$ is either a field or a finite-dimensional algebra over a field.
The primary goal of this library is to provide functionality only for this latter class of objects and any capability provided beyond that is considered a side-effect.

Hecke currently provides constructors that allow for the creation of the following objects:
- *structure constant algebras* (i.e. $R$-algebras whose underlying $R$-module is finite and free together with an explicit multiplication table),
- *matrix algebras* (i.e. $R$-algebras of the form $M_n(S)$ for an $R$-algebra $S$),
- *group algebras* (i.e. $R$-algebras of the form $R[G]$ for a finite group $G$),
- *quaternion algebras* (over a field and in arbitrary characteristic).


