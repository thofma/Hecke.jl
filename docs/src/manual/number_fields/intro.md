```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# [Introduction](@id NumberFieldsLink)

By definition, a number field is a finite extension of the rationals $\mathbf{Q}$.

In Hecke, a number field $L$ is recursively defined as being either the field of rational numbers $\mathbf{Q}$ or
a finite extension of a number field $K$.

We support two presentations for an extension $L/K$:
 - as a quotient $L = K[x]/(f)$, where $f \in K[x]$ is an irreducible polynomial (i.e. a *simple extension*), or
 - as a quotient $L = K[x_1,\dotsc,x_n]/(f_1(x_1),\dotsc,f_n(x_n))$, where $f_1,\dotsc,f_n \in K[x_1, \dotsc, x_n]$ are appropriate choices of univariate polynomials making $L$ a field (i.e. a *non-simple extension*).

In both cases we refer to $K$ as the *base field* of the number field $L$.

!!! info
    By the Primitive Element Theorem, any finite separable extension $L/K$ can be written as a simple extension $L=K(\alpha)$ for some $\alpha\in L$.
    The distinction between simple and non-simple extensions is therefore purely computational: it dictates how data is stored and how functions are implemented.

## Absolute and Relative Extensions

A useful dichotomy comes from the origin of the base field in the definition of a number field $L/K$.
We call $L$ an *absolute* number field if the base field is equal to the rational numbers $\mathbf{Q}$.
We call $L$ a *relative* number field if the base field is strictly larger than $\mathbf{Q}$.

There are (at least) four concrete types that can be used in the implementation of a number field:
 - `AbsSimpleNumField` for absolute simple number fields $\mathbf{Q}(\alpha)/\mathbf{Q}$,
 - `AbsNonSimpleNumField` for absolute non-simple number fields $\mathbf{Q}(\alpha_1,...,\alpha_n)/\mathbf{Q}$,
 - `RelSimpleNumField` for simple relative extensions $K(\alpha)/K$,
 - `RelNonSimpleNumField` for non-simple relative extensions $K(\alpha_1,...,\alpha_n)/K$.

!!! tip "Example"
    We can construct an absolute simple quadratic field $K/\mathbb{Q}$ and a non-simple relative extension $L/K$.

    ```julia
    julia> K, a = quadratic_field(5)
    (Real quadratic field defined by x^2 - 5, sqrt(5))

    julia> Kx, x = K["x"]
    (Univariate polynomial ring in x over K, x)

    julia> L, b = number_field([x^2-2, x^2-3], "b")
    (Relative non-simple number field of degree 4 over K, RelNonSimpleNumFieldElem{AbsSimpleNumFieldElem}[b1, b2])

    julia> typeof(K)
    AbsSimpleNumField

    julia> typeof(L)
    RelNonSimpleNumField{AbsSimpleNumFieldElem}
    ```

Both the absolute and relative simple number field types are concrete subtypes of the abstract type `SimpleNumField{T}` parametrized by the element type `T` of the associated base field.
Both absolute and relative non-simple number field types are subtypes of the abstract type `NonSimpleNumField{T}` parametrized similarly.
These types are themselves subtypes of the abstract parametrized type `NumField{T}`.

Thus a (simplified) graph of the type tree for number fields is:

```text
NumField{QQFieldElem}                   NumField{T}
├── NonSimpleNumField{QQFieldElem}      ├── NonSimpleNumField{T}
│   └── AbsNonSimpleNumField            │   └── RelNonSimpleNumField
└── SimpleNumField{QQFieldElem}         └── SimpleNumField{T}
    └── AbsSimpleNumField                   └── RelSimpleNumField
```

Elements of fields implemented by one of these concrete types have a similar type but with an `Elem` suffix (e.g. an element of an absolute simple number field of type `AbsSimpleNumField` has type `AbsSimpleNumFieldElem`).
