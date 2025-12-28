```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# [Introduction](@id NumberFieldsLink)

By definition, a number field is a finite extension of the rationals $\mathbf{Q}$.

In Hecke, a number field $L$ is recursively defined as being either the field of rational numbers $\mathbf{Q}$ or
a finite extension of a number field $K$.

Extensions $L/K$ can be defined in one of the following two ways:
 - as a quotient $L = K[x]/(f)$, where $f \in K[x]$ is an irreducible polynomial (i.e. a *simple extension*), or
 - as a quotient $L = K[x_1,\dotsc,x_n]/(f_1(x_1),\dotsc,f_n(x_n))$, where $f_1,\dotsc,f_n \in K[x_1, \dotsc, x_n]$ are appropriate choices of univariate polynomials making $L$ a field (i.e. a *non-simple extension*).

In both cases we refer to $K$ as the *base field* of the number field $L$.

## Absolute and Relative Extensions

A useful dichotomy comes from the origin of the base field in the definition of a number field $L/K$.
We call $L$ an *absolute* number field if the base field is equal to the rational numbers $\mathbf{Q}$.
We call $L$ a *relative* number field if the base field is strictly larger than $\mathbf{Q}$.

There are four concrete types that can be used in the implementation of a number field:
 - `AbsSimpleNumField` for absolute simple number fields $\mathbf{Q}(\alpha)/\mathbf{Q}$,
 - `AbsNonSimpleNumField` for absolute non-simple number fields $\mathbf{Q}(\alpha_1,...,\alpha_n)/\mathbf{Q}$,
 - `RelSimpleNumField` for simple relative extensions $K(\alpha)/K$,
 - `RelNonSimpleNumField` for non-simple relative extensions $K(\alpha_1,...,\alpha_n)/K$.

Both the absolute and relative simple number field types are concrete subtypes of the abstract type `SimpleNumField{T}` parametrized by the element type of `T` of the corresponding base field.
Both absolute and relative non-simple number field types are subtypes of the abstract type `NonSimpleNumField{T}` parametrized similarly.
Both of these coarse types are subtypes of the abstract parametrized type `NumField{T}`.

```text
NumField{QQFieldElem}                   NumField{T}
├── NonSimpleNumField{QQFieldElem}      ├── NonSimpleNumField{T}
│   └── AbsNonSimpleNumField            │   └── RelNonSimpleNumField
└── SimpleNumField{QQFieldElem}         └── SimpleNumField{T}
    └── AbsSimpleNumField                   └── RelSimpleNumField
```

Elements of fields implemented by a given concrete type have the type with an `Elem` suffix (e.g. an element of an absolute simple number field of type `AbsSimpleNumField` has type `AbsSimpleNumFieldElem`).
