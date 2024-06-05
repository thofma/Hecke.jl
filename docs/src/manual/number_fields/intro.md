```@meta
CurrentModule = Hecke
```

# [Introduction](@id NumberFieldsLink2)

By definition, mathematically a number field is just a finite extension of the rational $\mathbf{Q}$.
In Hecke, a number field $L$ is recursively defined as being the field of rational numbers $\mathbf{Q}$ or
a finite extension of a number field $K$. In the second case, the extension
can be defined in the one of the following two ways:
 - We have $L = K[x]/(f)$, where $f \in K[x]$ is an irreducible polynomial (*simple extension*), or
 - We have $L = K[x_1,\dotsc,x_n]/(f_1(x_1),\dotsc,f_n(x_n))$, where $f_1,\dotsc,f_n \in K[x]$
   are univariate polynomials (*non-simple extension*).
In both cases we refer to $K$ as the *base field* of the number field $L$.
Another useful dichotomy comes from the type of the base field.
We call $L$ an *absolute* number field, if the base field is equal to the rational numbers $\mathbf{Q}$.
