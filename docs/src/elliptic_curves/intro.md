# Introduction

```@meta
CurrentModule = Hecke
DocTestSetup = quote
    using Hecke
end

```

This chapter deals with functionality for elliptic curves, which is available over arbitrary fields, with
specific features available for curvers over the rationals and number fields, and finite fields.

An elliptic curve $E$ is the projective closure of the curve given by the *Weierstrass equation*
```math
y^2 + a_1 x y + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6
```
specified by the list of coefficients `[a1, a2, a3, a4, a6]`. If $a_1 = a_2 = a_3 = 0$, this simplifies
to
```math
y^2 = x^3 + a_4 x + a_6
```
which we refer to as a *short Weierstrass equation* and which is specified by the two element list `[a4, a6]`.
