# Degree localization of a rational function field

```@meta
CurrentModule = Hecke
DocTestSetup = quote
  using Hecke
end
```

## Degree localization

Given $k(x)$ a (univariate) rational function field, there are two rings of interest,
both of which are Euclidean:

* $k[x]$
* $k_\infty(x) = \{a/b | a, b \in k[x] \;\;\mbox{where}\;\; \deg(a) \leq \deg(b)\}$

The second of these rings is the localization of $k[1/x]$ at $(1/x)$ inside the rational
function field $k(x)$, i.e. the localization of the function field at the point at
infinity, i.e. the valuation ring for valuation $-$degree$(x)$.

We refer to this ring as the *degree localization* of the rational function field $k(x)$.

### Construction of the degree localization

The degree localization of a rational function field $k(x)$ can be constructed using
a `localization` constructor, passing in the `degree` function as argument.

```@docs
localization(K::Generic.RationalFunctionField{T}, ::typeof(degree)) where T <: FieldElement
```

---

#### Example +

```@repl
using Hecke # hide
K, x = rational_function_field(FlintQQ, "x");
R = localization(K, degree)
```

### Elements of the degree localization

Elements of the degree localization are created using the parent object $R$ representing
the degree localization

---

#### Example +

```@repl
using Hecke # hide
K, x = rational_function_field(FlintQQ, "x");
R = localization(K, degree)

a = R()
b = R(1)
c = R((x + 1)//x)
```

Note that the degree of the denominator of the function field element passed to the
constructor must be at least that of the numerator or an exception is raised.

### Element functionality

```@docs
degree(a::KInftyElem)
valuation(a::KInftyElem)
```

One can test whether a given element of a rational function field is in the degree
localization.

```@docs
in(a::Generic.RationalFunctionFieldElem{T}, R::KInftyRing{T}) where T <: FieldElement
```

All basic arithmetic operations are provided for elements of the degree localization.

As the degree localization is a Euclidean ring, all standard Euclidean functions, including
`div`, `divrem`, `mod`, `gcd`, `gcdx`, are provided.

