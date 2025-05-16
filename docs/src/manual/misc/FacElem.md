```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# Factored Elements

In many applications in number theory related to the multiplicative
structure of number fields, interesting elements, e.g. units,
are extremely large when written with respect to a fixed basis for the field:
for the fundamental unit in $Q[\sqrt d]$ it is known that the coefficients
with respect to the canonical basis $1, \sqrt d$ can have $O(\exp \sqrt d)$ many digits.
All currently known, fast methods construct those elements as power
products of smaller elements, allowing the computer to handle them.

Mathematically, one can think of factored elements to formally
live in the ring $\mathbb{Z}[K^*]$ the group ring of the non-zero field
elements. Thus elements are of the form $\prod a_i^{e_i}$ where
$a_i$ are elements in $K$, typically _small_ and the $e_i\in \mathbb{Z}$ are frequently
large exponents. We refer to the $a_i$ as the *base* and the $e_i$ as the
*exponents* of the factored element.

Presentations of elements of $K^*$ are
non-unique; elements in this form can easily be multiplied, raised
to large powers, but in general not compared and not added.

In Hecke, this is captured more generally by the type `FacElem`,
parametrized by the type of the elements in the base and the type of their
parent.

Important special cases are
 * ```FacElem{ZZRingElem, ZZRing}```, factored integers
 * ```FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}```, factored algebraic numbers
 * ```FacElem{AbsNumFieldOrderIdeal, AbsNumFieldOrderIdealSet}```, factored ideals

It should be noted that an object of type `FacElem{ZZRingElem, ZZRing}`
will, in general, not represent an integer as the exponents can be
negative.

## Construction
In general one can define factored elements by giving 2 arrays, the
base and the exponent, or a dictionary containing the pairs:

```@docs
FacElem
FacElem(a::AbsSimpleNumFieldElem)
```

```@docs
ideal(::AbsSimpleNumFieldOrder, ::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField})
```


## Conversion
The process of computing the value defined by a factored element is
available as ```evaluate```. Depending on the types involved this
can be very efficient.

```@docs
evaluate(::FacElem{ZZRingElem, S}) where S
evaluate(::FacElem{QQFieldElem, S} where S)
evaluate(::FacElem{T,S} where S) where T
evaluate_naive(::FacElem{T,S} where S) where T
```

## Special functions

In the case where the parent of the base allows for efficient gcd computation,
power products can be made unique:

```@docs
simplify(x::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
simplify(x::FacElem{QQFieldElem,S} where S)
```

The simplified version can then be used further:

```@docs
isone(x::FacElem{QQFieldElem, S} where S)
factor_coprime(::FacElem{ZZRingElem, S} where S)
factor_coprime(::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
factor_coprime(::FacElem{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
factor_coprime(::AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField})
factor(::FacElem{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
factor(::AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField})
```

For factorised algebraic numbers a unique simplification is not possible,
however, this allows still do obtain partial results:

```@docs
compact_presentation(a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, n::Int = 2)
```

```@docs
valuation(::FacElem{AbsSimpleNumFieldElem,AbsSimpleNumField}, ::AbsNumFieldOrderIdeal{AbsSimpleNumField,AbsSimpleNumFieldElem})
valuation(::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField,AbsSimpleNumFieldElem},Hecke.AbsNumFieldOrderIdealSet{AbsSimpleNumField,AbsSimpleNumFieldElem}}, ::AbsNumFieldOrderIdeal{AbsSimpleNumField,AbsSimpleNumFieldElem})
evaluate_mod(::FacElem{AbsSimpleNumFieldElem,AbsSimpleNumField}, ::AbsSimpleNumFieldOrderFractionalIdeal)
reduce_ideal(::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField,AbsSimpleNumFieldElem},Hecke.AbsNumFieldOrderIdealSet{AbsSimpleNumField,AbsSimpleNumFieldElem}})
modular_proj(::FacElem{AbsSimpleNumFieldElem,AbsSimpleNumField}, ::Hecke.modular_env)
```

## Positivity & Signs

Factored elements can be used instead of number field elements for the functions
`sign`, `signs`, `is_positive`, `is_negative` and `is_totally_positive`, see
[Positivity & Signs](@ref positivity_and_signs2)

## Miscellaneous

```@docs
max_exp(a::FacElem)
min_exp(a::FacElem)
maxabs_exp(a::FacElem)
```

