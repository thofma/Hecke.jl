# Factored Elements

```@meta
CurrentModule = Hecke
```

In many applications in number theory related to the multiplicative
structure of number fields, interesting elements, e.g. units,
are extremely large when written wrt. to a fxied basis for the field:
for the fundamental unit in $Q[\sqrt d]$ it is known that the coefficients
wrt. the canonical basis $1, \sqrt d$ can have $O(\exp \sqrt d)$ many digits.
All currently known, fast methods construct those elements as power
products of smaller elements, allowing the computer to handle them.

Mathematically, one can think of factored elements to formally
live in the ring $Z[K]$ the group ring of the non-zero field
elements. Thus elements are of the form $ \prod a_i^{e_i}$ where
$a_i$ are elements in $K$, typically _small_ and the $e_i\in Z$ are frequently
large exponents. We refer to the $a_i$ as the *base* and the $e_i$ as the
*exponents* of the factored element.

Since $K$ is, in general, no PID, this presentation
is non-unique, elements in this form can easily be multiplied, raised
to large powers, but in general not compared and not added.

In Hecke, this is caputured more generally by the type `FacElem`,
parametrized by the type of the elements in the base and the type of their
parent.

Important special cases are
 * ```FacElem{fmpz, FlintIntegerRing}```, factored integers
 * ```FacElem{nf_elem, AnticNumberField}```, factored algerbaic numbers
 * ```FacElem{NfAbsOrdIdl, NfAbsOrdIdlSet}```, factored ideals

It should be noted that an object of type ```FacElem{fmpz, FlintIntegerRing}``
will, in general, not represent an integer as the exponents can be
negative.

## Construction
In general one can define factored elements by giving 2 arrays, the
base and the exponent, or a dictionary containing the pairs:

```@docs
FacElem
FacElem(a::nf_elem)
```

```@docs
ideal(::NfOrd, ::FacElem{nf_elem, AnticNumberField})
```


## Conversion
The process of computing the value defined by a factored element is
available as ```evaluate```. Depending on the types involved this
can be very efficient.

```@docs
evaluate(::FacElem{fmpz, S}) where S
evaluate(::FacElem{fmpq, S} where S)
evaluate(::FacElem{T,S} where S) where T
evaluate_naive(::FacElem{T,S} where S) where T
```

## Special functions

In the case where the parent of the base allows for efficient gcd computation,
power products can be made unique:

```@docs
simplify(x::FacElem{NfOrdIdl, NfOrdIdlSet})
simplify(x::FacElem{fmpq,S} where S)
```

The simplified version can then be used further:

```@docs
isone(x::FacElem{fmpq, S} where S)
factor_coprime(::FacElem{fmpz, S} where S)
factor_coprime(::FacElem{NfOrdIdl, NfOrdIdlSet})
factor_coprime(::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
factor_coprime(::FacElem{nf_elem, AnticNumberField}, ::NfOrdIdlSet)
factor(::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
factor(::FacElem{nf_elem, AnticNumberField}, ::NfOrdIdlSet)
```

For factorised algebraic numbers a unique simplification is not possible,
however, this allows still do obtain partial results:

```@docs
compact_presentation(a::FacElem{nf_elem, AnticNumberField}, n::Int = 2)
```

```@docs
signs(::Union{FacElem{nf_elem,AnticNumberField}, nf_elem})
signs(::Union{FacElem{nf_elem,AnticNumberField}, nf_elem}, ::Vector{InfPlc})
sign(::Union{FacElem{nf_elem,AnticNumberField}, nf_elem}, ::InfPlc)
is_positive(::Union{FacElem{nf_elem,AnticNumberField}, nf_elem}, ::InfPlc)
is_positive(::Union{FacElem{nf_elem,AnticNumberField}, nf_elem}, ::Vector{InfPlc})
is_totally_positive(::Union{FacElem{nf_elem,AnticNumberField}, nf_elem})
```

```@docs
valuation(::FacElem{nf_elem,AnticNumberField}, ::NfAbsOrdIdl{AnticNumberField,nf_elem})
valuation(::FacElem{NfAbsOrdIdl{AnticNumberField,nf_elem},Hecke.NfAbsOrdIdlSet{AnticNumberField,nf_elem}}, ::NfAbsOrdIdl{AnticNumberField,nf_elem})
evaluate_mod(::FacElem{nf_elem,AnticNumberField}, ::NfOrdFracIdl)
reduce_ideal(::FacElem{NfAbsOrdIdl{AnticNumberField,nf_elem},Hecke.NfAbsOrdIdlSet{AnticNumberField,nf_elem}})
modular_proj(::FacElem{nf_elem,AnticNumberField}, ::Hecke.modular_env)
```

## Miscellaneous

```@docs
max_exp(a::FacElem)
min_exp(a::FacElem)
maxabs_exp(a::FacElem)
```

