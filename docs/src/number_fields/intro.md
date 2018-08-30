# Number Fields

```@meta
CurrentModule = Hecke
```

## Introduction

This chapter deals with number fields. Number fields, in Hecke, come in several
different types:
 - `AnticNumberField`: a finite simple extension of the rational numbers $Q$
 - `NfAbsNS`: a finite extension of $Q$ given by several polynomials.
 We will refer to this as a non-simple field - even though mathematically
 we can find a primitive elements.
 - `NfRel`: a finite simple extension of a number field. This is 
    actually parametried by the (element) type of the coefficient field.
    The complete type of an extension of an absolute field (`AnticNumberField`)
    is `NfRel{nf_elem}`. The next extension thus will be
    `NfRel{NfRelElem{nf_elem}}`.
 - `NfRel_ns`: extensions of number fields given by several polynomials.
    This too will be refered to as a non-simple field.

The simple types `AnticNumberField` and `NfRel` are also calle simple
fields in the rest of this document, `NfRel` and `NfRel_ns` are referred
to as relative extensions while `AnticNumberField` and `NfAbsNS` are
called absolute.

Internally, simple fields are essentially just (univariate) polynomial
quotients in a dense representation, while non-simple fields are
multivariate quotient rings, thus have a sparse presentation.
In general, simple fields allow much faster arithmetic, while 
the non-simple fields give easy access to large degree fields.


## Absolute Simple Fields

The most basic number field type is that of `AnticNumberField`. Internally
this is essentially represented as a unvariate quotient with the
arithmetic provided by the antic-c-library and implemented in Nemo.

### Creation
Number fields are mostly created using `NumberField`, but also using
`number_field`.

Many of the constructors have arguments of type `Symbol` or `AbstractString`,
if used, they define the appearance in printing, and printing only.
The named parameter `check` can be `true` or `false, the default being `true`.
This parameter controlls is the polynomial defining the number field is
tested for irreducibility or not. Given that this can be potentially 
very time consuiming if the degree if large, one can omit this test. Note
however, that the behaviour of Hecke is undefined if a reducible polynomial
is used to define a "field".

The named boolean parameter `cached` is inherited from the underlying Nemo
system. Two number fields defined using the same polynomial from the
identical polynomial ring and the same (identical) symbol/ string
will be identical if `cached == true` and different if `cached == false`.

```@docs
NumberField(f::fmpq_poly)
cyclotomic_field(n::Int)
#CyclotomicField(n::Int, s::AbstractString, t; cached)
#CyclotomicField(n::Int, s::AbstractString, t)
#CyclotomicField(n::Int, s::AbstractString)
#MaximalRealSubfield(n::Int, s::AbstractString)
#MaximalRealSubfield(n::Int, s::AbstractString, t)
wildanger_field(n::Int, B::fmpz)
pure_extension(n::Int, gen::Integer)
```


### Example

```@repl
using Hecke # hide
Qx, x = PolynomialRing(FlintQQ, "x");
K, a = NumberField(x^2 - 10, "a");
```

## Absolute Non-Simple Fields
### Creation
```@docs
NumberField(f::Array{fmpq_poly, 1}, s::String="_\$")
```

### Example

```@repl
using Hecke # hide
Qx, x = PolynomialRing(FlintQQ, "x");
K, g = number_field([x^2-2, x^2-3, x^2-5])
g[1]^2
minpoly(g[1] + g[2])
```

### Conversion
```@docs
simple_extension(K::NfAbsNS)
```

## Simple Relative Fields
### Creation
```@docs
NumberField(f::Generic.Poly)
NumberField(f::Generic.Poly, s::String)
```

### Conversion
```@docs
absolute_field(K::NfRel{nf_elem})
absolute_field(K::NfRel{NfRelElem})
```

## Non-Simple Relative Fields
### Creation
```@docs
NumberField(f::Array{Generic.Poly{T}, 1}, s::String="_\$") where T
```

### Conversion
```@docs
simple_extension(K::NfRel_ns)
simple_extension(K::NfRel_ns{nf_elem}, ::FlintRationalField)
```

## Implicit Relative Extensions
Given two absolute fields $K$ and $k$ as well as an embedding $\phi:k \to K$
we can regard $K$ as an extension on $k$, hence invariante of $K$ can
be investigated relative to $k$ rathern than over $Q$.
Here we list functions achieving this without actually computing
$K$ as an extension of $k$.

```@docs
minimum(m::T, I::NfOrdIdl) where T<:(AbstractAlgebra.Map{Nemo.AnticNumberField,Nemo.AnticNumberField,S,T} where T where S)
norm(m::T, I::Hecke.NfAbsOrdIdl{Nemo.AnticNumberField,Nemo.nf_elem}) where T<:(AbstractAlgebra.Map{Nemo.AnticNumberField,Nemo.AnticNumberField,S,T} where T where S)
norm(m::T, a::nf_elem)  where T<:(AbstractAlgebra.Map{Nemo.AnticNumberField,Nemo.AnticNumberField,S,T} where T where S)
discriminant(m::Map, R::NfOrd)
```

```@docs
(I::NfAbsOrdIdlSet{Nemo.AnticNumberField,Nemo.nf_elem})(mp::Map, i::NfOrdIdl)
```

## Invariants

```@docs
degree(::AnticNumberField)
basis(::AnticNumberField)
discriminant(::AnticNumberField)
```

## Elements

### Creation

```@docs
(K::)(poly)
(K::)(Integer)
```

### Invariants

```@doc
norm(a)
norm(a, k)
norm(a, phi)
trace
minpoly
charpoly
repmat
coeffs
length
t2
conjugates
logs
denominator
numerator
isunit
```

