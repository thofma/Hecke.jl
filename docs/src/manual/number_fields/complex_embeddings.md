```@meta
CurrentModule = Hecke
DocTestSetup = quote
    using Hecke
  end
```

# Complex embedding

We describe functionality for complex embeddings of arbitrary number fields.
Note that a *complex embedding* of a number field $L$ is a morphism $\iota \colon L \to \mathbf{C}$.
Such an embedding is called *real* if $\operatorname{im}(\iota) \subseteq \mathbf{R}$ and *imaginary* otherwise.

## Construction of complex embeddings

```@docs
complex_embeddings(::NumField)
real_embeddings(::NumField)
```

## Properties

```@docs
number_field(::NumFieldEmb)
is_real(::NumFieldEmb)
is_imaginary(::NumFieldEmb)
```

## Conjugated embedding

```@docs
conj(::NumFieldEmb)
```

## Evaluating elements at complex embeddings

Given an embedding $f \colon K \to \mathbf{C}$ and an element $x$ of $K$,
the image $f(x)$ of $x$ under $f$ can be constructed as follows.

```julia
    (f::NumFieldEmb)(x::NumFieldElem, prec::Int = 32) -> AcbFieldElem
```

  - Note that the return type will be a complex ball of type `AcbFieldElem`. The radius `r` of the ball is guaranteed to satisfy `r < 2^(-prec)`.
  - If the embedding is real, then the value `c` will satisfy `is_real(c) == true`.

For convenience, we also provide the following function to quickly create a corresponding
anonymous function:

```@docs
evaluation_function(e::NumFieldEmb, prec::Int)
```

## Logarithmic embedding

Given an object `e` representing an embedding $\iota \colon L \to \mathbf{C}$, the corresponding logarithmic embedding $L \to \mathbf{R}, \ x \mapsto \log(\lvert \iota(x) \rvert)$ can be constructed as `log(abs(e))`.

```jldoctest
julia> K, a = quadratic_field(2);

julia> e = complex_embedding(K, 1.41)
Complex embedding corresponding to 1.41
  of real quadratic field defined by x^2 - 2

julia> log(abs(e))(a, 128)
[0.346573590279972654708616060729088284037750067180127627 +/- 4.62e-55]

julia> log(abs(e(a)))
[0.346573590 +/- 2.99e-10]
```

## Restriction

Given a subfield $\iota \colon k \to K$, any embedding
$f \colon K \to \mathbf{C}$ naturally restricts to a complex embedding of $K$. Computing this restriction is supported in case $k$ appears
as a base field of (a base field) of $K$ or $\iota$ is provided:

```@docs
restrict(::NumFieldEmb, ::NumField)
restrict(::NumFieldEmb, ::NumFieldHom)
```

## Extension

Given a complex embedding $f \colon k \to \mathbf{C}$ and a morphism $\iota \colon k \to K$, an embedding $g \colon K \to \mathbf{C}$ is extension of $f$, if $g$ restricts to $f$. Given an embedding and a morphism,
all extensions can be computed as follows:

```@docs
extend(::NumFieldEmb, ::NumFieldHom)
```

## [Positivity & Signs](@id positivity_and_signs2)

```@docs
sign(::NumFieldElem, ::NumFieldEmb)
signs(::NumFieldElem, ::Vector{NumFieldEmb})
is_positive(::NumFieldElem, ::NumFieldEmb)
is_positive(::NumFieldElem, ::Vector{NumFieldEmb})
is_totally_positive(::NumFieldElem)
is_negative(::NumFieldElem, ::NumFieldEmb)
is_negative(::NumFieldElem, ::Vector{NumFieldEmb})
```

## Example

As mentioned, this functionality works for all types of number fields.
Here is an example of an absolute non-simple number field.

```jldoctest
julia> Qx, x = QQ["x"];

julia> K, a = number_field([x^2 + 1, x^3 + 2], "a");

julia> emb = complex_embeddings(K)
6-element Vector{AbsNonSimpleNumFieldEmbedding}:
 Complex embedding corresponding to [1.00 * i, -1.26] of non-simple number field
 Complex embedding corresponding to [1.00 * i, 0.63 + 1.09 * i] of non-simple number field
 Complex embedding corresponding to [-1.00 * i, 0.63 + 1.09 * i] of non-simple number field
 Complex embedding corresponding to [-1.00 * i, -1.26] of non-simple number field
 Complex embedding corresponding to [-1.00 * i, 0.63 - 1.09 * i] of non-simple number field
 Complex embedding corresponding to [1.00 * i, 0.63 - 1.09 * i] of non-simple number field

julia> k, b = quadratic_field(-1);

julia> i = hom(k, K, a[1]);

julia> restrict(emb[1], i)
Complex embedding corresponding to 1.00 * i
  of imaginary quadratic field defined by x^2 + 1

julia> restrict(emb[3], i)
Complex embedding corresponding to -1.00 * i
  of imaginary quadratic field defined by x^2 + 1
```
