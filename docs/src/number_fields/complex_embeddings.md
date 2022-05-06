```@meta
CurrentModule = Hecke
DocTestSetup = quote
    using Hecke
  end
```

# Complex embedding

Functionality for working with complex embeddings of a number field $L$,
that is, with ring morphisms $L \to \mathbf{C}$ is provided for all possible
number field types.

## Construction of complex embeddings

```@docs
complex_embeddings(::NumField)
real_embeddings(::NumField)
```

## Properties

```@docs
number_field(::NumFieldEmb)
isreal(::NumFieldEmb)
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
    (f::NumFieldEmb)(x::NumFieldElem, prec::Int = 32) -> acb
```

  - Note that the return type will be a complex ball of type `acb`. The radius `r` of the ball is guarenteed to satisfy `r < 2^(-prec)`.
  - If the embedding is real, then the value `c` will satisfy `isreal(c) == true`.

For convenience, we also provide the following function to quickly create a corresponding
anonymous function:

```@docs
evaluation_function(e::NumFieldEmb, prec::Int)
```

## Restriction

Given a subfield $\iota \colon k \to K$, any embedding
$f \colon K \to \mathbf{C}$ naturally restricts to a complex embedding of $K$. Computing this restriction is supported in case $k$ appears
as a base field of (a base field) of $K$ or $\iota$ is provided:

```@docs
restrict(::NumFieldEmb, ::NumField)
restrict(::NumFieldEmb, ::NumFieldMor)
```

## Extension

Given a complex embedding $f \colon k \to \mathbf{C}$ and a morphism $\iota \colon k \to K$, an embedding $g \colon K \to \mathbf{C}$ is extension of $f$, if $g$ restricts to $f$. Given an embedding and a morphism,
all extensions can be computed as follows:

```@docs
extend(::NumFieldEmb, ::NumFieldMor)
```

## Example

As mentioned, this functionality works for all types of number fields.
Here is an example of an absolute non-simple number field.

```jldoctest
julia> Qx, x = QQ["x"];

julia> K, a = number_field([x^2 + 1, x^3 + 2], "a");

julia> emb = complex_embeddings(K)
6-element Vector{Hecke.NumFieldEmbNfAbsNS}:
 Embedding corresponding to ≈ [ 1.00 * i, -1.26]
 Embedding corresponding to ≈ [ 1.00 * i, 0.63 + 1.09 * i]
 Embedding corresponding to ≈ [ -1.00 * i, 0.63 + 1.09 * i]
 Embedding corresponding to ≈ [ -1.00 * i, -1.26]
 Embedding corresponding to ≈ [ -1.00 * i, 0.63 - 1.09 * i]
 Embedding corresponding to ≈ [ 1.00 * i, 0.63 - 1.09 * i]

julia> k, b = quadratic_field(-1);

julia> i = hom(k, K, a[1]);

julia> restrict(emb[1], i)
Embedding of
Imaginary quadratic field defined by x^2 + 1
corresponding to ≈ 1.00 * i

julia> restrict(emb[3], i)
Embedding of
Imaginary quadratic field defined by x^2 + 1
corresponding to ≈ -1.00 * i
```
