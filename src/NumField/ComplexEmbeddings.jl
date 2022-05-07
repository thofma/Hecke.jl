export complex_embeddings, real_embeddings, evaluation_function

@doc Markdown.doc"""
    complex_embeddings(K::NumField; conjugates::Bool = true) -> Vector{NumFieldEmb}

Return the complex embeddings of $K$. If `conjugates` is `false`, only one
imaginary embedding per conjugated pairs is returned.

# Examples

```jldoctest
julia> K, a = quadratic_field(-3);

julia> complex_embeddings(K)
2-element Vector{Hecke.NumFieldEmbNfAbs}:
 Embedding corresponding to ≈ 0.00 + 1.73 * i
 Embedding corresponding to ≈ 0.00 - 1.73 * i

julia> complex_embeddings(K, conjugates = false)
1-element Vector{Hecke.NumFieldEmbNfAbs}:
 Embedding corresponding to ≈ 0.00 + 1.73 * i
```
"""
complex_embeddings(K::NumField)

@doc Markdown.doc"""
    real_embeddings(K::NumField) -> Vector{NumFieldEmb}

Return the real embeddings of $K$.

# Examples

```jldoctst
julia> K, a = quadratic_field(3);

julia> real_embeddings(K)
2-element Vector{Hecke.NumFieldEmbNfAbs}:
 Embedding corresponding to ≈ -1.73
 Embedding corresponding to ≈ 1.73
```
"""
function real_embeddings(K::NumField)
  res = get_attribute!(K, :real_embeddings) do
    r, s = signature(K)
    return complex_embeddings(K)[1:r]
  end::Vector{embedding_type(K)}
end

@doc Markdown.doc"""
    number_field(f::NumFieldEmb) -> NumField

Return the corresponding number field of the embedding $f$.

# Examples

```jldoctet
julia> K, a = quadratic_field(-3); e = complex_embeddings(K)[1];

julia> number_field(e)
Imaginary quadratic field defined by x^2 + 3
```
"""
number_field(::NumFieldEmb)

@doc Markdown.doc"""
    isreal(f::NumFieldEmb) -> Bool

Return `true` if the embedding is real.

# Examples

```jldoctest
julia> K, a = quadratic_field(3); e = complex_embeddings(K)[1];

julia> isreal(e)
true
```
"""
isreal(f::NumFieldEmb)

@doc Markdown.doc"""
    is_imaginary(f::NumFieldEmb) -> Bool

Returns `true` if the embedding is imaginary, that is, not real.

# Examples

```jldoctest
julia> K, a = quadratic_field(-3); e = complex_embeddings(K)[1];

julia> is_imaginary(e)
true
```
"""
is_imaginary(f::NumFieldEmb) = !isreal(f)

@doc Markdown.doc"""
    conj(f::NumFieldEmb) -> NumFieldEmb

Returns the conjugate embedding of `f`.

# Examples

```jldoctest
julia> K, a = quadratic_field(-3); e = complex_embeddings(K);

julia> conj(e[1]) == e[2]
true
```
"""
conj(f::NumFieldEmb)

# Restriction

@doc Markdown.doc"""
    restrict(f::NumFieldEmb, K::NumField)

Given an embedding $f$ of a number field $L$ and a number field $K$ appearing
as a base field of $L$, return the restriction of $f$ to $L$.

# Examples

```jldoctest
julia> K, a = quadratic_field(3);

julia> L, b = NumberField(polynomial(K, [1, 0, 1]), "b");

julia> e = complex_embeddings(L);

julia> restrict(e[1], K)
Embedding of
Real quadratic field defined by x^2 - 3
corresponding to ≈ -1.73
```
"""
restrict(f::NumFieldEmb, K::NumField)

@doc Markdown.doc"""
    restrict(f::NumFieldEmb, g::NumFieldMor)

Given an embedding $f$ of a number field $L$ and a morphism $g \colon K \to L$,
return the embedding $g \circ f$ of $K$.

This is the same as `g * f`.

# Examples

```jldoctest
julia> K, a = CyclotomicField(5, "a");

julia> k, ktoK = Hecke.subfield(K, [a + inv(a)]);

julia> e = complex_embeddings(K);

julia> restrict(e[1], ktoK)
Embedding of
Number field over Rational Field with defining polynomial x^2 + x - 1
corresponding to ≈ 0.62
```
"""
restrict(f::NumFieldEmb, K::NumFieldMor)

function Base.:(*)(f::NumFieldMor, e::NumFieldEmb)
  return restrict(e, f)
end

################################################################################
#
#  Extension
#
################################################################################

@doc Markdown.doc"""
    extend(e::NumFieldEmb, f::NumFieldMor)

Given an embedding $e$ of $k$ and a morphism $f \colon k \to K$, determine
all embedings of $K$ which restrict to $e$ along $f$.

# Example

```jldoctest
julia> K, a = CyclotomicField(5, "a");

julia> k, ktoK = Hecke.subfield(K, [a + inv(a)]);

julia> e = complex_embeddings(k)[1];

julia> extend(e, ktoK)
2-element Vector{Hecke.NumFieldEmbNfAbs}:
 Embedding corresponding to ≈ 0.31 + 0.95 * i
 Embedding corresponding to ≈ 0.31 - 0.95 * i
```
"""
function extend(e::NumFieldEmb, f::NumFieldMor)
  @req number_field(e) === domain(f) "Number field of embedding must be domain"
  emb = complex_embeddings(codomain(f))
  res = eltype(emb)[ E for E in emb if f * E == e ]
  @assert length(res) == div(absolute_degree(codomain(f)), absolute_degree(domain(f)))
  return res
end

################################################################################
#
#  Evaluation function
#
################################################################################

@doc Markdown.doc"""
    evaluation_function(e::NumFieldEmb, prec::Int) -> Function

Return the anonymous function `x -> e(x, prec)`.

# Examples

```jldoctest
julia> K, a = quadratic_field(-3);

julia> e = complex_embeddings(K)[1];

julia> fn = evaluation_function(e, 64);

julia> fn(a)
[+/- 3.99e-77] + [1.73205080756887729353 +/- 5.41e-21]*im
```
"""
function evaluation_function(e::NumFieldEmb, prec::Int = 32)
  return x -> e(x, prec)
end
