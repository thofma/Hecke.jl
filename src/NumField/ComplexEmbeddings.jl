export complex_embeddings, real_embeddings, evaluation_function, complex_embedding

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

function Base.:(*)(f::NumFieldMor, e::NumFieldEmb)
  return restrict(e, f)
end

function compose(f::NumFieldMor, e::NumFieldEmb)
  return f * e
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

################################################################################
#
#  Sign
#
################################################################################

function sign(x::NumFieldElem, e::NumFieldEmb)
  @req parent(x) === number_field(e) "Parents must match"
  @req is_real(e) "Embedding must be real"
  @req !iszero(x) "Element must be non-zero"
  p = 32
  while true
    ex = e(x, p)
    if is_positive(real(ex))
      return 1
    elseif is_negative(real(ex))
      return -1 
    end
    p = 2 * p
  end
end

sign(x::NumFieldOrdElem, e...) = sign(elem_in_nf(x), e...)

function sign(x::FacElem{<:NumFieldElem}, e::NumFieldEmb)
  @req _base_ring(x) === number_field(e) "Parents must match"
  @req is_real(e) "Embedding must be real"
  s = 1
  for (k, ee) = x.fac
    if iseven(ee)
      continue
    end
    s = s * sign(k, e)
  end
  return s
end

@doc Markdown.doc"""
    signs(a::NumFieldElem, [p::Vector{NumFieldEmb = real_embeddings(K)]})
                                                            -> Dict{InfPlc, Int}

Return the signs of `a` at the complex embeddings in `p` as a dictionary.

# Examples

```jldoctest
julia> K, a = quadratic_field(3);

julia> signs(a)
Dict{Hecke.NumFieldEmbNfAbs, Int64} with 2 entries:
  Embedding corresponding to ≈ 1.73  => 1
  Embedding corresponding to ≈ -1.73 => -1
```
"""
function signs(a::Union{NumFieldElem, FacElem}, p::Vector{<: NumFieldEmb} = real_embeddings(_base_ring(a)))
  return Dict(q => sign(a, q) for q in p)
end

#signs(a) = signs(a, real_embeddings(parent(a)))
#
#signs(a::FacElem) = signs(a, real_embeddings(_base_ring(a)))

################################################################################
#
#  Positivity
#
################################################################################

@doc Markdown.doc"""
    is_positive(a::NumFieldElem, e::NumFieldEmb)   -> Bool

Given a number field element `a` and a real embedding `e`, return whether `a`
is positive at `e`.

# Examples

```jldoctest
julia> K, a  = quadratic_field(5);

julia> e = complex_embedding(K, 2.1);

julia> is_positive(a, e)
true
```
"""
is_positive(x::NumFieldElem, e::NumFieldEmb) = sign(x, e) == 1

@doc Markdown.doc"""
    is_positive(a::NumFieldElem, embs::Vector{NumFieldEmb}) -> Bool

Return whether the element $a$ is positive at all embeddings of `embs`. All
embeddings in `embs` must be real.

```jldoctest
julia> K, a  = quadratic_field(5);

julia> e = complex_embedding(K, 2.1);

julia> e(a)
[2.236067977 +/- 5.02e-10]

julia> is_positive(a, [e])
true
```
"""
function is_positive(a::Union{nf_elem, FacElem}, l::Vector{<: NumFieldEmb})
  return all(x -> is_positive(a, x), l)
end

@doc Markdown.doc"""
    is_totally_positive(a::NumFieldElem) -> Bool

Return whether the element $a$ is totally positive, that is, whether it is
positive at all real embeddings of the ambient number field.
"""
function is_totally_positive(a::Union{NumFieldElem, FacElem})
  K = _base_ring(a)
  return is_positive(a, real_embeddings(K))
end

is_positive(a::NumFieldOrdElem, e...) = is_positive(elem_in_nf(a), e...)

is_totally_positive(a::NumFieldOrdElem, e...) = is_totally_positive(elem_in_nf(a), e...)

################################################################################
#
#  Negativity
#
################################################################################

@doc Markdown.doc"""
    is_negative(a::NumFieldElem, e::NumFieldEmb)   -> Bool

Given a number field element `a` and a real embedding `e`, return whether `a`
is positive at `e`.

# Examples

```jldoctest
julia> K, a  = quadratic_field(5);

julia> e = complex_embedding(K, 2.1);

julia> is_negative(a, e)
false
```
"""
is_negative(x::NumFieldElem, e::NumFieldEmb) = sign(x, e) == -1

@doc Markdown.doc"""
    is_negative(a::NumFieldElem, embs::Vector{NumFieldEmb}) -> Bool

Return whether the element $a$ is positive at all embeddings of `embs`. All
embeddings in `embs` must be real.

# Examples

```jldoctest
julia> K, a  = quadratic_field(5);

julia> e = complex_embedding(K, -2.1);

julia> e(a)
[-2.236067977 +/- 5.02e-10]

julia> is_negative(a, [e])
true
```
"""
function is_negative(a::Union{nf_elem, FacElem}, l::Vector{<: NumFieldEmb})
  return all(x -> is_negative(a, x), l)
end

is_negative(a::NumFieldOrdElem, e...) = is_positive(elem_in_nf(a), e...)

################################################################################
#
#  Embedding for QQ
#
################################################################################

struct QQEmb <: NumFieldEmb{FlintRationalField}
end

function Base.show(io::IO, ::QQEmb)
  print(io, "Complex embedding of rational numbers")
end

number_field(::QQEmb) = QQ

(::QQEmb)(x::fmpq, prec::Int = 32) = ArbField(prec)(x)

real_embeddings(::FlintRationalField) = [QQEmb()]

complex_embeddings(::FlintRationalField) = [QQEmb()]

is_real(::QQEmb) = true

restrict(::NumFieldEmb, ::FlintRationalField) = QQEmb()

_embedding(::PosInf) = QQEmb()

evaluate(x::fmpq, ::QQEmb, prec::Int = 32) = AcbField(prec)(x)

evaluate(x::fmpz, ::QQEmb, prec::Int = 32) = AcbField(prec)(x)

is_positive(x::Union{fmpz, fmpq}, ::QQEmb) = x > 0

is_totally_positive(x::Union{fmpz,fmpq}) = is_positive(x)

is_negative(x::Union{fmpz, fmpq}, ::QQEmb) = x < 0
