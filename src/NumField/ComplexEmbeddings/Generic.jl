@doc raw"""
    complex_embeddings(K::NumField; conjugates::Bool = true) -> Vector{NumFieldEmb}

Return the complex embeddings of $K$. If `conjugates` is `false`, only one
imaginary embedding per conjugated pairs is returned.

# Examples

```jldoctest
julia> K, a = quadratic_field(-3);

julia> complex_embeddings(K)
2-element Vector{AbsSimpleNumFieldEmbedding}:
 Complex embedding corresponding to 0.00 + 1.73 * i of imaginary quadratic field
 Complex embedding corresponding to 0.00 - 1.73 * i of imaginary quadratic field

julia> complex_embeddings(K, conjugates = false)
1-element Vector{AbsSimpleNumFieldEmbedding}:
 Complex embedding corresponding to 0.00 + 1.73 * i of imaginary quadratic field
```
"""
complex_embeddings(K::NumField)

@doc raw"""
    real_embeddings(K::NumField) -> Vector{NumFieldEmb}

Return the real embeddings of $K$.

# Examples

```jldoctst
julia> K, a = quadratic_field(3);

julia> real_embeddings(K)
2-element Vector{AbsSimpleNumFieldEmbedding}:
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

@doc raw"""
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

@doc raw"""
    is_real(f::NumFieldEmb) -> Bool

Return `true` if the embedding is real.

# Examples

```jldoctest
julia> K, a = quadratic_field(3); e = complex_embeddings(K)[1];

julia> is_real(e)
true
```
"""
is_real(f::NumFieldEmb)

@doc raw"""
    is_imaginary(f::NumFieldEmb) -> Bool

Returns `true` if the embedding is imaginary, that is, not real.

# Examples

```jldoctest
julia> K, a = quadratic_field(-3); e = complex_embeddings(K)[1];

julia> is_imaginary(e)
true
```
"""
is_imaginary(f::NumFieldEmb) = !is_real(f)

@doc raw"""
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

@doc raw"""
    restrict(f::NumFieldEmb, K::NumField)

Given an embedding $f$ of a number field $L$ and a number field $K$ appearing
as a base field of $L$, return the restriction of $f$ to $K$.

# Examples

```jldoctest
julia> K, a = quadratic_field(3);

julia> L, b = number_field(polynomial(K, [1, 0, 1]), "b");

julia> e = complex_embeddings(L);

julia> restrict(e[1], K)
Complex embedding corresponding to -1.73
  of real quadratic field defined by x^2 - 3
```
"""
restrict(f::NumFieldEmb, K::NumField)

@doc raw"""
    restrict(f::NumFieldEmb, g::NumFieldHom)

Given an embedding $f$ of a number field $L$ and a morphism $g \colon K \to L$,
return the embedding $g \circ f$ of $K$.

This is the same as `g * f`.

# Examples

```jldoctest
julia> K, a = cyclotomic_field(5, "a");

julia> k, ktoK = Hecke.subfield(K, [a + inv(a)]);

julia> e = complex_embeddings(K);

julia> restrict(e[1], ktoK)
Complex embedding corresponding to 0.62
  of number field with defining polynomial x^2 + x - 1
    over rational field
```
"""
restrict(f::NumFieldEmb, K::NumFieldHom)

################################################################################
#
#  Extension
#
################################################################################

@doc raw"""
    extend(e::NumFieldEmb, f::NumFieldHom)

Given an embedding $e$ of $k$ and a morphism $f \colon k \to K$, determine
all embedings of $K$ which restrict to $e$ along $f$.

# Example

```jldoctest
julia> K, a = cyclotomic_field(5, "a");

julia> k, ktoK = Hecke.subfield(K, [a + inv(a)]);

julia> e = complex_embeddings(k)[1];

julia> extend(e, ktoK)
2-element Vector{AbsSimpleNumFieldEmbedding}:
 Complex embedding corresponding to -0.81 + 0.59 * i of cyclotomic field of order 5
 Complex embedding corresponding to -0.81 - 0.59 * i of cyclotomic field of order 5
```
"""
function extend(e::NumFieldEmb, f::NumFieldHom)
  @req number_field(e) === domain(f) "Number field of embedding must be domain"
  emb = complex_embeddings(codomain(f))
  res = eltype(emb)[ E for E in emb if f * E == e ]
  @assert length(res) == div(absolute_degree(codomain(f)),
                             absolute_degree(domain(f)))
  return res
end

function Base.:(*)(f::NumFieldHom, e::NumFieldEmb)
  return restrict(e, f)
end

function compose(f::NumFieldHom, e::NumFieldEmb)
  return f * e
end

################################################################################
#
#  Evaluation function
#
################################################################################

# Extension to order elements

(f::NumFieldEmb)(x::NumFieldOrderElem, prec::Int = 32) = f(elem_in_nf(x), prec)

@doc raw"""
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

@doc raw"""
    sign(x::NumFieldElem, e::NumFieldEmb) -> Int

Given a number field element `x` and a complex embedding `e`, return `1`, `-1`
or `0` depending on whether `e(x)` is positive, negative, or zero.

# Examples

```jldoctest
julia> K, a = quadratic_field(3);

julia> e = complex_embedding(K, 1.7);

julia> sign(a, e)
1
```
"""
function sign(x::NumFieldElem, e::NumFieldEmb)
  @req parent(x) === number_field(e) "Parents must match"
  @req is_real(e) "Embedding must be real"
  iszero(x) && return 0
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

sign(x::NumFieldOrderElem, e::NumFieldEmb) = sign(elem_in_nf(x), e)

function sign(x::FacElem{<:NumFieldElem}, e::NumFieldEmb)
  @req _base_ring(x) === number_field(e) "Parents must match"
  @req is_real(e) "Embedding must be real"
  s = 1
  for (k, ee) = x
    if iseven(ee)
      continue
    end
    s = s * sign(k, e)
  end
  return s
end

@doc raw"""
    signs(a::NumFieldElem, [embs::Vector{NumFieldEmb} = real_embeddings(K)])
                                                       -> Dict{NumFieldEmb, Int}

Return the signs of `a` at the real embeddings in `embs` as a dictionary, which
are by default all real embeddings of the number field.

# Examples

```jldoctest; filter = r"Complex.*"
julia> K, a = quadratic_field(3);

julia> signs(a)
Dict{AbsSimpleNumFieldEmbedding, Int64} with 2 entries:
  Complex embedding corresponding to -1.73 of real quadratic field define… => -1
  Complex embedding corresponding to 1.73 of real quadratic field defined… => 1
```
"""
function signs(a::Union{NumFieldElem, FacElem, NumFieldOrderElem},
               p::Vector{<: NumFieldEmb} = real_embeddings(_base_ring(a)))
  return Dict(q => sign(a, q) for q in p)
end

################################################################################
#
#  Positivity
#
################################################################################

@doc raw"""
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
is_positive(x::Union{NumFieldElem, FacElem}, e::NumFieldEmb) = sign(x, e) == 1

@doc raw"""
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
function is_positive(a::Union{NumFieldElem, FacElem}, l::Vector{<: NumFieldEmb})
  return all(x -> is_positive(a, x), l)
end

@doc raw"""
    is_totally_positive(a::NumFieldElem) -> Bool

Return whether the element $a$ is totally positive, that is, whether it is
positive at all real embeddings of the ambient number field.
"""
function is_totally_positive(a::Union{NumFieldElem, FacElem})
  K = _base_ring(a)
  return is_positive(a, real_embeddings(K))
end

is_positive(a::NumFieldOrderElem, e...) = is_positive(elem_in_nf(a), e...)

is_totally_positive(a::NumFieldOrderElem, e...) =
    is_totally_positive(elem_in_nf(a), e...)

################################################################################
#
#  Negativity
#
################################################################################

@doc raw"""
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
is_negative(x::Union{NumFieldElem, FacElem}, e::NumFieldEmb) = sign(x, e) == -1

@doc raw"""
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
function is_negative(a::Union{NumFieldElem, FacElem}, l::Vector{<: NumFieldEmb})
  return all(x -> is_negative(a, x), l)
end

is_negative(a::NumFieldOrderElem, e...) = is_negative(elem_in_nf(a), e...)

################################################################################
#
#  Logarithmic embedding
#
################################################################################

(::typeof(abs))(e::NumFieldEmb) = ComposedFunction(abs, e)

(::typeof(log))(f::ComposedFunction{typeof(abs), <: NumFieldEmb}) =
    ComposedFunction(log, f)

function (f::ComposedFunction{typeof(log), ComposedFunction{typeof(abs), T}})(x::Union{NumFieldElem, NumFieldOrderElem, FacElem}, prec::Int = 64) where {T}
  return _log_evaluate_fac_elem(f.inner.inner, x, prec)
end

################################################################################
#
#  Factored elements
#
################################################################################

function _evaluate_fac_elem(e, x, prec)
  z = one(AcbField(prec, cached = false))
  for (b, n) in x
    z = z * e(b, prec)^n
  end
  return z
end

function (e::NumFieldEmb{T})(x::FacElem{S, T}, prec::Int = 64) where {S, T}
  wprec = Base.trunc(Int, prec * 1.3)
  z = _evaluate_fac_elem(e, x, wprec)
  while !radiuslttwopower(z, -prec)
    wprec = Base.trunc(Int, wprec * 1.3)
    z = _evaluate_fac_elem(e, x, wprec)
  end
  return z
end

function __log_evaluate_fac_elem(e, x::NumFieldOrderElem, prec)
  return __log_evaluate_fac_elem(e, elem_in_nf(x, copy = false), prec)
end

function __log_evaluate_fac_elem(e, x::NumFieldElem, prec)
  return log(abs(e(x, prec)))
end

function __log_evaluate_fac_elem(e, x, prec)
  z = zero(ArbField(prec, cached = false))
  for (b, n) in x
    z = z + n * log(abs(e(b, prec)))
  end
  return z
end

function _log_evaluate_fac_elem(e, x, prec)
  wprec = Base.trunc(Int, prec * 1.3)
  z = __log_evaluate_fac_elem(e, x, wprec)
  while !radiuslttwopower(z, -prec)
    wprec = Base.trunc(Int, wprec * 1.3)
    z = __log_evaluate_fac_elem(e, x, wprec)
  end
  return z
end

################################################################################
#
#  Complex conjugation
#
################################################################################

function complex_conjugation(K::NumField)
  L, f = absolute_simple_field(K)
  g = inv(f)
  conj = complex_conjugation(L)
  return compose(compose(g, conj), f)
end
