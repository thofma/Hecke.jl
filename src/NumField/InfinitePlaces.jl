################################################################################
#
#  Infinite places for number fields
#
#
#  (C) 2017 Tommy Hofmann
#
################################################################################

export is_complex,
       is_positive,
       is_totally_positive,
       signs,
       sign,
       real_places,
       complex_places,
       infinite_places,
       infinite_place,
       embedding,
       embeddings,
       absolute_value

################################################################################
#
#  Field access
#
################################################################################

# this is internal and not part of the interface!
_embedding(p::InfPlc) = p.embedding

embedding(p::PosInf) = QQEmb()

embeddings(p::PosInf) = [QQEmb()]

@doc Markdown.doc"""
    embedding(p::InfPlc) -> NumFieldEmb

Given a real infinite place, return the unique real embedding defining
this place. If the infinite place is not real, an error is thrown.

See also [`embeddings`](@ref).

# Examples

```juldoctest
julia> K, a = quadratic_field(5);

julia> embedding(real_places(K)[1])
Embedding of
Real quadratic field defined by x^2 - 5
corresponding to ≈ -2.24
"""
function embedding(p::InfPlc)
  if is_complex(p)
    throw(ArgumentError("No unique embedding inducing complex infinite place.\n" *
                        "Use `embeddings(p)` to get all embeddings."))
  end
  return _embedding(p)
end

@doc Markdown.doc"""
    embeddings(p::InfPlc) -> Vector{NumFieldEmb}

Given a complex place, return all complex embeddings defining this place.

See also [`embedding`](@ref).

# Examples

```jldoctest
julia> K,  = quadratic_field(-5);

julia> embeddings(complex_places(K)[1])
2-element Vector{Hecke.NumFieldEmbNfAbs}:
 Embedding corresponding to ≈ 0.00 + 2.24 * i
 Embedding corresponding to ≈ 0.00 - 2.24 * i
```
"""
function embeddings(p::InfPlc)
  if is_real(p)
    return [_embedding(p)]
  else
    e = _embedding(p)
    return [e, conj(e)]
  end
end

@doc Markdown.doc"""
    number_field(p::InfPlc) -> NumField

Return the number field of the infinite place.

# Examples

```jldoctest
julia> K, = quadratic_field(5);

julia> p = infinite_places(K)[1];

julia> number_field(p) == K
true
```
"""
number_field(p::InfPlc) = number_field(_embedding(p))

################################################################################
#
#  Equality and hashing
#
################################################################################

function ==(p::InfPlc, q::InfPlc)
  ep = _embedding(p)
  eq = _embedding(q)
  return ep == eq || ep == conj(eq)
end

function Base.hash(p::InfPlc, h::UInt)
  return Base.hash(_embedding(p), h)
end

################################################################################
#
#  I/O
#
################################################################################
 
function Base.show(io::IO, ::MIME"text/plain", p::InfPlc)
  print(io, "Infinite place of\n", number_field(p), "\ncorresponding to\n",
        _embedding(p))
end

function Base.show(io::IO, p::InfPlc)
  print(io, "Infinite place corresponding to (", _embedding(p), ")")
end

################################################################################
#
#  Predicates
#
################################################################################

@doc Markdown.doc"""
    is_real(p::InfPlc) -> Bool

Return whether the infinite place `p` is real.

```jldoctest
julia> K, = quadratic_field(3);

julia> is_real(infinite_places(K)[1])
true
```
"""
is_real(p::InfPlc) = is_real(_embedding(p))

@doc Markdown.doc"""
    is_real(p::InfPlc) -> Bool

Return whether the infinite place `p` is complex.

```jldoctest
julia> K, = quadratic_field(3);

julia> is_complex(infinite_places(K)[1])
false
```
"""
is_complex(p::InfPlc) = is_imaginary(_embedding(p))

################################################################################
#
#  Construction
#
################################################################################

@doc Markdown.doc"""
    infinite_place(e::NumFieldEmb)

Construct the infinite place induced by the given complex embedding.
```jldoctest
julia> K,  = quadratic_field(5);

julia> infinite_place(complex_embedding(K, 2.24))
Infinite place of
Real quadratic field defined by x^2 - 5
corresponding to
Embedding corresponding to ≈ 2.24
```
"""
function infinite_place(e::NumFieldEmb)
  return InfPlc(e)
end

@doc Markdown.doc"""
    infinite_places(K::NumField) -> Vector{InfPlc}

Return all infinite places of the number field.

# Examples

```jldoctest
julia> K,  = quadratic_field(5);

julia> infinite_places(K)
2-element Vector{InfPlc{AnticNumberField, Hecke.NumFieldEmbNfAbs}}:
 Infinite place corresponding to (Embedding corresponding to ≈ -2.24)
 Infinite place corresponding to (Embedding corresponding to ≈ 2.24)
```
"""
function infinite_places(K::NumField)
  return infinite_place.(complex_embeddings(K, conjugates = false))
end

@doc Markdown.doc"""
    real_places(K::NumField) -> Vector{InfPlc}

Return all infinite real places of the number field.

# Examples

```jldoctest
julia> K,  = quadratic_field(5);

julia> infinite_places(K)
2-element Vector{InfPlc{AnticNumberField, Hecke.NumFieldEmbNfAbs}}:
 Infinite place corresponding to (Embedding corresponding to ≈ -2.24)
 Infinite place corresponding to (Embedding corresponding to ≈ 2.24)
```
"""
real_places(K::NumField) = infinite_place.(real_embeddings(K))

@doc Markdown.doc"""
    complex_places(K::NumField) -> Vector{InfPlc}

Return all infinite complex places of $K$.

# Examples

```jldoctest
julia> K,  = quadratic_field(-5);

julia> complex_places(K)
1-element Vector{InfPlc{AnticNumberField, Hecke.NumFieldEmbNfAbs}}:
 Infinite place corresponding to (Embedding corresponding to ≈ 0.00 + 2.24 * i)
```
"""
complex_places(K::NumField) = [p for p in infinite_places(K) if is_complex(p)]

################################################################################
#
#  Restriction
#
################################################################################

@doc Markdown.doc"""
    restrict(p::InfPlc, K::NumField)

Given an infinite place `p` of a number field `L` and a number field `K`
appearing as a base field of `L`, return the restriction of `p` to `L`.

# Examples

```jldoctest
julia> K, a = quadratic_field(3);

julia> L, b = NumberField(polynomial(K, [1, 0, 1]), "b");

julia> p = complex_places(L)[1];

julia> restrict(p, K)
Infinite place of
Real quadratic field defined by x^2 - 3
corresponding to
Embedding corresponding to ≈ -1.73
```
"""
restrict(p::InfPlc, K::NumField) = infinite_place(restrict(_embedding(p), K))

restrict(p::Union{InfPlc, PosInf}, ::QQField) = inf

################################################################################
#
#  Extension
#
################################################################################
 
@doc Markdown.doc"""
    extend(p::InfPlc, L::NumField) -> Vector{InfPlc}

Given an infinite place `p` of a number field `K` and an extension `L` of `K`,
return all infinite places of `L` lying above `p`.

# Examples

```jldoctest
julia> K, a = quadratic_field(3);

julia> L, b = NumberField(polynomial(K, [-2, 0, 0, 1]), "b");

julia> p = infinite_places(K)[1];

julia> extend(p, L)
2-element Vector{InfPlc{Hecke.NfRel{nf_elem}, Hecke.NumFieldEmbNfRel{Hecke.NumFieldEmbNfAbs, Hecke.NfRel{nf_elem}}}}:
 Infinite place corresponding to (Embedding corresponding to (Embedding corresponding to ≈ -1.73) and ≈ 1.26)
 Infinite place corresponding to (Embedding corresponding to (Embedding corresponding to ≈ -1.73) and ≈ -0.63 + 1.09 * i)
```
"""
function extend(p::InfPlc, L::NumField)
  l = infinite_places(L)
  return place_type(L)[P for P in l if restrict(P, number_field(p)) == p]
end

################################################################################
#
#  Action of a morphism on a infinite place
#
################################################################################

#The action of f on P is defined as f(P) = P\circ f^{-1} and not P\circ f
#In this way, (f\circ g)(P)= f(g(P)), otherwise it would fail.

@doc Markdown.doc"""
    induce_image(m::NfToNfMor, P::InfPlc) -> InfPlc

Find a place in the image of $P$ under $m$. If $m$ is an automorphism,
this is unique.
"""
function induce_image(m::NfToNfMor, P::InfPlc)
  return infinite_place(first(extend(_embedding(P), m)))
end

################################################################################
#
#  Absolute value
#
################################################################################

@doc Markdown.doc"""
    absolute_value(x::NumFieldElem, p::InfPlc, prec::Int = 32) -> arb

Return the evaluation of `x` at the normalized absolute valuation contained
in the infinite place. If `e` is a complex embedding inducing `p`,
this is `abs(e(x))` if `e` is real and `abs(e(x))^2` otherwise.

```jldoctest
julia> Qx, x = QQ["x"];

julia> K, a = number_field(x^3 - 2, "a");

julia> absolute_value(a, real_places(K)[1])
[1.2599210499 +/- 8.44e-11]

julia> absolute_value(a, complex_places(K)[1])
[1.587401052 +/- 6.63e-10]
```
"""
function absolute_value(x::NumFieldElem, p::InfPlc, prec::Int = 32)
  if is_real(p)
    return abs(_embedding(p)(x, prec))
  else
    return abs(_embedding(p)(x, prec))^2
  end
end

################################################################################
#
#  Positivity and signs
#
################################################################################

function sign(x::Union{NumFieldElem, FacElem, NumFieldOrdElem}, p::InfPlc)
  return sign(x, _embedding(p))
end

function signs(x::Union{NumFieldElem, FacElem, NumFieldOrdElem}, ps::Vector{<: InfPlc})
  return Dict(p => sign(x, p) for p in ps)
end

is_positive(x::Union{NumFieldElem, FacElem}, p::InfPlc) = is_positive(x, _embedding(p))

is_negative(x::Union{NumFieldElem, FacElem}, p::InfPlc) = is_negative(x, _embedding(p))

function is_positive(x::Union{NumFieldElem, FacElem},
                             ps::Vector{<: InfPlc})
  return all(is_positive(x, p) for p in ps)
end

function is_negative(x::Union{NumFieldElem, FacElem},
                             ps::Vector{<: InfPlc})
  return all(is_negative(x, p) for p in ps)
end
