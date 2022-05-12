################################################################################
#
#  Pure and Kummer extensions
#
################################################################################

@doc Markdown.doc"""
    is_radical_extension(L::SimpleNumField) -> Bool

Tests if $L/K$ is pure, that is, if the defining polynomial is of the form
$x^n - b$ for some $b \in K$.
"""
function is_radical_extension(K::SimpleNumField)
  if !is_monic(K.pol)
    return false
  end
  return all(i -> iszero(coeff(K.pol, i)), 1:degree(K)-1)
end

@doc Markdown.doc"""
    is_kummer_extension(L::SimpleNumField) -> Bool

Tests if $L/K$ is a Kummer extension, that is, if the defining polynomial is
of the form $x^n - b$ for some $b \in K$ and if $K$ contains the $n$-th roots
of unity.
"""
function is_kummer_extension(K::SimpleNumField)
  if !is_radical_extension(K)
    return false
  end

  k = base_field(K)
  Zk = maximal_order(k)
  _, o = torsion_units_gen_order(Zk)
  if o % degree(K) != 0
    return false
  end
  return true
end

function is_kummer_extension(K::AnticNumberField)
  if degree(K) != 2
    return false
  end
  return is_radical_extension(K)
end

function radical_extension(n::Int, a::FacElem, s::String = "_\$";
                        cached::Bool = true, check::Bool = true)
  return radical_extension(n, evaluate(a), s, cached = cached, check = check)
end

@doc Markdown.doc"""
    radical_extension(n::Int, a::NumFieldElem, s = "_$";
                   check = true, cached = true) -> NumField, NumFieldElem

Given an element $a$ of a number field $K$ and an integer $n$, create the simple
extension of $K$ with the defining polynomial $x^n - a$.

# Examples

```jldoctest
julia> radical_extension(5, QQ(2), "a")
(Number field over Rational Field with defining polynomial x^5 - 2, a)
```
"""
function radical_extension(n::Int, a::NumFieldElem, s::String = "_\$";
                        cached::Bool = true, check::Bool = true)
  k = parent(a)
  kx, x = PolynomialRing(k, cached = false)
  return number_field(x^n - a, s, check = check, cached = cached)
end

function radical_extension(n::Int, a::fmpq, s::String = "_\$";
                        cached::Bool = true, check::Bool = true)
  k = parent(a)
  kx, x = PolynomialRing(k, cached = false)
  return number_field(x^n - a, s, check = check, cached = cached)
end

################################################################################
#
#  Basis
#
################################################################################

@doc Markdown.doc"""
    basis(L::SimpleNumField) -> Vector{NumFieldElem}

Return the canonical basis of a simple extension $L/K$, that is, the elements
$1,a,\dotsc,a^{d - 1}$, where $d$ is the degree of $K$ and $a$ the primitive
element.

# Examples

```jldoctest
julia> Qx, x = QQ["x"];

julia> K, a = NumberField(x^2 - 2, "a");

julia> basis(K)
2-element Vector{nf_elem}:
 1
 a
```
"""
basis(::SimpleNumField)

################################################################################
#
#  Defining polynomial
#
################################################################################

export defining_polynomial

@doc Markdown.doc"""
    defining_polynomial(L::SimpleNumField) -> PolyElem

Given a simple number field $L/K$, constructed as $L = K[x]/(f)$, this function
returns $f$.
"""
defining_polynomial(::SimpleNumField)

defining_polynomial(K::NfRel) = K.pol

################################################################################
#
#  Discriminant
#
################################################################################

@doc Markdown.doc"""
    discriminant(L::SimpleNumField) -> NumFieldElem

The discriminant of the defining polynomial of $L$, *not* the discriminant of
the maximal order of $L$.
"""
function discriminant(K::SimpleNumField)
  return discriminant(defining_polynomial(K))
end

################################################################################
#
#  Absolute discriminant
#
################################################################################

@doc Markdown.doc"""
    absolute_discriminant(L::SimpleNumField, QQ) -> fmpq

The absolute discriminant of the defining polynomial of $L$, *not* the
discriminant of the maximal order of $L$. This is the norm of the discriminant
times the $d$-th power of the discriminant of the base field, where $d$ is the
degree of $L$.
"""
absolute_discriminant(::SimpleNumField)

function absolute_discriminant(K::AnticNumberField)
  return discriminant(K)
end

function absolute_discriminant(K::NfRel)
  d = norm(discriminant(K)) * absolute_discriminant(base_field(K))^degree(K)
  return d
end

function discriminant(K::FlintRationalField)
  return one(K)
end

################################################################################
#
#  Is subfield
#
################################################################################

@doc Markdown.doc"""
    is_subfield(K::SimpleNumField, L::SimpleNumField) -> Bool, Map

Return `true` and an injection from $K$ to $L$ if $K$ is a subfield of $L$.
Otherwise the function returns `false` and a morphism mapping everything to
$0$.
"""
is_subfield(::SimpleNumField, ::SimpleNumField)

@doc Markdown.doc"""
    is_isomorphic(K::SimpleNumField, L::SimpleNumField) -> Bool

Return `true` if $K$ and $L$ are isomorphic, otherwise `false`.
"""
is_isomorphic(K::SimpleNumField, L::SimpleNumField) = is_isomorphic_with_map(K, L)[1]

@doc Markdown.doc"""
    is_isomorphic_with_map(K::SimpleNumField, L::SimpleNumField) -> Bool, Map

Return `true` and an isomorphism from $K$ to $L$ if $K$ and $L$ are isomorphic.
Otherwise the function returns `false` and a morphism mapping everything to $0$.
"""
is_isomorphic_with_map(::SimpleNumField, ::SimpleNumField)

export is_isomorphic_with_map

################################################################################
#
#  Linear disjointness
#
################################################################################

# TODO (easy): Do this for Non-Simple number fields
@doc Markdown.doc"""
    is_linearly_disjoint(K::SimpleNumField, L::SimpleNumField) -> Bool

Given two number fields $K$ and $L$ with the same base field $k$, this function
returns whether $K$ and $L$ are linear disjoint over $k$.
"""
is_linearly_disjoint(K::SimpleNumField, L::SimpleNumField)

################################################################################
#
#  Primitive element
#
################################################################################

function primitive_element(K::SimpleNumField)
  return gen(K)
end
