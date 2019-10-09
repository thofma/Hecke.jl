################################################################################
#
#  Pure and Kummer extensions
#
################################################################################

@doc Markdown.doc"""
    isradical_extension(L::SimpleNumField) -> Bool

Tests if $L/K$ is pure, that is, if the defining polynomial is of the form
$x^n - b$ for some $b \in K$.
"""
function isradical_extension(K::SimpleNumField)
  if !ismonic(K.pol)
    return false
  end
  return all(i -> iszero(coeff(K.pol, i)), 1:degree(K)-1)
end

@doc Markdown.doc"""
    iskummer_extension(L::SimpleNumField) -> Bool

Tests if $L/K$ is a Kummer extension, that is, if the defining polynomial is
of the form $x^n - b$ for some $b \in K$ and if $K$ contains the $n$-th roots
of unity.
"""
function iskummer_extension(K::SimpleNumField)
  if !isradical_extension(K)
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

function iskummer_extension(K::AnticNumberField)
  if degree(K) != 2
    return false
  end
  return isradical_extension(K)
end

function radical_extension(n::Int, a::FacElem;
                        cached::Bool = true, check::Bool = true)
  return radical_extension(n, evaluate(a), cached = cached, check = check)
end

@doc Markdown.doc"""
    radical_extension(n::Int, a::NumFieldElem; s = "_$",
                   check = true, cached = true) -> NumField, NumFieldElem

Given an element $a$ of a number field $K$ and an integer $n$, create the simple
extension of $K$ with the defining polynomial $x^n - a$.
"""
function radical_extension(n::Int, a::NumFieldElem; s::String = "_\$",
                        cached::Bool = true, check::Bool = true)
  k = parent(a)
  kx, x = PolynomialRing(k, cached = false)
  return number_field(x^n - a, s, check = check, cached = cached)
end

function radical_extension(n::Int, a::fmpq; s::String = "_\$",
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

Returns the canonical basis of a simple extension $L/K$, that is, the elements
$1,a,\dotsc,a^{d - 1}$, where $d$ is the degree of $K$ and $a$ the primitive
element.
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

defining_polynomial(K::AnticNumberField) = K.pol

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
    issubfield(K::SimpleNumField, L::SimpleNumField) -> Bool, Map

Returns `true` and an injection from $K$ to $L$ if $K$ is a subfield of $L$.
Otherwise the function returns `false` and a morphism mapping everything to
$0$.
"""
issubfield(::SimpleNumField, ::SimpleNumField)

@doc Markdown.doc"""
    isisomorphic(K::SimpleNumField, L::SimpleNumField) -> Bool, Map

Returns `true` and an isomorphism from $K$ to $L$ if $K$ and $L$ are isomorphic.
Otherwise the function returns `false` and a morphism mapping everything to $0$.
"""
isisomorphic(::SimpleNumField, ::SimpleNumField)

################################################################################
#
#  Linear disjointness
#
################################################################################

# TODO (easy): Do this for Non-Simple number fields
@doc Markdown.doc"""
    islinear_disjoint(K::SimpleNumField, L::SimpleNumField) -> Bool

Given two number fields $K$ and $L$ with the same base field $k$, this function
returns whether $K$ and $L$ are linear disjoint over $k$.
"""
islinear_disjoint(K::SimpleNumField, L::SimpleNumField)


