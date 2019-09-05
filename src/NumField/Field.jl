################################################################################
#
#  Base field
#
################################################################################

@doc Markdown.doc"""
    base_field(L::NumField) -> NumField

Given a number field $L/K$ this function returns the base field $K$.
For absolute extensions this returns $\mathbf{Q}$.
"""
base_field(::NumField)

_base_ring(K::NumField) = base_field(K)

_base_ring(::FlintRationalField) = FlintQQ

################################################################################
#
#  Predicates
#
################################################################################

export isabsolute

@doc Markdown.doc"""
    isabsolute(L::NumField) -> Bool

Returns whether $L$ is an absolute extension, that is, whether the base field
of $L$ is $\mathbf{Q}$.
"""
isabsolute(::NumField)

isabsolute(::NumField) = false

isabsolute(::NumField{fmpq}) = true

@doc Markdown.doc"""
    elem_type(L::NumField) -> Type

Returns the type of the elements of $L$.
"""
elem_type(::NumField)

################################################################################
#
#  Degree
#
################################################################################

@doc Markdown.doc"""
    degree(L::NumField) -> Int 

Given a number field $L/K$, this function returns the degree of $L$ over $K$.
"""
degree(A::NumField)

dim(K::NumField) = degree(K)

################################################################################
#
#  Absolute degree
#
################################################################################

@doc Markdown.doc"""
    absolute_degree(L::NumField) -> Int 

Given a number field $L/K$, this function returns the degree of $L$ over
$\mathbf Q$.
"""
function absolute_degree(A::NumField)
  return absolute_degree(base_field(A)) * degree(A)
end

################################################################################
#
#  Is simple extension
#
################################################################################

@doc Markdown.doc"""
    issimple(L::NumField) -> Bool

Given a number field $L/K$ this function returns whether $L$ is simple, that is,
whether $L/K$ is defined by a univariate polynomial$.
"""
issimple(a::NumField)

################################################################################
#
#  Number field creation
#
################################################################################

@doc Markdown.doc"""
    NumberField(f::Poly{NumFieldElem}, s::String;
                cached::Bool = false, check::Bool = false) -> NumField, NumFieldElem

Given an irreducible polynomial $f \in K[x]$ over some number field $K$, this
function creates the simple number field $L = K[x]/(x)$ and returns $(L, b)$,
where $b$ is the class of $x$ in $L$. The string `s` is used only for printing
the primitive element $b$.

Testing that $f$ is irreducible can be disabled by setting the keyword argument
`check` to `false`.
"""
NumberField(f::PolyElem{<:NumFieldElem}, s::String;
            cached::Bool = false, check::Bool = false) 

################################################################################
#
#  Is commutative
#
################################################################################

iscommutative(K::NumField) = true

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

## Non-simple

@doc Markdown.doc"""
    NumberField(f::Vector{PolyElem{<:NumFieldElem}}, s::String="_\$")
                                              -> NumField, Vector{NumFieldElem}

Given a list $f$ of univariate polynomials $f_1, \ldots, f_n \in K[x]$ over
some number field $K$, constructs the extension $K[x_1, \ldots, x_n]/(f_1(x_1),
\ldots, f_n(x_n))$.

The extensions $K[x]/(f_i)$ must be linearly disjoint or equivalently the ideal
$(f_1(x_1),\dotsc,f_n(x_n))$ must be maximal (although this is not tested).
"""
NumberField(::Vector{PolyElem{<:Union{NumFieldElem, fmpq}}}, ::String)

## Missing

@doc Markdown.doc"""
    basis(L::SimpleNumField) -> Vector{NumFieldElem}

Returns the canonical basis of a simple extension $L/K$, that is, the elements
$1,a,\dotsc,a^{d - 1}$, where $d$ is the degree of $K$ and $a$ the primitive
element.
"""
basis(::SimpleNumField)

@doc Markdown.doc"""
    basis(L::NonSimpleNumField) -> Vector{NumFieldElem}

Returns the canonical basis of a non-simple extension $L/K$. If $L = K(a_1,\dotsc,a_n)$
where each $a_i$ has degree $d_i$, then the basis will be $a_1^{i_1}\dotsm a_d^{i_d}$
with $0 \leq i_j d_j - 1$ for $1 \leq j \leq n$.
"""
basis(::NonSimpleNumField)

@doc Markdown.doc"""
    simple_extension(L::NonSimpleNumField) -> SimpleNumField, Map

Given a non-simple extension $L/K$, this function computes a simple extension $M/K$
and an $K$-linear isomorphism $M \to L$.
"""
simple_extension(::NonSimpleNumField)

@doc Markdown.doc"""
    absolute_field(L::NumField) -> NumField, Map

Given a number field $L$, this function returns an absolute simple number field $M/\mathbf{Q}$
together with a $\mathbf{Q}$-linear isomorphism $M \to K$.
"""
absolute_field(::NumField)

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

@doc Markdown.doc"""
    discriminant(L::SimpleNumField) -> NumFieldElem

The discriminant of the defining polynomial of $L$, *not* the discriminant of
the maximal order of $L$.
"""
function discriminant(K::SimpleNumField)
  return discriminant(defining_polynomial(K))
end

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

##

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

################################################################################
# 
#  Normal basis
#
################################################################################

@doc Markdown.doc"""
    normal_basis(L::NumField) -> NumFieldElem

Given a normal number field $L/K$, this function returns an element $a$ of $L$,
such that the orbit of $a$ under the Galois group of $L/K$ is an $K$-basis
of $L$.
"""
function normal_basis(L::NumField)
  n = degree(L)
  K = base_field(L)
  Aut = automorphisms(L)

  length(Aut) != degree(L) && error("The field is not normal over the rationals!")

  A = zero_matrix(K, n, n)
  r = one(L)
  while true
    r = rand(basis(L), -n:n)
    for i = 1:n
      y = Aut[i](r)
      for j = 1:n
        A[i,j] = coeff(y, j - 1)
      end
    end
    if !iszero(det(A))
      break
    end
  end
  return r
end

################################################################################
#
#  Check linearly disjointness
#
################################################################################

function _check_consistency(K::NonSimpleNumField)
  QQz, z = PolynomialRing(base_field(K), "z")
  for i = 1:length(K.pol)
    v = [zero(QQz) for i in 1:length(K.pol)]
    v[i] = z
    p = evaluate(K.pol[i], v)
    if !isirreducible(p)
      return false
    end
  end
  lg = gens(K)
  el = lg[1]
  f = minpoly(el)
  d = degree(f)
  for i = 2:length(lg)
    el += lg[i]
    f = minpoly(el)
    while !issquarefree(f)
      el += lg[i]
      f = minpoly(el)
    end
    if degree(f) != prod(degree(K.pol[j], j) for j = 1:i)
      return false
    end
    if !isirreducible(f)
      return false
    end 
  end
  return true
end
