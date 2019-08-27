################################################################################
#
#  Base field
#
################################################################################

@doc Markdown.doc"""
    base_field(L::NumField) -> NumField

Given a number field $L/K$ this function returns the base field $K$.
For absolute extensions this returns `QQ`.
"""
base_field(::NumField)

_base_ring(K::NumField) = base_field(K)

_base_ring(::FlintRationalField) = FlintQQ

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
    ispure_extension(L::SimpleNumField) -> Bool

Tests if $L/K$ is pure, that is, if the defining polynomial is of the form
$x^n - b$ for some $b \in K$.
"""
function ispure_extension(K::SimpleNumField)
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
  if !ispure_extension(K)
    return false
  end

  k = base_field(K)
  Zk = maximal_order(k)
  _, o = Hecke.torsion_units_gen_order(Zk)
  if o % degree(K) != 0
    return false
  end
  return true
end

function iskummer_extension(K::AnticNumberField)
  if degree(K) != 2
    return false
  end
  return ispure_extension(K)
end

function pure_extension(n::Int, a::FacElem;
                        cached::Bool = true, check::Bool = true)
  return pure_extension(n, evaluate(a), cached = cached, check = check)
end

@doc Markdown.doc"""
    pure_extension(n::Int, a::NumFieldElem; s = "_$",
                   check = true, cached = true) -> NumField, NumFieldElem

Given an element $a$ of a number field $K$ and an integer $n$, create the simple
extension of $K$ with the defining polynomial $x^n - a$.
"""
function pure_extension(n::Int, a::NumFieldElem; s::String = "_\$",
                        cached::Bool = true, check::Bool = true)
  k = parent(a)
  kx, x = PolynomialRing(k, cached = false)
  return number_field(x^n - a, s, check = check, cached = cached)
end

function pure_extension(n::Int, a::fmpq; s::String = "_\$",
                        cached::Bool = true, check::Bool = true)
  k = parent(a)
  kx, x = PolynomialRing(k, cached = false)
  return number_field(x^n - a, s, check = check, cached = cached)
end
