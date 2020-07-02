################################################################################
#
#  Constructor
#
################################################################################

@doc Markdown.doc"""
    NumberField(f::Vector{PolyElem{<:NumFieldElem}}, s::String="_\$", check = true)
                                              -> NumField, Vector{NumFieldElem}

Given a list $f_1, \ldots, f_n$ of univariate polynomials in $K[x]$ over
some number field $K$, constructs the extension $K[x_1, \ldots, x_n]/(f_1(x_1),
\ldots, f_n(x_n))$.
"""
NumberField(::Vector{PolyElem{<:Union{NumFieldElem, fmpq}}}, ::String, check::Bool = true)

################################################################################
#
#  Basis
#
################################################################################

@doc Markdown.doc"""
    basis(L::NonSimpleNumField) -> Vector{NumFieldElem}

Returns the canonical basis of a non-simple extension $L/K$. If
$L = K(a_1,\dotsc,a_n)$ where each $a_i$ has degree $d_i$, then the basis will
be $a_1^{i_1}\dotsm a_d^{i_d}$ with $0 \leq i_j d_j - 1$ for $1 \leq j \leq n$.
"""
basis(::NonSimpleNumField)

################################################################################
#
#  Conversion to simple extension
#
################################################################################

@doc Markdown.doc"""
    simple_extension(L::NonSimpleNumField) -> SimpleNumField, Map

Given a non-simple extension $L/K$, this function computes a simple extension
$M/K$ and a $K$-linear isomorphism $M \to L$.
"""
simple_extension(::NonSimpleNumField)

################################################################################
#
#  Check consistency
#
################################################################################

# This is used for the check in the constructor
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

################################################################################
#
#  Component
#
################################################################################
@doc Markdown.doc"""
    component(L::NonSimpleNumField, i::Int) -> SimpleNumField, Map

Given a non-simple extension $L/K$, this function returns the simple number field 
corresponding to the $i$-th component of $L$ togheter with its embedding.
"""
function component(K::NonSimpleNumField, i::Int)
  fl, g = isunivariate(K.pol[i])
  gK = gens(K)
  @assert fl
  Ki, a = number_field(g, cached = false, check = false)
  mp = hom(Ki, K, gK[i])
  return Ki, mp
end