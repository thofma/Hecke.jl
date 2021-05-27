###############################################################################
#
#  Localization of K[1/x] at (1/x), i.e. k_\infty(x) \subseteq k(x)
#
#
#  (C) 2021 William Hart
#
###############################################################################

###############################################################################
#
#  Declaration types
#  KInftyRing / KInftyElem 
#
###############################################################################

mutable struct KInftyRing{T <: FieldElement} <: Hecke.Ring
   K::Generic.RationalFunctionField{T}

   function KInftyRing{T}(K::Generic.RationalFunctionField{T}, cached::Bool) where T <: FieldElement
      return AbstractAlgebra.get_cached!(KInftyID, K, cached) do
         new{T}(K)
      end::KInftyRing{T}
   end
end

const KInftyID = Dict{Generic.RationalFunctionField, Hecke.Ring}()

mutable struct KInftyElem{T <: FieldElement} <: Hecke.RingElem
   d::Generic.Rat{T}
   parent::KInftyRing{T}
end

###############################################################################
#
#   Data type and parent object methods
#
###############################################################################

elem_type(::Type{KInftyRing{T}}) where T <: FieldElement = KInftyElem{T}

parent_type(::Type{KInftyElem{T}}) where T <: FieldElement = KInftyRing{T}

function function_field(R::KInftyRing{T}) where T <: FieldElement
   return R.K::Generic.RationalFunctionField{T}
end

parent(a::KInftyElem{T}) where T <: FieldElement = a.parent

function check_parent(a::KInftyElem{T}, b::KInftyElem{T})  where T <: FieldElement
   parent(a) != parent(b) && error("Parent objects do not match")
end

###############################################################################
#
#   Basic manipulation
#
###############################################################################

data(a::KInftyElem{T}) where T <: FieldElement = a.d::Generic.Rat{T}

function numerator(a::KInftyElem{T}, canonicalise::Bool=true) where T <: FieldElement
   return numerator(data(a), canonicalise)
end

function denominator(a::KInftyElem{T}, canonicalise::Bool=true) where T <: FieldElement
   return denominator(data(a), canonicalise)
end

degree(a::KInftyElem) = degree(numerator(a, false)) - degree(denominator(a, false))

zero(K::KInftyRing{T}) where T <: FieldElement = K(0)

one(K::KInftyRing{T}) where T <: FieldElement = K(1)

iszero(a::KInftyElem{T}) where T <: FieldElement = iszero(data(a))

isone(a::KInftyElem{T}) where T <: FieldElement = isone(data(a))

function isunit(a::KInftyElem{T}) where T <: FieldElement
   return degree(numerator(data(a), false)) ==
                                            degree(denominator(data(a), false))
end

function in(a::Generic.Rat{T}, R::KInftyRing{T}) where T <: FieldElement
   if parent(a) != function_field(R)
      return false
   end
   return degree(numerator(a, false)) <= degree(denominator(a, false))
end

function deepcopy_internal(a::KInftyElem{T}, dict::IdDict) where T <: FieldElement
   parent(a)(deepcopy(data(a)))
end

###############################################################################
#
#   AbstractString I/O
#
###############################################################################

function AbstractAlgebra.expressify(a::KInftyElem; context = nothing)
   return AbstractAlgebra.expressify(data(a), context = context)
end

function show(io::IO, a::KInftyElem)
   print(io, AbstractAlgebra.obj_to_string(a, context = io))
end

function show(io::IO, R::KInftyRing)
   print(io, "Degree localization of ", function_field(R))
end

###############################################################################
#
#   Unary operations
#
###############################################################################

function -(a::KInftyElem{T}) where T <: FieldElement
   parent(a)(-data(a), false)
end

###############################################################################
#
#   Binary operators
#
###############################################################################

function +(a::KInftyElem{T}, b::KInftyElem{T})  where T <: FieldElement
   check_parent(a, b)
   return parent(a)(data(a) + data(b), false)
end

function -(a::KInftyElem{T}, b::KInftyElem{T})  where T <: FieldElement
   check_parent(a, b)
   return parent(a)(data(a) - data(b), false)
end

function *(a::KInftyElem{T}, b::KInftyElem{T})  where T <: FieldElement
   check_parent(a, b)
   return parent(a)(data(a)*data(b), false)
end

###############################################################################
#
#   Comparison
#
###############################################################################

function ==(a::KInftyElem{T}, b::KInftyElem{T}) where T <: FieldElement
   check_parent(a, b)
   return data(a) == data(b)
end

###############################################################################
#
#  Inversion
#
###############################################################################

@doc Markdown.doc"""
     inv(a::KInftyElem{T}, checked::Bool = true)  where T <: FieldElem
Returns the inverse element of $a$ if $a$ is a unit.
If 'checked = false' the invertibility of $a$ is not checked and the
corresponding inverse element of the rational function field is returned.
"""
function inv(a::KInftyElem{T}, checked::Bool = true)  where T <: FieldElement
   b = inv(data(a))
   return parent(a)(b, checked)
end

###############################################################################
#
#  Exact division
#
###############################################################################

@doc Markdown.doc"""
     divides(a::KInftyElem{T}, b::KInftyElem{T}, checked::Bool = true) where T <: FieldElement

Returns tuple `(flag, c)` where `flag = true` if $b$ divides $a$ and $a = bc$,
otherwise `flag = false` and $c = 0$.
If `checked = false` the corresponding element of the rational function field
is returned and it is not checked whether it is an element of the given
localization.
"""
function divides(a::KInftyElem{T}, b::KInftyElem{T}, checked::Bool = true) where T <: FieldElement
   check_parent(a, b)
   if checked && degree(a) > degree(b)
      return false, parent(a)()
   else
      elem = divexact(data(a), data(b))
      return true, parent(a)(elem, false)
   end
end

@doc Markdown.doc"""
     divexact(a::KInftyElem{T}, b::KInftyElem{T}, checked::Bool = true)  where {T <: nf_elem}
Returns element 'c' of given localization such that $a = bc$ if such element
exists. If `checked = false` the corresponding element of the rational function
field is returned and it is not checked whether it is an element of the given
localization.
"""
function divexact(a::KInftyElem{T}, b::KInftyElem{T}, checked::Bool = true)  where T <: FieldElement
   d = divides(a, b, checked)
   d[1] ? d[2] : error("$a not divisible by $b in the given localization")
end

###############################################################################
#
#  Euclidean division
#
###############################################################################

function div(a::KInftyElem{T}, b::KInftyElem{T}, checked::Bool=true) where T <: FieldElement
   check_parent(a, b)
   iszero(b) && throw(DivideError())
   if degree(a) > degree(b)
      return parent(a)()
   else
      return divexact(a, b, false)
   end
end

function divrem(a::KInftyElem{T}, b::KInftyElem{T}, checked::Bool=true) where T <: FieldElement
  check_parent(a, b)
   iszero(b) && throw(DivideError())
   if degree(a) > degree(b)
      return parent(a)(), deepcopy(a)
   else
      return divexact(a, b, false), parent(a)()
   end
end

function mod(a::KInftyElem{T}, b::KInftyElem{T}, checked::Bool=true) where T <: FieldElement
   check_parent(a, b)
   iszero(b) && throw(DivideError())
   if degree(a) > degree(b)
      return deepcopy(a)
   else
      return parent(a)()
   end
end 

###############################################################################
#
#  GCD
#
###############################################################################

function gcd(a::KInftyElem{T}, b::KInftyElem{T}, checked::Bool=true) where T <: FieldElement
   check_parent(a, b)
   if degree(a) <= degree(b)
      return b
   else
      return a
   end
end

###############################################################################
#
#  GCDX
#
###############################################################################

function gcdx(a::KInftyElem{T}, b::KInftyElem{T}, checked::Bool=true) where T <: FieldElement
   check_parent(a, b)
   K = parent(a)
   if degree(a) <= degree(b)
      return b, zero(K), one(K)
   else
      return a, one(K), zero(K)
   end
end

###############################################################################
#
#  Parent call overloading
#
###############################################################################

(R::KInftyRing)() = R(function_field(R)())

function (R::KInftyRing{T})(a::Generic.Rat{T}, checked::Bool=true) where T <: FieldElement
   checked && degree(numerator(a, false)) > degree(denominator(a, false)) &&
                                           error("Not an element of k_infty(x)")
   return KInftyElem{T}(a, R)
end

(R::KInftyRing)(a::RingElement) = R(function_field(R)(a), false)

function (R::KInftyRing{T})(a::KInftyElem{T}) where T <: FieldElement
   parent(a) != R && error("Cannot coerce element")
   return a
end

###############################################################################
#
#  Constructors
#
###############################################################################

@doc Markdown.doc"""
    Localization(K::RationalFunctionField{T}, ::typeof(degree)) where T <: FieldElem

Return the localization of $k[1/x]$ at $(1/x)$ inside the rational function
field $k(x)$, i.e. the localization of the function field at the point at
infinity, i.e. the valuation ring for valuation -degree(x). This is the ring
$k_\infty(x) = \{ f/g | \deg(f) \leq \deg(g)\}$.
"""
function Localization(K::Generic.RationalFunctionField{T}, ::typeof(degree); cached::Bool=true) where T <: FieldElement
   return KInftyRing{T}(K, cached)
end


