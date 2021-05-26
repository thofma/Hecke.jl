################################################################################
#
#  Localization of K[1/x] at (1/x), i.e. k_\infty(x) \subseteq k(x)
#
#
#  (C) 2021 William Hart
#
################################################################################

################################################################################
#
#  Declaration types
#  KInftyRing / KInftyElem 
#
################################################################################

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

################################################################################
#
#  Parent call overloading
#
################################################################################

(R::KInftyRing)() = R(function_field(R)())

function (R::KInftyRing{T})(a::Generic.Rat{T}) where T <: FieldElement
   degree(numerator(a, false)) > degree(denominator(a, false)) &&
                                           error("Not an element of k_infty(x)")
   return KInftyElem{T}(a, R)
end

(R::KInftyRing)(a::RingElement) = R(function_field(R)(a))

function (R::KInftyRing{T})(a::KInftyElem{T}) where T <: FieldElement
  parent(a) != R && error("Cannot coerce element")
  return a
end

################################################################################
#
#  Constructors
#
################################################################################

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


