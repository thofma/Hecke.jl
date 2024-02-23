abstract type AbelianExt end

struct ExtendAutoError <: Exception end

mutable struct KummerExt <: AbelianExt
  zeta::AbsSimpleNumFieldElem
  n::Int
  gen::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}

  AutG::FinGenAbGroup
  frob_cache::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, FinGenAbGroupElem}
  frob_gens::Tuple{Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}, Vector{FinGenAbGroupElem}}
  gen_mod_nth_power::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}
  eval_mod_nth::Vector{AbsSimpleNumFieldElem}

  function KummerExt()
    return new()
  end
end


mutable struct BadPrime <: Exception
  p
end

function Base.show(io::IO, E::BadPrime)
  if isdefined(E, :p)
    println("Bad prime $(E.p) encountered")
  else
    println("Unknown bad prime encountered")
  end
end

mutable struct ClassField_pp{S, T}
  rayclassgroupmap::S
  quotientmap::T
  a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}#Generator of the Kummer Extension

  sup::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}} # the support of a - if known
  sup_known::Bool

  factored_conductor::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}

  K::RelSimpleNumField{AbsSimpleNumFieldElem} # the target with the roots of unity
  A::RelSimpleNumField{AbsSimpleNumFieldElem} # the target
  o::Int # the degree of K - note, in general this is a divisor of the degree of A
  defect::Int # div(degree(A), degree(K)) = div(degree(A), o)
  pe::RelSimpleNumFieldElem{AbsSimpleNumFieldElem} #The image of the generator of A in K
  AutG::Vector{NumFieldHom{RelSimpleNumField{AbsSimpleNumFieldElem}, RelSimpleNumField{AbsSimpleNumFieldElem}}}
  AutR::ZZMatrix
  bigK::KummerExt
  h::FinGenAbGroupHom #The Artin Map provided by the function build_map
  degree::Int # The degree of the relative extension we are searching for.
              # In other words, the order of the codomain of quotientmap

  function ClassField_pp{S, T}() where {S, T}
    z = new{S, T}()
    z.degree = -1
    return z
  end
end

@attributes mutable struct ClassField{S, T} <: AbelianExt
  rayclassgroupmap::S#Union{MapRayClassGrp{FinGenAbGroup}, MapClassGrp{FinGenAbGroup}}
  quotientmap::T#FinGenAbGroupHom

  factored_conductor::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}
  conductor::Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Vector{InfPlc{AbsSimpleNumField, AbsSimpleNumFieldEmbedding}}}
  relative_discriminant::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}
  absolute_discriminant::Dict{ZZRingElem,Int}
  cyc::Vector{ClassField_pp{S, T}}
  A::RelNonSimpleNumField{AbsSimpleNumFieldElem}
  AbsAutGrpA::Vector{NumFieldHom{RelNonSimpleNumField{AbsSimpleNumFieldElem}, RelNonSimpleNumField{AbsSimpleNumFieldElem}}} #The generators for the absolute automorphism
                                                     #group of A
  degree::Int # The degree of the relative extension we are searching for.
              # In other words, the order of the codomain of quotientmap

  function ClassField{S, T}() where {S, T}
    z = new{S, T}()
    z.degree = -1
    return z
  end
end

mutable struct RCFCharacter{S, T}
  C::ClassField{S, T}
  x::FinGenAbGroupElem
  mGhat::Map
  factored_conductor::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}
  conductor::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}
  conductor_inf_plc::Vector{InfPlc{AbsSimpleNumField, AbsSimpleNumFieldEmbedding}}
  mrcond::Union{MapClassGrp, MapRayClassGrp}
  mp_cond::FinGenAbGroupHom
  charcond::Map #Character directly on the rcf given by the conductor

  function RCFCharacter(C::ClassField{S, T}, x::FinGenAbGroupElem, mGhat::Map) where {S, T}
    z = new{S, T}()
    z.C = C
    z.x = x
    z.mGhat = mGhat
    return z
  end
end
