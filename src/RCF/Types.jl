export ClassField

abstract type AbelianExt end

struct ExtendAutoError <: Exception end

mutable struct KummerExt <: AbelianExt
  zeta::nf_elem
  n::Int
  gen::Vector{FacElem{nf_elem, AnticNumberField}}

  AutG::GrpAbFinGen
  frob_cache::Dict{NfOrdIdl, GrpAbFinGenElem}
  frob_gens::Tuple{Vector{NfOrdIdl}, Vector{GrpAbFinGenElem}}
  gen_mod_nth_power::Vector{FacElem{nf_elem, AnticNumberField}}
  eval_mod_nth::Vector{nf_elem}

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
  a::FacElem{nf_elem, AnticNumberField}#Generator of the Kummer Extension

  sup::Vector{NfOrdIdl} # the support of a - if known
  sup_known::Bool

  factored_conductor::Dict{NfOrdIdl, Int}

  K::NfRel{nf_elem} # the target with the roots of unity
  A::NfRel{nf_elem} # the target
  o::Int # the degree of K - note, in general this is a divisor of the degree of A
  defect::Int # div(degree(A), degree(K)) = div(degree(A), o)
  pe::NfRelElem{nf_elem} #The image of the generator of A in K
  AutG::Vector{NfRelToNfRelMor_nf_elem_nf_elem}
  AutR::fmpz_mat
  bigK::KummerExt
  h::GrpAbFinGenMap #The Artin Map provided by the function build_map
  degree::Int # The degree of the relative extension we are searching for.
              # In other words, the order of the codomain of quotientmap

  function ClassField_pp{S, T}() where {S, T}
    z = new{S, T}()
    z.degree = -1
    return z
  end
end

@attributes mutable struct ClassField{S, T} <: AbelianExt
  rayclassgroupmap::S#Union{MapRayClassGrp{GrpAbFinGen}, MapClassGrp{GrpAbFinGen}}
  quotientmap::T#GrpAbFinGenMap

  factored_conductor::Dict{NfOrdIdl, Int}
  conductor::Tuple{NfOrdIdl, Vector{InfPlc}}
  relative_discriminant::Dict{NfOrdIdl, Int}
  absolute_discriminant::Dict{fmpz,Int}
  cyc::Vector{ClassField_pp{S, T}}
  A::NfRelNS{nf_elem}
  AbsAutGrpA::Vector{NfRelNSToNfRelNSMor_nf_elem} #The generators for the absolute automorphism
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
  x::GrpAbFinGenElem
  mGhat::Map
  factored_conductor::Dict{NfOrdIdl, Int}
  conductor::NfOrdIdl
  conductor_inf_plc::Vector{InfPlc}
  mrcond::Union{MapClassGrp, MapRayClassGrp}
  mp_cond::GrpAbFinGenMap
  charcond::Map #Character directly on the rcf given by the conductor

  function RCFCharacter(C::ClassField{S, T}, x::GrpAbFinGenElem, mGhat::Map) where {S, T}
    z = new{S, T}()
    z.C = C
    z.x = x
    z.mGhat = mGhat
    return z
  end
end
