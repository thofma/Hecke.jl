#TODO: create an interface using characters

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

abstract type AbelianExt end

mutable struct KummerExt <: AbelianExt
  zeta::nf_elem
  n::Int
  gen::Array{FacElem{nf_elem}, 1}

  AutG::GrpAbFinGen
  frob_cache::Dict{NfOrdIdl, GrpAbFinGenElem}

  function KummerExt()
    return new()
  end
end

function Base.show(io::IO, K::KummerExt)
  print(io, "KummerExt of exponent $(K.n) with $(length(K.gen)) generators")
end

function kummer_extension(n::Int, gen::Array{FacElem{nf_elem, AnticNumberField}, 1})
  K = KummerExt()
  k = base_ring(gen[1])
  L = maximal_order(k)
  zeta, o = torsion_units_gen_order(L)
  @assert o % n == 0

  K.zeta = k(zeta)^div(o, n)
  K.n = n
  K.gen = gen
  K.AutG = GrpAbFinGen(fmpz[n for i=gen])
  K.frob_cache = Dict{NfOrdIdl, GrpAbFinGenElem}()
  return K
end

mutable struct ClassField_pp
  mq::Map
  rayclassgroupmap::Map#MapRayClassGrp
  quotientmap::Map#GrpAbFinGenMap
  a::FacElem

  sup::Array{NfOrdIdl, 1} # the support of a - if known
  sup_known::Bool

  K::NfRel{nf_elem} # the target with the roots of unity
  A::NfRel{nf_elem} # the target
  o::Int # the degree of K - note, in general this is a divisor of the degree of A
  pe::NfRelElem{nf_elem}
  AutG::Array
  AutR::fmpz_mat
  bigK::KummerExt
  degree::Int # The degree of the relative extension we are searching for.
              # In other words, the order of the codomain of quotientmap

  function ClassField_pp()
    z = new()
    z.degree = -1
    return z
  end
end

function Base.show(io::IO, C::ClassField_pp)
  println(io, "Cyclic class field of degree $(order(codomain(C.quotientmap))) defined modulo $(defining_modulus(C))")
  if isdefined(C, :a)
    println(io, "Kummer generator ", C.a)
  end
  if isdefined(C, :K)
    println(io, "Kummer extension: ", C.K)
  end
  if isdefined(C, :A)
    println(io, "Defining  polynomial ", C.A.pol)
  end
end


mutable struct ClassField
  mq::Map
  rayclassgroupmap::Map
  quotientmap::Map#GrpAbFinGenMap

  conductor::Tuple{NfOrdIdl, Array{InfPlc, 1}}
  relative_discriminant::Dict{NfOrdIdl, Int}
  absolute_discriminant::Dict{fmpz,Int}
  cyc::Array{ClassField_pp, 1}
  A::NfRel_ns{nf_elem}
  degree::Int # The degree of the relative extension we are searching for.
              # In other words, the order of the codomain of quotientmap

  function ClassField()
    z = new()
    z.degree = -1
    return z
  end
end

function Base.show(io::IO, CF::ClassField)
  println("Class field defined mod $(defining_modulus(CF)) of structure $(codomain(CF.quotientmap)))")
end
