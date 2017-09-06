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
  a::FacElem
  K::NfRel{nf_elem} # the target with the roots of unity
  A::NfRel{nf_elem} # the target
  pe::NfRelElem{nf_elem}
  AutG::Array
  AutR::fmpz_mat
  bigK::KummerExt

  function ClassField_pp()
    return new()
  end
end

function Base.show(io::IO, C::ClassField_pp)
  println(io, "Cyclic class field of degree $(order(domain(C.mq))) defined modulo $(_modulus(C.mq))")
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
  cyc::Array{ClassField_pp, 1}
  function ClassField()
    return new()
  end
end

function Base.show(io::IO, CF::ClassField)
  println("Class field defined mod $(_modulus(CF.mq)) of structure $(snf(domain(CF.mq)))")
end


