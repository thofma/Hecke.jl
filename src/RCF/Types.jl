#TODO: create an interface using characters

type BadPrime <: Exception
  p
end

function Base.show(io::IO, E::BadPrime)
  if isdefined(E, :p)
    println("Bad prime $(E.p) encountered")
  else
    println("Unknown bad prime encountered")
  end
end

abstract AbelianExt

type KummerExt <: AbelianExt
  zeta::nf_elem
  n::Int
  gen::Array{FacElem{nf_elem}, 1}

  AutG::Hecke.GrpAbFinGen

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
  zeta, o = Hecke.torsion_units_gen_order(L)
  @assert o % n == 0

  K.zeta = k(zeta)^div(o, n)
  K.n = n
  K.gen = gen
  K.AutG = Hecke.GrpAbFinGen(fmpz[n for i=gen])
  return K
end

type ClassField_pp
  mq::Map
  a::FacElem
  K::Hecke.NfRel{nf_elem} # the target with the roots of unity
  A::Hecke.NfRel{nf_elem} # the target
  AutG::Array
  AutR::fmpz_mat

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


type ClassField
  mq::Map
  cyc::Array{ClassField_pp, 1}
  function ClassField()
    return new()
  end
end

function Base.show(io::IO, CF::ClassField)
  println("Class field defined mod $(_modulus(CF.mq)) of structure $(snf(domain(CF.mq)))")
end


