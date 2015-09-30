
abstract Mapping{S, T}

type NfToNfMor <: Mapping{nf_elem, nf_elem}
  domain::AnticNumberField
  codomain::AnticNumberField
  fun::Function
  inv::Function

  function NfToNfMor()
  end
end

type NfMaxOrdToFqNmodMor <: Mapping{NfOrderElem, fq_nmod}
  domain::NfMaximalOrder
  codomain::FqNmodFiniteField
  fun::Function
  inv::Function
  sec::Function # a section to fun

  function NfMaxOrdToFqNmodMor()
    z = new()
    return z
  end
end

type NfToFqNmodMor <: Mapping{nf_elem, fq_nmod}
  domain::AnticNumberField
  codomain::FqNmodFiniteField
  fun::Function
  inv::Function
  sec::Function # a section to fun

  function NfToFqNmodMor()
    z = new()
    return z
  end
end


function extend(f::NfMaxOrdToFqNmodMor, K::AnticNumberField)
  nf(domain(f)) != K && error("Number field is not the number field of the order")

  z = NfToFqNmodMor()
  z.domain = K
  z.codomain = f.codomain

  p = characteristic(z.codomain)
  Zx = PolynomialRing(ZZ, "x")[1]
  y = f(NfOrderElem(domain(f), gen(K)))

  function fun(x::nf_elem)
    g = parent(K.pol)(x)
    u = inv(z.codomain(den(g)))
    g = Zx(den(g)*g)
    return u*evaluate(g, y)
  end

  z.fun = fun
  return z
end
   
function Mor(O::NfMaximalOrder, F::FqNmodFiniteField, y::fq_nmod)
  z = NfMaxOrdToFqNmodMor()
  z.domain = O
  z.codomain = F
  p = characteristic(F)
  Zx = PolynomialRing(ZZ, "x")[1]

  function fun(x::NfOrderElem)
    g = parent(nf(O).pol)(elem_in_nf(x))
    u = inv(F(den(g)))
    g = Zx(den(g)*g)
    return u*evaluate(g, y)
  end

  z.fun = fun
  return z
end

function evaluate(f::fmpz_poly, r::fq_nmod)
  #Horner - stolen from Claus
  l = f.length-1
  s = coeff(f, l)
  for i =l-1:-1:0
    s = s*r + coeff(f, i)
  end
  return s
end                                           


function Mor(K::AnticNumberField, L::AnticNumberField, y::nf_elem)
  z = NfToNfMor()
  z.domain = K
  z.codomain = L

  function fun(x::nf_elem)
    g = parent(K.pol)(x)
    return evaluate(g, y)
  end

  z.fun = fun
  return z
end

function call{D, C}(f::Mapping{D, C}, x::D)
  parent(x) != domain(f) && error("Argument not in domain")
  return f.fun(x)::C
end

domain(f::Mapping) = f.domain

codomain(f::Mapping) = f.codomain

function show(io::IO, f::Mapping)
  println("Function from $(f.domain) to $(f.codomain)")
end

