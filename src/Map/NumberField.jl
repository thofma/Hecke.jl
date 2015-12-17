

type NfToNfMor <: Map
  header::MapHeader

  function NfToNfMor()
    r = new()
    r.header = MapHeader()
    return r
  end
end

type NfMaxOrdToFqNmodMor <: Map
  header::MapHeader
  sec::Function # a section to fun

  function NfMaxOrdToFqNmodMor()
    r = new()
    r.header = MapHeader()
    return r
  end
end

type NfToFqNmodMor <: Map
  header::MapHeader
  sec::Function # a section to fun

  function NfToFqNmodMor()
    r = new()
    r.header = MapHeader()
    return r
  end
end


function extend(f::NfMaxOrdToFqNmodMor, K::AnticNumberField)
  nf(domain(f)) != K && error("Number field is not the number field of the order")

  z = NfToFqNmodMor()
  z.header.domain = K
  z.header.codomain = f.header.codomain

  p = characteristic(z.header.codomain)
  Zx = PolynomialRing(ZZ, "x")[1]
  y = f(NfOrderElem(domain(f), gen(K)))

  function fun(M::Map, x::nf_elem)
    g = parent(K.pol)(x)
    u = inv(z.header.codomain(den(g)))
    g = Zx(den(g)*g)
    return u*evaluate(g, y)
  end

  z.header.image = fun
  return z
end
   
function Mor(O::NfMaximalOrder, F::FqNmodFiniteField, y::fq_nmod)
  z = NfMaxOrdToFqNmodMor()
  z.header.domain = O
  z.header.codomain = F
  p = characteristic(F)
  Zx = PolynomialRing(ZZ, "x")[1]

  function fun(M::Map, x::NfOrderElem)
    g = parent(nf(O).pol)(elem_in_nf(x))
    u = inv(F(den(g)))
    g = Zx(den(g)*g)
    return u*evaluate(g, y)
  end

  z.header.image = fun
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
  z.header.domain = K
  z.header.codomain = L

  function fun(M::Map, x::nf_elem)
    g = parent(K.pol)(x)
    return evaluate(g, y)
  end

  z.header.image = fun
  return z
end
