
type NfToNfMor <: Map{AnticNumberField, AnticNumberField}
  header::MapHeader{AnticNumberField, AnticNumberField}
  prim_img::nf_elem

  function NfToNfMor()
    z = new()
    z.header = MapHeader()
    return r
  end
  
  function NfToNfMor(K::AnticNumberField, L::AnticNumberField, y::nf_elem)
    z = new()
    z.prim_img = y

    function image(x::nf_elem)
      g = parent(K.pol)(x)
      return evaluate(g, y)
    end

    z.header = MapHeader(K, L, image)
    return z
  end
end

type NfMaxOrdToFqNmodMor <: Map{NfMaximalOrder, FqNmodFiniteField}
  header::MapHeader{NfMaximalOrder, FqNmodFiniteField}

  function NfMaxOrdToFqNmodMor()
    r = new()
    r.header = MapHeader()
    return r
  end
  
  function NfMaxOrdToFqNmodMor(O::NfMaximalOrder, F::FqNmodFiniteField, y::fq_nmod)
    z = new()

    p = characteristic(F)
    Zx = PolynomialRing(ZZ, "x")[1]

    function _image(x::NfOrderElem)
      g = parent(nf(O).pol)(elem_in_nf(x))
      u = inv(F(den(g)))
      g = Zx(den(g)*g)
      return u*evaluate(g, y)
    end

    z.header = MapHeader{NfMaximalOrder, FqNmodFiniteField}(O, F, _image)

    return z
  end
end

function Mor(O::NfMaximalOrder, F::FqNmodFiniteField, y::fq_nmod)
  return NfMaxOrdToFqNmodMor(O, F, y)
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
  z = NfToNfMor(K, L, y)
  return z
end
