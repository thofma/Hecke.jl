export Mor, domain

abstract Mapping{S, T}

type NfToNfMor <: Mapping{nf_elem, nf_elem}
  domain::NfNumberField
  codomain::NfNumberField
  fun::Function
  inv::Function

  function NfToNfMor()
    z = new()
    return z
  end
end

type NfToFqNmodMor <: Mapping{NfOrderElem, fq_nmod}
  domain::NfMaximalOrder
  codomain::FqNmodFiniteField
  fun::Function
  inv::Function
  sec::Function # a section to fun

  function NfToFqNmodMor()
    z = new()
    return z
  end
end

function Mor(O::NfMaximalOrder, F::FqNmodFiniteField, y::fq_nmod)
  z = NfToFqNmodMor()
  z.domain = O
  z.codomain = F
  p = characteristic(F)
  Zx = PolynomialRing(ZZ, "x")[1]

  function fun(x::NfOrderElem)
    g = parent(nf(O).pol)(elem_in_nf(x))
    u = inv(F(denominator(g)))
    g = Zx(denominator(g)*g)
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


function Mor(K::NfNumberField, L::NfNumberField, y::nf_elem)
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
  return f.fun(x)
end
  
function call(f::NfToNfMor, x::nf_elem)
  parent(x) != domain(f) && error("Argument not in domain")
  return f.fun(x)
end

domain(f::Mapping) = f.domain
