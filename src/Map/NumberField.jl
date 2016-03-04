
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
    r.header = MapHeader{NfMaximalOrder, FqNmodFiniteField}()
    return r
  end
  
  function NfMaxOrdToFqNmodMor(O::NfMaximalOrder, F::FqNmodFiniteField, y::fq_nmod)
    z = new()

    p = characteristic(F)
    Zx = PolynomialRing(ZZ, "x")[1]
    a = gen(nf(O))

    function _image(x::NfOrderElem)
      g = parent(nf(O).pol)(elem_in_nf(x))
      u = inv(F(den(g)))
      g = Zx(den(g)*g)
      return u*evaluate(g, y)
    end

    function _preimage(x::fq_nmod)
      z = nf(O)()

      for i in 0:degree(F)-1
        z = z + _get_coeff_raw(x, i)*a^i
      end

      return O(z, false)
    end

    z.header = MapHeader{NfMaximalOrder, FqNmodFiniteField}(O, F, _image, _preimage)

    return z
  end
end

type NfMaxOrdQuoMap <: Map{NfMaximalOrder, NfMaxOrdQuoRing}
  header::MapHeader{NfMaximalOrder, NfMaxOrdQuoRing}

  function NfMaxOrdQuoMap(O::NfMaximalOrder, Q::NfMaxOrdQuoRing)
    z = new()
    
    _image = function (x::NfOrderElem)
      return Q(x)
    end

    _preimage = function (x::NfMaxOrdQuoRingElem)
      return x.elem
    end

    z.header = MapHeader(O, Q, _image, _preimage)
    return z
  end
end

function Mor(O::NfMaximalOrder, F::FqNmodFiniteField, y::fq_nmod)
  return NfMaxOrdToFqNmodMor(O, F, y)
end

type NfToFqNmodMor <: Map{AnticNumberField, FqNmodFiniteField}
  header::MapHeader

  function NfToFqNmodMor()
    r = new()
    r.header = MapHeader{AnticNumberField, FqNmodFiniteField}()
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
  y = f(NfOrderElem{NfMaximalOrder}(domain(f), gen(K)))

  function _image(x::nf_elem)
    g = parent(K.pol)(x)
    u = inv(z.header.codomain(den(g)))
    g = Zx(den(g)*g)
    return u*evaluate(g, y)
  end

  z.header.image = _image
  return z
end
   

function evaluate(f::fmpz_poly, r::fq_nmod)
  #Horner - stolen from Claus

  if length(f) == 0
    return parent(r)()
  end

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

function _get_coeff_raw(x::fq_nmod, i::Int)
  u = ccall((:nmod_poly_get_coeff_ui, :libflint), UInt, (Ptr{fq_nmod}, Int), &x, i)
  return u
end

function _get_coeff_raw(x::fq, i::Int)
  t = ZZ()
  ccall((:fmpz_poly_get_coeff_fmpz, :libflint), Void, (Ptr{fmpz}, Ptr{fq}, Int), &t, &x, i)
  return t
end

function call(f::NfMaxOrdToFqNmodMor, p::Poly{NfOrderElem})
  F = codomain(f)
  Fx,_ = PolynomialRing(F, "_\$")

  ar = NfOrderElem[ coeff(p, i) for i in 0:degree(p) ]

  z = Fx(map(f, ar))

  return z
end

function call(f::NfMaxOrdQuoMap, I::NfMaximalOrderIdeal)
  O = domain(f)
  Q = codomain(f)
  B = Q.ideal + I
  b = basis(B)

  z = O()

  while true
    z = rand(fmpz(1):norm(Q.ideal)^2) * b[1]

    for i in 2:degree(O)
      z = z + rand(fmpz(1):norm(Q.ideal)^2) * b[i]
    end

    if norm(ideal(O, z) + ideal(O, O(norm(Q.ideal)))) == norm(B)
      break
    end
  end

  return Q(z)
end


function call(f::NfMaxOrdQuoMap, p::Poly{NfOrderElem})
  F = codomain(f)
  Fx,_ = PolynomialRing(F, "_\$")

  ar = NfOrderElem[ coeff(p, i) for i in 0:degree(p) ]

  z = Fx(map(f, ar))

  return z
end

base_ring(::NfMaximalOrder) = Union{}

Nemo.needs_parentheses(::NfOrderElem) = true

Nemo.is_negative(::NfOrderElem) = false

