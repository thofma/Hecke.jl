
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

type NfMaxOrdToFqNmodMor <: Map{NfMaxOrd, FqNmodFiniteField}
  header::MapHeader{NfMaxOrd, FqNmodFiniteField}
  poly_of_the_field::nmod_poly

  function NfMaxOrdToFqNmodMor()
    r = new()
    r.header = MapHeader{NfMaxOrd, FqNmodFiniteField}()
    return r
  end

  function NfMaxOrdToFqNmodMor(O::NfMaxOrd, F::FqNmodFiniteField, g::nmod_poly)
    # assume that F = F_p[X]/(g) and g is a factor of f mod p

    z = new()
    p = characteristic(F)
    a = gen(nf(O))
    tmp_nmod_poly = parent(g)()

    z.poly_of_the_field = g
    
    function _image(x::NfOrdElem)
      u = F()
      gg = parent(nf(O).pol)(elem_in_nf(x))::fmpq_poly
      fmpq_poly_to_nmod_poly_raw!(tmp_nmod_poly, gg)
      ccall((:fq_nmod_set, :libflint), Void, (Ptr{fq_nmod}, Ptr{nmod_poly}, Ptr{FqNmodFiniteField}), &u, &tmp_nmod_poly, &F)
      ccall((:fq_nmod_reduce, :libflint), Void, (Ptr{fq_nmod}, Ptr{FqNmodFiniteField}), &u, &F)
      return u
    end

    function _preimage(x::fq_nmod)
      zz = nf(O)()

      for i in 0:degree(F)-1
        zz = zz + _get_coeff_raw(x, i)*a^i
      end

      return O(zz, false)
    end

    z.header = MapHeader{NfMaxOrd, FqNmodFiniteField}(O, F, _image, _preimage)

    return z
  end
  
  function NfMaxOrdToFqNmodMor(O::NfMaxOrd, F::FqNmodFiniteField, y::fq_nmod)
    z = new()

    p = characteristic(F)
    Zx = PolynomialRing(FlintIntegerRing(), "x")[1]
    a = gen(nf(O))
    h = Zx()
    t_fq_nmod = F()
    tt_fq_nmod = F()
    t_fmpz = fmpz()

    function _image(x::NfOrdElem)
      g = parent(nf(O).pol)(elem_in_nf(x))

      #pseudocode:
      #u = inv(F(den(g)))
      #return u*evaluate(num(g), y)

      ccall((:fmpq_poly_get_denominator, :libflint), Void,
            (Ptr{fmpz}, Ptr{fmpq_poly}), &t_fmpz, &g)
      
      ccall((:fq_nmod_set_fmpz, :libflint), Void, 
            (Ptr{fq_nmod}, Ptr{fmpz}, Ptr{FqNmodFiniteField}),
            &tt_fq_nmod, &t_fmpz, &F)

      ccall((:fq_nmod_inv, :libflint), Void,
            (Ptr{fq_nmod}, Ptr{fq_nmod}, Ptr{FqNmodFiniteField}),
            &tt_fq_nmod, &tt_fq_nmod, &F)

      ccall((:fmpq_poly_get_numerator, :libflint), Void,
                  (Ptr{fmpz_poly}, Ptr{fmpq_poly}), &h, &g)

      evaluate!(t_fq_nmod, h, y)
      #@assert t_fq_nmod == evaluate(h, y)
      return tt_fq_nmod * t_fq_nmod 
    end

    function _preimage(x::fq_nmod)
      z = nf(O)()

      for i in 0:degree(F)-1
        z = z + _get_coeff_raw(x, i)*a^i
      end

      return O(z, false)
    end

    z.header = MapHeader{NfMaxOrd, FqNmodFiniteField}(O, F, _image, _preimage)

    return z
  end
end

type NfMaxOrdQuoMap <: Map{NfMaxOrd, NfMaxOrdQuoRing}
  header::MapHeader{NfMaxOrd, NfMaxOrdQuoRing}

  function NfMaxOrdQuoMap(O::NfMaxOrd, Q::NfMaxOrdQuoRing)
    z = new()
    
    _image = function (x::NfOrdElem)
      return Q(x)
    end

    _preimage = function (x::NfMaxOrdQuoRingElem)
      return x.elem
    end

    z.header = MapHeader(O, Q, _image, _preimage)
    return z
  end
end

function Mor(O::NfMaxOrd, F::FqNmodFiniteField, y::fq_nmod)
  return NfMaxOrdToFqNmodMor(O, F, y)
end

function Mor(O::NfMaxOrd, F::FqNmodFiniteField, h::nmod_poly)
  return NfMaxOrdToFqNmodMor(O, F, h)
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
  Zx = PolynomialRing(FlintIntegerRing(), "x")[1]
  y = f(NfOrdElem{NfMaxOrd}(domain(f), gen(K)))

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
  s = parent(r)(coeff(f, l))
  for i =l-1:-1:0
    s = s*r + parent(r)(coeff(f, i))
  end
  return s
end                                           

function evaluate!(z::fq_nmod, f::fmpz_poly, r::fq_nmod)
  #Horner - stolen from Claus

  zero!(z)

  if length(f) == 0
    return z
  end

  l = f.length-1
  set!(z, parent(r)(coeff(f, l)))
  #s = parent(r)(coeff(f, l))
  for i =l-1:-1:0
    mul!(z, z, r)
    add!(z, z, parent(r)(coeff(f, i)))
    #s = s*r + parent(r)(coeff(f, i))
  end
  return z
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
  t = FlintIntegerRing()
  ccall((:fmpz_poly_get_coeff_fmpz, :libflint), Void, (Ptr{fmpz}, Ptr{fq}, Int), &t, &x, i)
  return t
end

function call(f::NfMaxOrdToFqNmodMor, p::PolyElem{NfOrdElem})
  F = codomain(f)
  Fx,_ = PolynomialRing(F, "_\$")

  ar = NfOrdElem[ coeff(p, i) for i in 0:degree(p) ]

  z = Fx(map(f, ar))

  return z
end

# this is super slow
# improve
function call(f::NfMaxOrdQuoMap, I::NfMaxOrdIdl)
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


function call(f::NfMaxOrdQuoMap, p::PolyElem{NfOrdElem})
  F = codomain(f)
  Fx,_ = PolynomialRing(F, "_\$")

  ar = NfOrdElem[ coeff(p, i) for i in 0:degree(p) ]

  z = Fx(map(f, ar))

  return z
end

base_ring(::NfMaxOrd) = Union{}

Nemo.needs_parentheses(::NfOrdElem) = true

Nemo.is_negative(::NfOrdElem) = false

