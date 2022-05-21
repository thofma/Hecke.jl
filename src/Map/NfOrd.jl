################################################################################
#
#  Ringmorphisms of orders onto finite fields
#
################################################################################

# NfOrd -> FqNmod
mutable struct NfOrdToFqNmodMor <: Map{NfOrd, FqNmodFiniteField, HeckeMap, NfOrdToFqNmodMor}
  header::MapHeader{NfOrd, FqNmodFiniteField}
  poly_of_the_field::gfp_poly
  P::NfOrdIdl
  powers::Vector{nf_elem}

  function NfOrdToFqNmodMor()
    r = new()
    r.header = MapHeader{NfOrd, FqNmodFiniteField}()
    return r
  end

  function NfOrdToFqNmodMor(O::NfOrd, F::FqNmodFiniteField, g::gfp_poly)
    # assume that F = F_p[X]/(g) and g is a factor of f mod p

    z = new()
    d = degree(nf(O))
    p = characteristic(F)
    a = gen(nf(O))
    tmp_gfp_poly = parent(g)()
    z.poly_of_the_field = g

    powers = Vector{nf_elem}(undef, d)

    powers[1] = a
    for i in 2:d
      powers[i] = powers[i - 1] * a
    end
    z.powers = powers

    function _image(x::NfOrdElem)
      u = F()
      gg = parent(nf(O).pol)(elem_in_nf(x))::fmpq_poly
      fmpq_poly_to_gfp_poly_raw!(tmp_gfp_poly, gg)
      ccall((:nmod_poly_rem, libflint), Nothing,
            (Ref{gfp_poly}, Ref{gfp_poly}, Ref{gfp_poly}, Ptr{Nothing}),
            tmp_gfp_poly, tmp_gfp_poly, g, pointer_from_objref(F)+sizeof(fmpz))
      ccall((:fq_nmod_set, libflint), Nothing,
            (Ref{fq_nmod}, Ref{gfp_poly}, Ref{FqNmodFiniteField}),
            u, tmp_gfp_poly, F)
      ccall((:fq_nmod_reduce, libflint), Nothing,
            (Ref{fq_nmod}, Ref{FqNmodFiniteField}), u, F)
      return u
    end

    # The lift is even simpler!
    function _preimage(y::fq_nmod)
      zz = O()
      zz.elem_in_nf = nf(O)(coeff(y, 0))
      for i in 2:d
        add!(zz.elem_in_nf, zz.elem_in_nf, powers[i - 1] * coeff(y, i - 1))
      end
      zz.elem_in_nf = mod(zz.elem_in_nf, p)
      return zz
    end

    z.header = MapHeader{NfOrd, FqNmodFiniteField}(O, F, _image, _preimage)
    return z
  end

  function NfOrdToFqNmodMor(O::NfOrd, P::NfOrdIdl)
    z = NfOrdToFqNmodMor()
    z.P = P
    p = minimum(P)
    a, g, b = get_residue_field_data(P)
    psmall = Int(p)
    R = GF(psmall, cached = false)
    Rx, x = PolynomialRing(R, "_\$", cached = false)
    F = FqNmodFiniteField(Rx(g), Symbol("_\$"), false)
    d = degree(g)
    n = degree(O)
    imageofbasis = Vector{fq_nmod}(undef, n)
    powers = Vector{nf_elem}(undef, d)
    c = Rx()
    for i in 1:n
      ib = F()
      @assert d == ncols(b[i])
      for j in 1:d
        setcoeff!(c, j - 1, b[i][1, j])
      end
      ccall((:fq_nmod_set, libflint), Nothing, (Ref{fq_nmod}, Ref{gfp_poly}, Ref{FqNmodFiniteField}), ib, c, F)
      imageofbasis[i] = ib
    end

    powers[1] = a.elem_in_nf
    for i in 2:d
      powers[i] = powers[i - 1] * a.elem_in_nf
    end
    z.powers = powers

    tempF = F()

    function _image(x::NfOrdElem)
      v = coordinates(x, copy = false)
      zz = zero(F)
      for i in 1:n
        ccall((:fq_nmod_mul_fmpz, libflint), Nothing,
              (Ref{fq_nmod}, Ref{fq_nmod}, Ref{fmpz}, Ref{FqNmodFiniteField}),
              tempF, imageofbasis[i], v[i], F)
        add!(zz, zz, tempF)
      end
      return zz
    end

    function _preimage(y::fq_nmod)
      zz = O()
      zz.elem_in_nf = nf(O)(coeff(y, 0))
      for i in 2:d
        add!(zz.elem_in_nf, zz.elem_in_nf, powers[i - 1] * coeff(y, i - 1))
      end
      zz.elem_in_nf = mod(zz.elem_in_nf, p)
      return zz
    end

    z.header = MapHeader{NfOrd, FqNmodFiniteField}(O, F, _image, _preimage)
    return z
  end
end

function preimage(f::NfOrdToFqNmodMor, y::fq_nmod)
  O = domain(f)
  p = minimum(f.P)
  powers = f.powers
  d = length(powers)
  zz = O()
  zz.elem_in_nf = nf(O)(coeff(y, 0))
  for i in 2:d
    add!(zz.elem_in_nf, zz.elem_in_nf, powers[i - 1] * coeff(y, i - 1))
  end
  zz.elem_in_nf = mod(zz.elem_in_nf, p)
  return zz
end


# S is the type of the order, T the type of the ideal and U the elem_type of the order, which define the quotient ring
mutable struct AbsOrdQuoMap{S, T, U} <: Map{S, AbsOrdQuoRing{S, T}, HeckeMap, AbsOrdQuoMap}
  header::MapHeader{S, AbsOrdQuoRing{S, T}}

  function AbsOrdQuoMap{S, T, U}(O::S, Q::AbsOrdQuoRing{S, T}) where {S, T, U}
    z = new()

    function _image(x::U)
      return Q(x)
    end

    function _image(x::FacElem)
      return mod(x, Q)
    end

    function _preimage(x::AbsOrdQuoRingElem{S, T, U})
      x.elem = mod(x.elem, parent(x))
      return x.elem
    end

    z.header = MapHeader(O, Q, _image, _preimage)
    return z
  end
end

function AbsOrdQuoMap(O::S, Q::AbsOrdQuoRing{S, T}) where {S, T}
  U = elem_type(O)
  return AbsOrdQuoMap{S, T, U}(O, Q)
end

const NfOrdQuoMap = AbsOrdQuoMap{NfOrd, NfOrdIdl, NfOrdElem}

function Mor(O::NfOrd, F::FqNmodFiniteField, y::fq_nmod)
  return NfOrdToFqNmodMor(O, F, y)
end

function Mor(O::NfOrd, F::FqNmodFiniteField, h::gfp_poly)
  return NfOrdToFqNmodMor(O, F, h)
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

function _get_coeff_raw(x::fq_nmod, i::Int)
  u = ccall((:nmod_poly_get_coeff_ui, libflint), UInt, (Ref{fq_nmod}, Int), x, i)
  return u
end

function _get_coeff_raw(x::fq, i::Int)
  t = fmpz()
  ccall((:fmpz_poly_get_coeff_fmpz, libflint), Nothing, (Ref{fmpz}, Ref{fq}, Int), t, x, i)
  return t
end

# this is super slow
# improve
function (f::NfOrdQuoMap)(I::NfOrdIdl)
  O = domain(f)
  Q = codomain(f)
  B = Q.ideal + I
  nB = norm(B, copy = false)
  if isone(nB)
    return one(Q)
  end
  _assure_weakly_normal_presentation(B)
  nQ = norm(Q.ideal, copy = false)
  if _normmod(nQ, B.gen_two) == nB
    return Q(B.gen_two)
  end
  b = basis(B, copy = false)
  range1nQ2 = fmpz(1):nQ^2
  z = O()
  while true
    z = rand!(z, b, range1nQ2)
    if _normmod(nQ, z) == nB
      break
    end
  end
  return Q(z)
end


function (f::NfOrdQuoMap)(p::PolyElem{NfOrdElem})
  F = codomain(f)
  Fx,_ = PolynomialRing(F, "_\$", cached = false)

  ar = NfOrdElem[ coeff(p, i) for i in 0:degree(p) ]

  z = Fx(map(f, ar))

  return z
end

mutable struct NfOrdToFqMor <: Map{NfOrd, FqFiniteField, HeckeMap, NfOrdToFqMor}
  header::MapHeader{NfOrd, FqFiniteField}
  poly_of_the_field::gfp_fmpz_poly
  P::NfOrdIdl
  fastpath::Bool
  # Some temporary variables
  tmp_gfp_fmpz_poly::gfp_fmpz_poly
  t_fmpz_poly::fmpz_poly
  t_fmpz::fmpz
  a::nf_elem

  function NfOrdToFqMor()
    z = new()
    return z
  end

  function NfOrdToFqMor(O::NfOrd, F::FqFiniteField, g::gfp_fmpz_poly)
    # assume that F = F_p[X]/(g) and g is a factor of f mod p

    z = new()
    z.fastpath = true
    p = characteristic(F)
    z.tmp_gfp_fmpz_poly = parent(g)()
    z.t_fmpz_poly = fmpz_poly()
    z.t_fmpz = fmpz()

    z.a = gen(nf(O))
    z.poly_of_the_field = g

    z.header = MapHeader{NfOrd, FqFiniteField}(O, F)# _image, _preimage)

    return z
  end
end

function NfOrdToFqMor(O::NfOrd, P::NfOrdIdl)#, g::fmpz_poly, a::NfOrdElem, b::Vector{fmpz_mat})
  z = NfOrdToFqMor()
  z.fastpath = false
  z.P = P
  a, g, b = get_residue_field_data(P)
  p = minimum(P)
  R = GF(p, cached = false)
  Rx, x = PolynomialRing(R, "_\$", cached = false)
  F = FqFiniteField(Rx(g), Symbol("_\$"), false)
  d = degree(g)
  n = degree(O)
  imageofbasis = Vector{fq}(undef, n)
  powers = Vector{nf_elem}(undef, d)
  c = Rx()

  for i in 1:n
    ib = F()
    @assert d == ncols(b[i])
    for j in 1:d
      setcoeff!(c, j - 1, b[i][1, j])
    end
    ccall((:fq_set, libflint), Nothing, (Ref{fq}, Ref{gfp_fmpz_poly}, Ref{FqFiniteField}), ib, c, F)
    imageofbasis[i] = ib
  end

  powers[1] = a.elem_in_nf
  for i in 2:d
    powers[i] = powers[i - 1] * a.elem_in_nf
  end

  tempF = F()

  function _image(x::NfOrdElem)
    v = coordinates(x, copy = false)
    zz = zero(F)
    for i in 1:n
      ccall((:fq_mul_fmpz, libflint), Nothing,
            (Ref{fq}, Ref{fq}, Ref{fmpz}, Ref{FqFiniteField}),
            tempF, imageofbasis[i], v[i], F)
      add!(zz, zz, tempF)
    end
    return zz
  end

  function _preimage(y::fq)
    zz = O()
    zz.elem_in_nf = nf(O)(coeff(y, 0))
    for i in 2:d
      add!(zz.elem_in_nf, zz.elem_in_nf, powers[i - 1] * coeff(y, i - 1))
    end
    zz.elem_in_nf = mod(zz.elem_in_nf, p)
    return zz
  end

  z.header = MapHeader{NfOrd, FqFiniteField}(O, F, _image, _preimage)
  return z
end

function image(f::NfOrdToFqMor, x::NfOrdElem)
  if f.fastpath
    F = codomain(f)
    O = domain(f)
    u = F()
    gg = parent(nf(O).pol)(elem_in_nf(x, copy = false))::fmpq_poly
    fmpq_poly_to_gfp_fmpz_poly_raw!(f.tmp_gfp_fmpz_poly, gg, f.t_fmpz_poly, f.t_fmpz)
    ccall((:fmpz_mod_poly_rem, libflint), Nothing, (Ref{gfp_fmpz_poly}, Ref{gfp_fmpz_poly}, Ref{gfp_fmpz_poly}, Ref{Nemo.fmpz_mod_ctx_struct}), f.tmp_gfp_fmpz_poly, f.tmp_gfp_fmpz_poly, f.poly_of_the_field, f.tmp_gfp_fmpz_poly.parent.base_ring.ninv)
    ccall((:fq_set, libflint), Nothing, (Ref{fq}, Ref{gfp_fmpz_poly}, Ref{FqFiniteField}), u, f.tmp_gfp_fmpz_poly, F)
    ccall((:fq_reduce, libflint), Nothing, (Ref{fq}, Ref{FqFiniteField}), u, F)
    return u
  else
    return f.header.image(x)::fq
  end
end

function preimage(f::NfOrdToFqMor, x::fq)
  if f.fastpath
    O = domain(f)
    F = codomain(f)
    zz = nf(O)()

    a = f.a
    # TODO: Do something more clever here
    for i in 0:degree(F)-1
      zz = zz + coeff(x, i)*a^i
    end

    return O(zz, false)::NfOrdElem
  else
    @assert isdefined(f.header, :preimage)
    return f.header.preimage(x)::NfOrdElem
  end
end


function Mor(O::NfOrd, F::FqFiniteField, h::gfp_fmpz_poly)
  return NfOrdToFqMor(O, F, h)
end


################################################################################
#
#  ResidueField degree 1 primes
#
################################################################################


mutable struct NfOrdToGFMor <: Map{NfOrd, GaloisField, HeckeMap, NfOrdToFqNmodMor}
  header::MapHeader{NfOrd, GaloisField}
  poly_of_the_field::gfp_poly
  P::NfOrdIdl

  function NfOrdToGFMor()
    r = new()
    r.header = MapHeader{NfOrd, GaloisField}()
    return r
  end

  function NfOrdToGFMor(O::NfOrd, F::GaloisField, g::gfp_poly)
    # assume that F = F_p[X]/(g) and g is a factor of f mod p of degree 1

    z = new()
    tmp_gfp_poly = parent(g)()
    z.poly_of_the_field = g
		local _image
    let g = g, tmp_gfp_poly = tmp_gfp_poly, O = O, F = F
    	function _image(x::NfOrdElem)
      	gg = parent(nf(O).pol)(elem_in_nf(x))::fmpq_poly
      	fmpq_poly_to_gfp_poly_raw!(tmp_gfp_poly, gg)
      	ccall((:nmod_poly_rem, libflint), Nothing,
        	    (Ref{gfp_poly}, Ref{gfp_poly}, Ref{gfp_poly}, Ptr{Nothing}),
          	  tmp_gfp_poly, tmp_gfp_poly, g, pointer_from_objref(F)+sizeof(fmpz))
      	return coeff(tmp_gfp_poly, 0)
			end
    end

    z.header = MapHeader{NfOrd, GaloisField}(O, F, _image)
    return z
  end

  function NfOrdToGFMor(O::NfOrd, P::NfOrdIdl)
    z = NfOrdToGFMor()
    z.P = P
    p = minimum(P)
    a, g, b = get_residue_field_data(P)
    psmall = Int(p)
		n = degree(O)
    F = GF(psmall, cached = false)
    imageofbasis = Vector{gfp_elem}(undef, n)
    for i in 1:n
      imageofbasis[i] = F(b[i][1, 1])
    end

		local _image
		let imageofbasis = imageofbasis, F = F, n = n
   		function _image(x::NfOrdElem)
      	v = coordinates(x, copy = false)
      	tempF = zero(UInt)
      	for i in 1:n
          tempF += mul_mod(imageofbasis[i].data, v[i], F)
       	end
      	return F(tempF)
			end
    end

    z.header = MapHeader{NfOrd, GaloisField}(O, F, _image)
    return z
  end
end

function preimage(f::NfOrdToGFMor, a::gfp_elem)
  return domain(f)(a.data)
end

Mor(O::NfOrd, F::GaloisField, g::gfp_poly) = NfOrdToGFMor(O, F, g)



mutable struct NfOrdToGFFmpzMor <: Map{NfOrd, Nemo.GaloisFmpzField, HeckeMap, NfOrdToGFFmpzMor}
  header::MapHeader{NfOrd, Nemo.GaloisFmpzField}
  poly_of_the_field::gfp_fmpz_poly
  P::NfOrdIdl

  function NfOrdToGFFmpzMor()
    r = new()
    return r
  end

  function NfOrdToGFFmpzMor(O::NfOrd, F::Nemo.GaloisFmpzField, g::gfp_fmpz_poly)
    # assume that F = F_p[X]/(g) and g is a factor of f mod p of degree 1

    z = new()
    tmp_gfp_poly = parent(g)()
    z.poly_of_the_field = g
		local _image
    let g = g, tmp_gfp_poly = tmp_gfp_poly, O = O, F = F
    	function _image(x::NfOrdElem)
      	gg = parent(nf(O).pol)(elem_in_nf(x))::fmpq_poly
      	fmpq_poly_to_gfp_fmpz_poly_raw!(tmp_gfp_poly, gg)
				rem!(tmp_gfp_poly, tmp_gfp_poly, g)
      	return coeff(tmp_gfp_poly, 0)
			end
    end

    z.header = MapHeader{NfOrd, Nemo.GaloisFmpzField}(O, F, _image)
    return z
  end

  function NfOrdToGFFmpzMor(O::NfOrd, P::NfOrdIdl)
    z = NfOrdToGFFmpzMor()
    z.P = P
    p = minimum(P)
    a, g, b = get_residue_field_data(P)
		n = degree(O)
    F = GF(p, cached = false)
    imageofbasis = Vector{Nemo.gfp_fmpz_elem}(undef, n)
    for i in 1:n
      imageofbasis[i] = F(b[i][1, 1])
    end

    tempF = F()
		local _image
		let tempF = tempF, imageofbasis = imageofbasis, F = F, n = n
   		function _image(x::NfOrdElem)
      	v = coordinates(x, copy = false)
      	zz = zero(F)
      	for i in 1:n
          mul!(tempF, imageofbasis[i], v[i])
        	add!(zz, zz, tempF)
      	end
      	return zz
			end
    end

    z.header = MapHeader{NfOrd, Nemo.GaloisFmpzField}(O, F, _image)
    return z
  end
end

function preimage(f::NfOrdToGFFmpzMor, a::Nemo.gfp_fmpz_elem)
  return domain(f)(lift(a))
end

Mor(O::NfOrd, F::Nemo.GaloisFmpzField, h::gfp_fmpz_poly) = NfOrdToGFFmpzMor(O, F, h)

################################################################################
#
#  Extend to number field
#
################################################################################

mutable struct NfToFinFldMor{T} <: Map{AnticNumberField, T, HeckeMap, NfToFinFldMor{T}}
  header::MapHeader{AnticNumberField, T}

  function NfToFinFldMor{T}() where T
    r = new{T}()
    r.header = MapHeader{AnticNumberField, T}()
    return r
  end
end


function extend(f::T, K::AnticNumberField) where T <: Union{NfOrdToFqNmodMor, NfOrdToFqMor, NfOrdToGFMor, NfOrdToGFFmpzMor}
  nf(domain(f)) != K && error("Number field is not the number field of the order")

  z = NfToFinFldMor{typeof(codomain(f))}()

  z.header.domain = K
  z.header.codomain = f.header.codomain

  pia = anti_uniformizer(f.P)
  O = domain(f)
  P = f.P

  _image = function(x::nf_elem)
    !iszero(x) && valuation(x, P) < 0 && error("Element not p-integral")
    m = denominator(x, domain(f))
    l = valuation(m, P)
    if l == 0
      return f(O(m*x, false))//f(O(m))
    else
      pial = pia^l
      pialm = pial * m
      w = pialm * x
      return f(O(w, false))//f(O(pialm, false))
    end
  end

  _preimage = function(x)
    return elem_in_nf(preimage(f, x))
  end

  z.header.image = _image
  z.header.preimage = _preimage

  return z
end

#=
function (f::Union{NfOrdToFqNmodMor, NfOrdToFqMor, NfOrdToGFMor, NfOrdToGFFmpzMor})(p::PolyElem{NfOrdElem})
  return map_coefficients(f, p)
end
=#
@doc Markdown.doc"""
    extend_easy(f::Hecke.NfOrdToFqNmodMor, K::AnticNumberField) -> NfToFqNmodMor

For a residue field map from a prime ideal, extend the domain of the map
to the entire field.
Requires the prime ideal to be coprime to the index, unramified and
over a small integer. The resulting map can very efficiently be
evaluated using `image(map, elem)`.
The resulting map can be applied to
  * `nf_elem`
  * `FacElem{nf_elem}`
Will throw a `BadPrime` exception if applied to an element in the
field with a $p$ in the denominator. In the case of `FacElem`, zero
is also not permitted (and will produce a `BadPrime` error).
"""
function extend_easy(f::Hecke.NfOrdToFqNmodMor, K::AnticNumberField)
  nf(domain(f)) != K && error("Number field is not the number field of the order")
  return NfToFqNmodMor_easy(f, K)
end

#a stop-gap, mainly for non-monic polynomials
function extend_easy(f::Hecke.NfOrdToFqMor, K::AnticNumberField)
  return NfToFqMor_easy(f, K)
end

function extend_easy(f::Hecke.NfOrdToGFMor, K::AnticNumberField)
  return NfToGFMor_easy(f, K)
end

function extend_easy(f::Hecke.NfOrdToGFFmpzMor, K::AnticNumberField)
  return NfToGFFmpzMor_easy(f, K)
end


mutable struct NfToFqMor_easy <: Map{AnticNumberField, FqFiniteField, HeckeMap, NfToFqMor_easy}
  header::MapHeader{AnticNumberField, FqFiniteField}
  Fq::FqFiniteField
  s::fq
  t::gfp_fmpz_poly
  function NfToFqMor_easy(a::Map, k::AnticNumberField)
    r = new()
    r.Fq = codomain(a)
    r.header = MapHeader(k, r.Fq)
    r.s = r.Fq()
    r.t = PolynomialRing(GF(characteristic(r.Fq), cached = false), cached = false)[1]()
    return r
  end
end

function image(mF::NfToFqMor_easy, a::FacElem{nf_elem, AnticNumberField}, quo::Int = 0)
  Fq = mF.Fq
  q = one(Fq)
  t = mF.t
  s = mF.s
  for (k, v) = a.fac
    vv = v
    if quo != 0
      vv = v % quo
      if vv < 0
        vv += quo
      end
    end
    @assert vv < order(Fq)  #please complain if this is triggered
    if !iszero(vv)
      if denominator(k) % characteristic(Fq) == 0
        throw(BadPrime(characteristic(Fq)))
      end
      _nf_to_fq!(s, k, Fq, t)
      if iszero(s)
        throw(BadPrime(1))
      end
      if vv < 0
        ccall((:fq_inv, libflint), Nothing, (Ref{fq}, Ref{fq}, Ref{FqFiniteField}), s, s, Fq)
        vv = -vv
      end
      ccall((:fq_pow_ui, libflint), Nothing, (Ref{fq}, Ref{fq}, Int, Ref{FqFiniteField}), s, s, vv, Fq)
      mul!(q, q, s)
    end
  end
  return q
end

function image(mF::NfToFqMor_easy, a::nf_elem, n_quo::Int = 0)
  Fq = mF.Fq
  q = Fq()
  if denominator(a) % characteristic(Fq) == 0
    throw(BadPrime(characteristic(Fq)))
  end
  _nf_to_fq!(q, a, Fq, mF.t)
  return q
end


mutable struct NfToFqNmodMor_easy <: Map{AnticNumberField, FqNmodFiniteField, HeckeMap, NfToFqNmodMor_easy}
  header::MapHeader{AnticNumberField, FqNmodFiniteField}
  Fq::FqNmodFiniteField
  s::fq_nmod
  t::gfp_poly
  function NfToFqNmodMor_easy(a::Map, k::AnticNumberField)
    r = new()
    r.Fq = codomain(a)
    r.header = MapHeader(k, r.Fq)
    r.s = r.Fq()
    r.t = PolynomialRing(GF(UInt(characteristic(r.Fq)), cached=false), cached=false)[1]()
    return r
  end
end

function image(mF::NfToFqNmodMor_easy, a::FacElem{nf_elem, AnticNumberField}, quo::Int = 0)
  Fq = mF.Fq
  q = one(Fq)
  t = mF.t
  s = mF.s
  oFq = order(Fq) # fmpz
  small_mod = UInt(0)
  char_Fq = characteristic(Fq)

  if quo != 0
    small_mod = UInt(quo)
  end

  for (k, v) = a.fac
    # I want to map k^v to F. I can reduce mod q (reduction modulo q - 1 is
    # done by the power function itself.

    inver = false

    if v < 0
      v = -v
      inver = true
    end

    local vv::UInt

    if quo != 0
      if v > small_mod
        vv = fmpz_mod_ui(v, small_mod)
      else
        vv = UInt(v)
      end
    end

    if (quo != 0 && vv != 0) || !iszero(v)
      # We have something to do
      if iszero(denominator(k) % char_Fq)
        throw(BadPrime(characteristic(Fq)))
      end
      _nf_to_fq!(s, k, Fq, t)
      if iszero(s)
        throw(BadPrime(1))
      end
      if inver
        ccall((:fq_nmod_inv, libflint), Nothing, (Ref{fq_nmod}, Ref{fq_nmod}, Ref{FqNmodFiniteField}), s, s, Fq)
      end
      if quo != 0
        ccall((:fq_nmod_pow_ui, libflint), Nothing, (Ref{fq_nmod}, Ref{fq_nmod}, Int, Ref{FqNmodFiniteField}), s, s, vv, Fq)
      else
        ccall((:fq_nmod_pow, libflint), Nothing, (Ref{fq_nmod}, Ref{fq_nmod}, Ref{fmpz}, Ref{FqNmodFiniteField}), s, s, v, Fq)
      end
      mul!(q, q, s)
    end
  end
  return q
end

function image(mF::NfToFqNmodMor_easy, a::FacElem{nf_elem, AnticNumberField}, D::Vector, cached::Bool, quo::Int = 0)
  Fq = mF.Fq
  q = one(Fq)
  t = mF.t
  s = mF.s
  i = 0
  char = UInt(Fq.n)
  small_mod = UInt(0)

  if quo != 0
    small_mod = UInt(quo)
  end

  for (k, v) in a.fac
    i += 1

    inver = false

    if v < 0
      v = -v
      inver = true
    end

    local vv::UInt

    if quo != 0
      if v > small_mod
        vv = fmpz_mod_ui(v, small_mod)
      else
        vv = UInt(v)
      end
    end


    # We always reduce, so do the test first
    if !cached && iszero(fmpz_mod_ui(denominator(k), char))
      throw(BadPrime(characteristic(Fq)))
    end

    if !((quo != 0 && vv != 0) || !iszero(v))
      if !cached
        nf_elem_to_gfp_poly!(t, k)
        D[i] = zero(parent(t))
        set!(D[i], t)
      end
    end

    if (quo != 0 && vv != 0) || !iszero(v)
      if cached
        s = zero(Fq)
        ccall((:fq_nmod_set, libflint), Nothing,
          (Ref{fq_nmod}, Ref{gfp_poly}, Ref{FqNmodFiniteField}), s, D[i], Fq)
        _reduce(s)
      else
        nf_elem_to_gfp_poly!(t, k)
        #tt = deepcopy(t)
        if isassigned(D, i)
          y = D[i]
          if y.mod_n == t.mod_n
            y.parent = t.parent
            set!(y, t)
          else
            y.mod_n = t.mod_n
            y.mod_ninv = t.mod_ninv
            y.mod_norm = t.mod_norm
            y.parent = t.parent
            set!(y, t)
          end
        else
          D[i] = zero(parent(t))
          set!(D[i], t)
        end
        s = zero(Fq)
        ccall((:fq_nmod_set, libflint), Nothing,
          (Ref{fq_nmod}, Ref{gfp_poly}, Ref{FqNmodFiniteField}), s, D[i], Fq)
        _reduce(s)
      end
      if iszero(s)
        throw(BadPrime(1))
      end

      if inver
        ccall((:fq_nmod_inv, libflint), Nothing, (Ref{fq_nmod}, Ref{fq_nmod}, Ref{FqNmodFiniteField}), s, s, Fq)
      end
      if quo != 0
        ccall((:fq_nmod_pow_ui, libflint), Nothing, (Ref{fq_nmod}, Ref{fq_nmod}, Int, Ref{FqNmodFiniteField}), s, s, vv, Fq)
      else
        ccall((:fq_nmod_pow, libflint), Nothing, (Ref{fq_nmod}, Ref{fq_nmod}, Ref{fmpz}, Ref{FqNmodFiniteField}), s, s, v, Fq)
      end
      mul!(q, q, s)

      #if vv < 0
      #  s = inv(s)
      #  vv = -vv
      #end
      #s = s^Int(vv)
      #q = mul!(q, q, s)
    end
  end
  return q
end

function image(mF::NfToFqNmodMor_easy, a::nf_elem, n_quo::Int = 0)
  Fq = mF.Fq
  q = Fq()
  if denominator(a) % characteristic(Fq) == 0
    throw(BadPrime(characteristic(Fq)))
  end
  _nf_to_fq!(q, a, Fq, mF.t)
  return q
end

function _nf_to_gfp_elem(b::nf_elem, a_tmp::gfp_poly, def_pol::gfp_poly)
  nf_elem_to_gfp_poly!(a_tmp, b)
  rem!(a_tmp, a_tmp, def_pol)
  return coeff(a_tmp, 0)
end

function _nf_to_gfp_elem(b::nf_elem, a_tmp::gfp_fmpz_poly, def_pol::gfp_fmpz_poly)
  nf_elem_to_gfp_fmpz_poly!(a_tmp, b)
  rem!(a_tmp, a_tmp, def_pol)
  return coeff(a_tmp, 0)
end

mutable struct NfToGFMor_easy <: Map{AnticNumberField, GaloisField, HeckeMap, NfToGFMor_easy}
  header::MapHeader{AnticNumberField, GaloisField}
  Fq::GaloisField
  defining_pol::gfp_poly
  s::gfp_elem
  t::gfp_poly
  function NfToGFMor_easy(a::NfOrdToGFMor, k::AnticNumberField)
    r = new()
    r.Fq = codomain(a)
    r.defining_pol = a.poly_of_the_field
    r.header = MapHeader(k, r.Fq)
    r.s = r.Fq()
    r.t = zero(parent(r.defining_pol))
    return r
  end
end

function image(mF::NfToGFMor_easy, a::FacElem{nf_elem, AnticNumberField}, quo::Int = 0)
  Fq = mF.Fq
  p = mF.defining_pol
  q = one(Fq)
  t = mF.t
  for (k, v) = a.fac
    vv = v
    if quo != 0
      vv = v %quo
      if vv < 0
        vv += quo
      end
    end
    @assert vv < order(Fq)  #please complain if this is triggered
    if !iszero(vv)
      if denominator(k) % characteristic(Fq) == 0
        throw(BadPrime(characteristic(Fq)))
      end
      s = _nf_to_gfp_elem(k, t, p)
      if iszero(s)
        throw(BadPrime(1))
      end
      if vv < 0
        s = inv(s)
        vv = -vv
      end
      s = s^vv
      q = mul!(q, q, s)
    end
  end
  return q
end

function image(mF::NfToGFMor_easy, a::FacElem{nf_elem, AnticNumberField}, D::Vector, cached::Bool, quo::Int = 0)
  # cached == true also implies that all the denominators are coprime
  Fq = mF.Fq
  p = mF.defining_pol
  q = one(Fq)
  t = mF.t
  i = 0
  pminusone = Fq.n - 1
  @assert is_monic(p)
  evaluateat = -coeff(p, 0)
  for (k, v) in a.fac
    i += 1
    if v > 0 && v < pminusone
      vv = UInt(v)
    else
      vv = fmpz_mod_ui(v, pminusone)
    end
    if quo != 0
      vv = vv % quo # vv will always be positive
    end
    @assert vv < Fq.n  #please complain if this is triggered

    # We always have to reduce, so check first
    if !cached && (fmpz_mod_ui(denominator(k), Fq.n) == 0)
      throw(BadPrime(characteristic(Fq)))
    end

    if iszero(vv) && !cached
      D[i] = zero(parent(t))
      nf_elem_to_gfp_poly!(t, k)
      set!(D[i], t)
    end

    if !iszero(vv)
      if cached
        s = evaluate_raw(D[i], evaluateat)
      else
        nf_elem_to_gfp_poly!(t, k)
        #tt = deepcopy(t)
        if isassigned(D, i)
          y = D[i]
          if y.mod_n == t.mod_n
            y.parent = t.parent
            set!(y, t)
          else
            y.mod_n = t.mod_n
            y.mod_ninv = t.mod_ninv
            y.mod_norm = t.mod_norm
            y.parent = t.parent
            set!(y, t)
          end
        else
          D[i] = zero(parent(t))
          set!(D[i], t)
        end
        s = evaluate(t, evaluateat)
      end
      #s = _nf_to_gfp_elem(k, t, p)
      if iszero(s)
        throw(BadPrime(1))
      end
      if vv < 0
        s = inv(s)
        vv = -vv
      end
      s = s^Int(vv)
      q = mul!(q, q, s)
    end
  end
  return q
end

function image(mF::NfToGFMor_easy, a::nf_elem, n_quo::Int = 0)
  Fq = mF.Fq
  p = mF.defining_pol
  t = mF.t
  if denominator(a) % characteristic(Fq) == 0
    throw(BadPrime(characteristic(Fq)))
  end
  return _nf_to_gfp_elem(a, t, p)
end

function image(mF::NfToGFMor_easy, a::nf_elem, D::Vector, cached::Bool, n_quo::Int = 0)
  Fq = mF.Fq
  p = mF.defining_pol
  t = mF.t

  @assert is_monic(p)
  evaluateat = -coeff(p, 0)

  if denominator(a) % characteristic(Fq) == 0
    throw(BadPrime(characteristic(Fq)))
  end
  if cached
    @assert length(D) == 1
    s = evaluate_raw(D[1], evaluateat)
    #rem!(t, D[1], p)
    #s = coeff(t, 0)
  else
    nf_elem_to_gfp_poly!(t, a)
    D[1] = deepcopy(t)
    #rem!(t, t, p)
    #s = coeff(t, 0)
    s = evaluate_raw(t, evaluateat)
  end
  return s
end


mutable struct NfToGFFmpzMor_easy <: Map{AnticNumberField, Nemo.GaloisFmpzField, HeckeMap, NfToGFFmpzMor_easy}
  header::MapHeader{AnticNumberField, Nemo.GaloisFmpzField}
  Fq::Nemo.GaloisFmpzField
  defining_pol::Nemo.gfp_fmpz_poly
  s::Nemo.gfp_fmpz_elem
  t::Nemo.gfp_fmpz_poly
  function NfToGFFmpzMor_easy(a::NfOrdToGFFmpzMor, k::AnticNumberField)
    r = new()
    r.Fq = codomain(a)
    r.header = MapHeader(k, r.Fq)
    r.s = r.Fq()
    r.defining_pol = a.poly_of_the_field
    r.t = zero(parent(a.poly_of_the_field))
    return r
  end
end

function image(mF::NfToGFFmpzMor_easy, a::FacElem{nf_elem, AnticNumberField}, quo::Int = 0)
  Fq = mF.Fq
  p = mF.defining_pol
  q = one(Fq)
  t = mF.t
  for (k, v) = a.fac
    vv = v
    if quo != 0
      vv = v %quo
      if vv < 0
        vv += quo
      end
    end
    @assert vv < order(Fq)  #please complain if this is triggered
    if !iszero(vv)
      if denominator(k) % characteristic(Fq) == 0
        throw(BadPrime(characteristic(Fq)))
      end
      s = _nf_to_gfp_fmpz_elem(k, t, p)
      if iszero(s)
        throw(BadPrime(1))
      end
      if vv < 0
        s = inv(s)
        vv = -vv
      end
      s = s^vv
      mul!(q, q, s)
    end
  end
  return q
end

function image(mF::NfToGFFmpzMor_easy, a::nf_elem, n_quo::Int = 0)
  Fq = mF.Fq
  p = mF.defining_pol
  t = mF.t
  if denominator(a) % characteristic(Fq) == 0
    throw(BadPrime(characteristic(Fq)))
  end
  return _nf_to_gfp_fmpz_elem(a, t, p)
end

################################################################################
#
#  AbsOrdToAlgAssMor type
#
################################################################################

mutable struct AbsOrdToAlgAssMor{S, T} <: Map{S, AlgAss{T}, HeckeMap, AbsOrdToAlgAssMor}
  header::MapHeader

  function AbsOrdToAlgAssMor{S, T}(O::S, A::AlgAss{T}, _image::Function, _preimage::Function) where {S <: Union{ NfAbsOrd, AlgAssAbsOrd }, T}
    z = new{S, T}()
    z.header = MapHeader(O, A, _image, _preimage)
    return z
  end
end

function AbsOrdToAlgAssMor(O::Union{ NfAbsOrd, AlgAssAbsOrd }, A::AlgAss{T}, _image, _preimage) where {T}
  return AbsOrdToAlgAssMor{typeof(O), T}(O, A, _image, _preimage)
end


# Helper

function mul!(z::gfp_elem, x::gfp_elem, y::fmpz)
  R = parent(x)
  d = ccall((:fmpz_fdiv_ui, libflint), UInt, (Ref{fmpz}, UInt), y, R.n)
  r = ccall((:n_mulmod2_preinv, libflint), UInt, (UInt, UInt, UInt, UInt),
             x.data, d, R.n, R.ninv)
  z.data = r
  return z
end

function mul_mod(x::UInt, y::fmpz, R)
  d = ccall((:fmpz_fdiv_ui, libflint), UInt, (Ref{fmpz}, UInt), y, R.n)
  r = ccall((:n_mulmod2_preinv, libflint), UInt, (UInt, UInt, UInt, UInt),
             x, d, R.n, R.ninv)
  return r
end

function mul!(z::Nemo.gfp_fmpz_elem, x::Nemo.gfp_fmpz_elem, y::fmpz)
  R = parent(x)
  ccall((:fmpz_mod, libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}),
        z.data, y, R.n)

  ccall((:fmpz_mod_mul, libflint), Nothing,
        (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}, Ref{Nemo.fmpz_mod_ctx_struct}),
        z.data, x.data, z.data, R.ninv)
  return z
end

function rem!(z::gfp_poly, a::gfp_poly, b::gfp_poly)
  ccall((:nmod_poly_rem, libflint), Nothing,
        	    (Ref{gfp_poly}, Ref{gfp_poly}, Ref{gfp_poly}, Ptr{Nothing}),
          	  z, a, b, pointer_from_objref(base_ring(z))+sizeof(fmpz))
  return z
end

function evaluate_raw(x::gfp_poly, y::gfp_elem)
  z = ccall((:nmod_poly_evaluate_nmod, libflint), UInt,
              (Ref{gfp_poly}, UInt), x, y.data)
  return parent(y)(z)
end

function fmpz_mod_ui(x::fmpz, y::UInt)
  return ccall((:fmpz_fdiv_ui, libflint), UInt, (Ref{fmpz}, UInt), x, y)
end
