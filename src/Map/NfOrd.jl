################################################################################
#
#  Ringmorphisms of orders onto finite fields
#
################################################################################

# AbsSimpleNumFieldOrder -> FqNmod
mutable struct NfOrdToFqNmodMor <: Map{AbsSimpleNumFieldOrder, fqPolyRepField, HeckeMap, NfOrdToFqNmodMor}
  header::MapHeader{AbsSimpleNumFieldOrder, fqPolyRepField}
  poly_of_the_field::fpPolyRingElem
  P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}
  powers::Vector{AbsSimpleNumFieldElem}

  function NfOrdToFqNmodMor()
    r = new()
    r.header = MapHeader{AbsSimpleNumFieldOrder, fqPolyRepField}()
    return r
  end

  function NfOrdToFqNmodMor(O::AbsSimpleNumFieldOrder, F::fqPolyRepField, g::fpPolyRingElem)
    # assume that F = F_p[X]/(g) and g is a factor of f mod p

    z = new()
    d = degree(nf(O))
    p = characteristic(F)
    a = gen(nf(O))
    tmp_gfp_poly = parent(g)()
    z.poly_of_the_field = g

    powers = Vector{AbsSimpleNumFieldElem}(undef, d)

    powers[1] = a
    for i in 2:d
      powers[i] = powers[i - 1] * a
    end
    z.powers = powers

    function _image(x::AbsSimpleNumFieldOrderElem)
      u = F()
      gg = parent(nf(O).pol)(elem_in_nf(x))::QQPolyRingElem
      Nemo.fmpq_poly_to_gfp_poly_raw!(tmp_gfp_poly, gg)
      ccall((:nmod_poly_rem, libflint), Nothing,
            (Ref{fpPolyRingElem}, Ref{fpPolyRingElem}, Ref{fpPolyRingElem}, Ptr{Nothing}),
            tmp_gfp_poly, tmp_gfp_poly, g, pointer_from_objref(F)+sizeof(ZZRingElem))
      ccall((:fq_nmod_set, libflint), Nothing,
            (Ref{fqPolyRepFieldElem}, Ref{fpPolyRingElem}, Ref{fqPolyRepField}),
            u, tmp_gfp_poly, F)
      ccall((:fq_nmod_reduce, libflint), Nothing,
            (Ref{fqPolyRepFieldElem}, Ref{fqPolyRepField}), u, F)
      return u
    end

    # The lift is even simpler!
    function _preimage(y::fqPolyRepFieldElem)
      zz = O()
      zz.elem_in_nf = nf(O)(coeff(y, 0))
      for i in 2:d
        add!(zz.elem_in_nf, zz.elem_in_nf, powers[i - 1] * coeff(y, i - 1))
      end
      zz.elem_in_nf = mod(zz.elem_in_nf, p)
      return zz
    end

    z.header = MapHeader{AbsSimpleNumFieldOrder, fqPolyRepField}(O, F, _image, _preimage)
    return z
  end

  function NfOrdToFqNmodMor(O::AbsSimpleNumFieldOrder, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
    z = NfOrdToFqNmodMor()
    z.P = P
    p = minimum(P)
    a, g, b = get_residue_field_data(P)
    psmall = Int(p)
    R = Native.GF(psmall, cached = false)
    Rx, x = polynomial_ring(R, "_\$", cached = false)
    F = fqPolyRepField(Rx(g), Symbol("_\$"), false)
    d = degree(g)
    n = degree(O)
    imageofbasis = Vector{fqPolyRepFieldElem}(undef, n)
    powers = Vector{AbsSimpleNumFieldElem}(undef, d)
    c = Rx()
    for i in 1:n
      ib = F()
      @assert d == ncols(b[i])
      for j in 1:d
        setcoeff!(c, j - 1, b[i][1, j])
      end
      ccall((:fq_nmod_set, libflint), Nothing, (Ref{fqPolyRepFieldElem}, Ref{fpPolyRingElem}, Ref{fqPolyRepField}), ib, c, F)
      imageofbasis[i] = ib
    end

    powers[1] = a.elem_in_nf
    for i in 2:d
      powers[i] = powers[i - 1] * a.elem_in_nf
    end
    z.powers = powers

    tempF = F()

    function _image(x::AbsSimpleNumFieldOrderElem)
      v = coordinates(x, copy = false)
      zz = zero(F)
      for i in 1:n
        ccall((:fq_nmod_mul_fmpz, libflint), Nothing,
              (Ref{fqPolyRepFieldElem}, Ref{fqPolyRepFieldElem}, Ref{ZZRingElem}, Ref{fqPolyRepField}),
              tempF, imageofbasis[i], v[i], F)
        add!(zz, zz, tempF)
      end
      return zz
    end

    function _preimage(y::fqPolyRepFieldElem)
      zz = O()
      zz.elem_in_nf = nf(O)(coeff(y, 0))
      for i in 2:d
        add!(zz.elem_in_nf, zz.elem_in_nf, powers[i - 1] * coeff(y, i - 1))
      end
      zz.elem_in_nf = mod(zz.elem_in_nf, p)
      return zz
    end

    z.header = MapHeader{AbsSimpleNumFieldOrder, fqPolyRepField}(O, F, _image, _preimage)
    return z
  end
end

function preimage(f::NfOrdToFqNmodMor, y::fqPolyRepFieldElem)
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

const NfOrdQuoMap = AbsOrdQuoMap{AbsSimpleNumFieldOrder, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsSimpleNumFieldOrderElem}

function Mor(O::AbsSimpleNumFieldOrder, F::fqPolyRepField, y::fqPolyRepFieldElem)
  return NfOrdToFqNmodMor(O, F, y)
end

function Mor(O::AbsSimpleNumFieldOrder, F::fqPolyRepField, h::fpPolyRingElem)
  return NfOrdToFqNmodMor(O, F, h)
end

function _get_coeff_raw(x::fqPolyRepFieldElem, i::Int)
  u = ccall((:nmod_poly_get_coeff_ui, libflint), UInt, (Ref{fqPolyRepFieldElem}, Int), x, i)
  return u
end

function _get_coeff_raw(x::FqPolyRepFieldElem, i::Int)
  t = ZZRingElem()
  ccall((:fmpz_poly_get_coeff_fmpz, libflint), Nothing, (Ref{ZZRingElem}, Ref{FqPolyRepFieldElem}, Int), t, x, i)
  return t
end

# this is super slow
# improve
function (f::NfOrdQuoMap)(I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
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
  range1nQ2 = ZZRingElem(1):nQ^2
  z = O()
  while true
    z = rand!(z, b, range1nQ2)
    if _normmod(nQ, z) == nB
      break
    end
  end
  return Q(z)
end


function (f::NfOrdQuoMap)(p::PolyRingElem{AbsSimpleNumFieldOrderElem})
  F = codomain(f)
  Fx,_ = polynomial_ring(F, "_\$", cached = false)

  ar = AbsSimpleNumFieldOrderElem[ coeff(p, i) for i in 0:degree(p) ]

  z = Fx(map(f, ar))

  return z
end

mutable struct NfOrdToFqMor <: Map{AbsSimpleNumFieldOrder, FqPolyRepField, HeckeMap, NfOrdToFqMor}
  header::MapHeader{AbsSimpleNumFieldOrder, FqPolyRepField}
  poly_of_the_field::FpPolyRingElem
  P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}
  fastpath::Bool
  # Some temporary variables
  tmp_gfp_fmpz_poly::FpPolyRingElem
  t_fmpz_poly::ZZPolyRingElem
  t_fmpz::ZZRingElem
  a::AbsSimpleNumFieldElem

  function NfOrdToFqMor()
    z = new()
    return z
  end

  function NfOrdToFqMor(O::AbsSimpleNumFieldOrder, F::FqPolyRepField, g::FpPolyRingElem)
    # assume that F = F_p[X]/(g) and g is a factor of f mod p

    z = new()
    z.fastpath = true
    p = characteristic(F)
    z.tmp_gfp_fmpz_poly = parent(g)()
    z.t_fmpz_poly = ZZPolyRingElem()
    z.t_fmpz = ZZRingElem()

    z.a = gen(nf(O))
    z.poly_of_the_field = g

    z.header = MapHeader{AbsSimpleNumFieldOrder, FqPolyRepField}(O, F)# _image, _preimage)

    return z
  end
end

function NfOrdToFqMor(O::AbsSimpleNumFieldOrder, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})#, g::ZZPolyRingElem, a::AbsSimpleNumFieldOrderElem, b::Vector{ZZMatrix})
  z = NfOrdToFqMor()
  z.fastpath = false
  z.P = P
  a, g, b = get_residue_field_data(P)
  p = minimum(P)
  R = Native.GF(p, cached = false)
  Rx, x = polynomial_ring(R, "_\$", cached = false)
  F = FqPolyRepField(Rx(g), Symbol("_\$"), false)
  d = degree(g)
  n = degree(O)
  imageofbasis = Vector{FqPolyRepFieldElem}(undef, n)
  powers = Vector{AbsSimpleNumFieldElem}(undef, d)
  c = Rx()

  for i in 1:n
    ib = F()
    @assert d == ncols(b[i])
    for j in 1:d
      setcoeff!(c, j - 1, b[i][1, j])
    end
    ccall((:fq_set, libflint), Nothing, (Ref{FqPolyRepFieldElem}, Ref{FpPolyRingElem}, Ref{FqPolyRepField}), ib, c, F)
    imageofbasis[i] = ib
  end

  powers[1] = a.elem_in_nf
  for i in 2:d
    powers[i] = powers[i - 1] * a.elem_in_nf
  end

  tempF = F()

  function _image(x::AbsSimpleNumFieldOrderElem)
    v = coordinates(x, copy = false)
    zz = zero(F)
    for i in 1:n
      ccall((:fq_mul_fmpz, libflint), Nothing,
            (Ref{FqPolyRepFieldElem}, Ref{FqPolyRepFieldElem}, Ref{ZZRingElem}, Ref{FqPolyRepField}),
            tempF, imageofbasis[i], v[i], F)
      add!(zz, zz, tempF)
    end
    return zz
  end

  function _preimage(y::FqPolyRepFieldElem)
    zz = O()
    zz.elem_in_nf = nf(O)(coeff(y, 0))
    for i in 2:d
      add!(zz.elem_in_nf, zz.elem_in_nf, powers[i - 1] * coeff(y, i - 1))
    end
    zz.elem_in_nf = mod(zz.elem_in_nf, p)
    return zz
  end

  z.header = MapHeader{AbsSimpleNumFieldOrder, FqPolyRepField}(O, F, _image, _preimage)
  return z
end

function image(f::NfOrdToFqMor, x::AbsSimpleNumFieldOrderElem)
  if f.fastpath
    F = codomain(f)
    O = domain(f)
    u = F()
    gg = parent(nf(O).pol)(elem_in_nf(x, copy = false))::QQPolyRingElem
    Nemo.fmpq_poly_to_gfp_fmpz_poly_raw!(f.tmp_gfp_fmpz_poly, gg, f.t_fmpz_poly, f.t_fmpz)
    ccall((:fmpz_mod_poly_rem, libflint), Nothing, (Ref{FpPolyRingElem}, Ref{FpPolyRingElem}, Ref{FpPolyRingElem}, Ref{Nemo.fmpz_mod_ctx_struct}), f.tmp_gfp_fmpz_poly, f.tmp_gfp_fmpz_poly, f.poly_of_the_field, f.tmp_gfp_fmpz_poly.parent.base_ring.ninv)
    ccall((:fq_set, libflint), Nothing, (Ref{FqPolyRepFieldElem}, Ref{FpPolyRingElem}, Ref{FqPolyRepField}), u, f.tmp_gfp_fmpz_poly, F)
    ccall((:fq_reduce, libflint), Nothing, (Ref{FqPolyRepFieldElem}, Ref{FqPolyRepField}), u, F)
    return u
  else
    return f.header.image(x)::FqPolyRepFieldElem
  end
end

function preimage(f::NfOrdToFqMor, x::FqPolyRepFieldElem)
  if f.fastpath
    O = domain(f)
    F = codomain(f)
    zz = nf(O)()

    a = f.a
    # TODO: Do something more clever here
    for i in 0:degree(F)-1
      zz = zz + coeff(x, i)*a^i
    end

    return O(zz, false)::AbsSimpleNumFieldOrderElem
  else
    @assert isdefined(f.header, :preimage)
    return f.header.preimage(x)::AbsSimpleNumFieldOrderElem
  end
end


function Mor(O::AbsSimpleNumFieldOrder, F::FqPolyRepField, h::FpPolyRingElem)
  return NfOrdToFqMor(O, F, h)
end


################################################################################
#
#  residue_field degree 1 primes
#
################################################################################


mutable struct NfOrdToGFMor <: Map{AbsSimpleNumFieldOrder, fpField, HeckeMap, NfOrdToFqNmodMor}
  header::MapHeader{AbsSimpleNumFieldOrder, fpField}
  poly_of_the_field::fpPolyRingElem
  P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

  function NfOrdToGFMor()
    r = new()
    r.header = MapHeader{AbsSimpleNumFieldOrder, fpField}()
    return r
  end

  function NfOrdToGFMor(O::AbsSimpleNumFieldOrder, F::fpField, g::fpPolyRingElem)
    # assume that F = F_p[X]/(g) and g is a factor of f mod p of degree 1

    z = new()
    tmp_gfp_poly = parent(g)()
    z.poly_of_the_field = g
		local _image
    let g = g, tmp_gfp_poly = tmp_gfp_poly, O = O, F = F
    	function _image(x::AbsSimpleNumFieldOrderElem)
      	gg = parent(nf(O).pol)(elem_in_nf(x))::QQPolyRingElem
      	Nemo.fmpq_poly_to_gfp_poly_raw!(tmp_gfp_poly, gg)
      	ccall((:nmod_poly_rem, libflint), Nothing,
        	    (Ref{fpPolyRingElem}, Ref{fpPolyRingElem}, Ref{fpPolyRingElem}, Ptr{Nothing}),
          	  tmp_gfp_poly, tmp_gfp_poly, g, pointer_from_objref(F)+sizeof(ZZRingElem))
      	return coeff(tmp_gfp_poly, 0)
			end
    end

    z.header = MapHeader{AbsSimpleNumFieldOrder, fpField}(O, F, _image)
    return z
  end

  function NfOrdToGFMor(O::AbsSimpleNumFieldOrder, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
    z = NfOrdToGFMor()
    z.P = P
    p = minimum(P)
    a, g, b = get_residue_field_data(P)
    psmall = Int(p)
		n = degree(O)
    F = Native.GF(psmall, cached = false)
    imageofbasis = Vector{fpFieldElem}(undef, n)
    for i in 1:n
      imageofbasis[i] = F(b[i][1, 1])
    end

		local _image
		let imageofbasis = imageofbasis, F = F, n = n
   		function _image(x::AbsSimpleNumFieldOrderElem)
      	v = coordinates(x, copy = false)
      	tempF = zero(UInt)
      	for i in 1:n
          tempF += mul_mod(imageofbasis[i].data, v[i], F)
       	end
      	return F(tempF)
			end
    end

    z.header = MapHeader{AbsSimpleNumFieldOrder, fpField}(O, F, _image)
    return z
  end
end

function preimage(f::NfOrdToGFMor, a::fpFieldElem)
  return domain(f)(a.data)
end

Mor(O::AbsSimpleNumFieldOrder, F::fpField, g::fpPolyRingElem) = NfOrdToGFMor(O, F, g)



mutable struct NfOrdToGFFmpzMor <: Map{AbsSimpleNumFieldOrder, Nemo.FpField, HeckeMap, NfOrdToGFFmpzMor}
  header::MapHeader{AbsSimpleNumFieldOrder, Nemo.FpField}
  poly_of_the_field::FpPolyRingElem
  P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

  function NfOrdToGFFmpzMor()
    r = new()
    return r
  end

  function NfOrdToGFFmpzMor(O::AbsSimpleNumFieldOrder, F::Nemo.FpField, g::FpPolyRingElem)
    # assume that F = F_p[X]/(g) and g is a factor of f mod p of degree 1

    z = new()
    tmp_gfp_poly = parent(g)()
    z.poly_of_the_field = g
		local _image
    let g = g, tmp_gfp_poly = tmp_gfp_poly, O = O, F = F
    	function _image(x::AbsSimpleNumFieldOrderElem)
      	gg = parent(nf(O).pol)(elem_in_nf(x))::QQPolyRingElem
      	Nemo.fmpq_poly_to_gfp_fmpz_poly_raw!(tmp_gfp_poly, gg)
				rem!(tmp_gfp_poly, tmp_gfp_poly, g)
      	return coeff(tmp_gfp_poly, 0)
			end
    end

    z.header = MapHeader{AbsSimpleNumFieldOrder, Nemo.FpField}(O, F, _image)
    return z
  end

  function NfOrdToGFFmpzMor(O::AbsSimpleNumFieldOrder, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
    z = NfOrdToGFFmpzMor()
    z.P = P
    p = minimum(P)
    a, g, b = get_residue_field_data(P)
		n = degree(O)
    F = Native.GF(p, cached = false)
    imageofbasis = Vector{Nemo.FpFieldElem}(undef, n)
    for i in 1:n
      imageofbasis[i] = F(b[i][1, 1])
    end

    tempF = F()
		local _image
		let tempF = tempF, imageofbasis = imageofbasis, F = F, n = n
   		function _image(x::AbsSimpleNumFieldOrderElem)
      	v = coordinates(x, copy = false)
      	zz = zero(F)
      	for i in 1:n
          mul!(tempF, imageofbasis[i], v[i])
        	add!(zz, zz, tempF)
      	end
      	return zz
			end
    end

    z.header = MapHeader{AbsSimpleNumFieldOrder, Nemo.FpField}(O, F, _image)
    return z
  end
end

function preimage(f::NfOrdToGFFmpzMor, a::Nemo.FpFieldElem)
  return domain(f)(lift(a))
end

Mor(O::AbsSimpleNumFieldOrder, F::Nemo.FpField, h::FpPolyRingElem) = NfOrdToGFFmpzMor(O, F, h)

###############################################################################
#
#  Residue field with FqField (fq_default)
#
################################################################################

mutable struct NfOrdToFqFieldMor <: Map{AbsSimpleNumFieldOrder, FqField, HeckeMap, NfOrdToFqFieldMor}
  header::MapHeader{AbsSimpleNumFieldOrder, FqField}
  poly_of_the_field::FqPolyRingElem
  P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}
  fastpath::Bool
  # Some temporary variables
  tmp_gfp_fmpz_poly::FqPolyRingElem
  t_fmpz_poly::ZZPolyRingElem
  t_fmpz::ZZRingElem
  a::AbsSimpleNumFieldElem

  function NfOrdToFqFieldMor()
    z = new()
    return z
  end

  function NfOrdToFqFieldMor(O::AbsSimpleNumFieldOrder, F::FqField, g::FqPolyRingElem)
    # assume that F = F_p[X]/(g) and g is a factor of f mod p

    z = new()
    z.fastpath = true
    p = characteristic(F)
    z.tmp_gfp_fmpz_poly = parent(g)()
    z.t_fmpz_poly = ZZPolyRingElem()
    z.t_fmpz = ZZRingElem()

    z.a = gen(nf(O))
    z.poly_of_the_field = g

    z.header = MapHeader{AbsSimpleNumFieldOrder, FqField}(O, F)# _image, _preimage)

    return z
  end

end

#TODO: Less allocations
function NfOrdToFqFieldMor(O::AbsSimpleNumFieldOrder, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  z = NfOrdToFqFieldMor()
  z.fastpath = false
  z.P = P
  a, g, b = get_residue_field_data(P)
  p = minimum(P)
  R = GF(p, cached = false)
  Rx, x = polynomial_ring(R, "_\$", cached = false)
  F, = Nemo._residue_field(Rx(g), "_\$", check = false)
  d = degree(g)
  n = degree(O)
  imageofbasis = Vector{FqFieldElem}(undef, n)
  powers = Vector{AbsSimpleNumFieldElem}(undef, d)
  c = Rx()

  for i in 1:n
    ib = F()
    @assert d == ncols(b[i])
    for j in 1:d
      setcoeff!(c, j - 1, R(b[i][1, j]))
    end
    #@show c
    #@show typeof(c)
    #@show F.forwardmap(c)
    #ccall((:fq_set, libflint), Nothing, (Ref{FqPolyRepFieldElem}, Ref{FpPolyRingElem}, Ref{FqPolyRepField}), ib, c, F)
    imageofbasis[i] = F.forwardmap(c)
  end

  powers[1] = a.elem_in_nf
  for i in 2:d
    powers[i] = powers[i - 1] * a.elem_in_nf
  end

  tempF = F()

  function _image(x::AbsSimpleNumFieldOrderElem)
    v = coordinates(x, copy = false)
    zz = zero(F)
    for i in 1:n
      ccall((:fq_default_mul_fmpz, libflint), Nothing,
            (Ref{FqFieldElem}, Ref{FqFieldElem}, Ref{ZZRingElem}, Ref{FqField}),
            tempF, imageofbasis[i], v[i], F)
      add!(zz, zz, tempF)
    end
    return zz
  end

  function _preimage(y::FqFieldElem)
    zz = O()
    zz.elem_in_nf = nf(O)(lift(ZZ, coeff(y, 0)))
    for i in 2:d
      add!(zz.elem_in_nf, zz.elem_in_nf, powers[i - 1] * lift(ZZ, coeff(y, i - 1)))
    end
    if is_defining_polynomial_nice(nf(O)) && contains_equation_order(O)
      zz.elem_in_nf = mod(zz.elem_in_nf, p)
    else
      zz = mod(zz, p)
    end
    @assert _image(zz) == y
    return zz
  end

  z.header = MapHeader{AbsSimpleNumFieldOrder, FqField}(O, F, _image, _preimage)
  return z
end

function image(f::NfOrdToFqFieldMor, x::AbsSimpleNumFieldOrderElem)
  if f.fastpath
    F = codomain(f)
    O = domain(f)
    u = F()
    gg = parent(nf(O).pol)(elem_in_nf(x, copy = false))::QQPolyRingElem
    Nemo.fmpq_poly_to_fq_default_poly_raw!(f.tmp_gfp_fmpz_poly, gg, f.t_fmpz_poly, f.t_fmpz)
    ccall((:fq_default_poly_rem, libflint), Nothing, (Ref{FqPolyRingElem}, Ref{FqPolyRingElem}, Ref{FqPolyRingElem}, Ref{Nemo.FqField}), f.tmp_gfp_fmpz_poly, f.tmp_gfp_fmpz_poly, f.poly_of_the_field, f.tmp_gfp_fmpz_poly.parent.base_ring)
    res = F.forwardmap(f.tmp_gfp_fmpz_poly)::FqFieldElem
    @assert parent(res) === F
    return res
    #return u
  else
    res = f.header.image(x)::FqFieldElem
    @assert parent(res) === codomain(f)
    return res
  end
end

global _debug = []

function preimage(f::NfOrdToFqFieldMor, x::FqFieldElem)
  @assert parent(x) === codomain(f)
  if f.fastpath
    O = domain(f)
    F = codomain(f)
    zz = nf(O)()

    a = f.a
    # TODO: Do something more clever here
    for i in 0:degree(F)-1
      zz = zz + lift(ZZ, coeff(x, i))*a^i
    end

    res = O(zz, false)::AbsSimpleNumFieldOrderElem
    return res
  else
    @assert isdefined(f.header, :preimage)
    res =  f.header.preimage(x)::AbsSimpleNumFieldOrderElem
    return res
  end
end

Mor(O::AbsSimpleNumFieldOrder, F::Nemo.FqField, h::FqPolyRingElem) = NfOrdToFqFieldMor(O, F, h)

################################################################################
#
#  Extend to number field
#
################################################################################

mutable struct NfToFinFldMor{T} <: Map{AbsSimpleNumField, T, HeckeMap, NfToFinFldMor{T}}
  header::MapHeader{AbsSimpleNumField, T}

  function NfToFinFldMor{T}() where T
    r = new{T}()
    r.header = MapHeader{AbsSimpleNumField, T}()
    return r
  end
end


function extend(f::T, K::AbsSimpleNumField) where T <: Union{NfOrdToFqNmodMor, NfOrdToFqMor, NfOrdToGFMor, NfOrdToGFFmpzMor, NfOrdToFqFieldMor}
  nf(domain(f)) != K && error("Number field is not the number field of the order")

  z = NfToFinFldMor{typeof(codomain(f))}()

  z.header.domain = K
  z.header.codomain = f.header.codomain

  pia = anti_uniformizer(f.P)
  O = domain(f)
  P = f.P

  _image = function(x::AbsSimpleNumFieldElem)
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

@doc raw"""
    extend_easy(f::Hecke.NfOrdToFqNmodMor, K::AbsSimpleNumField) -> NfToFqNmodMor

For a residue field map from a prime ideal, extend the domain of the map
to the entire field.
Requires the prime ideal to be coprime to the index, unramified and
over a small integer. The resulting map can very efficiently be
evaluated using `image(map, elem)`.
The resulting map can be applied to
  * `AbsSimpleNumFieldElem`
  * `FacElem{AbsSimpleNumFieldElem}`
Will throw a `BadPrime` exception if applied to an element in the
field with a $p$ in the denominator. In the case of `FacElem`, zero
is also not permitted (and will produce a `BadPrime` error).
"""
function extend_easy(f::Hecke.NfOrdToFqNmodMor, K::AbsSimpleNumField)
  nf(domain(f)) != K && error("Number field is not the number field of the order")
  return NfToFqNmodMor_easy(f, K)
end

#a stop-gap, mainly for non-monic polynomials
function extend_easy(f::Hecke.NfOrdToFqMor, K::AbsSimpleNumField)
  return NfToFqMor_easy(f, K)
end

function extend_easy(f::Hecke.NfOrdToGFMor, K::AbsSimpleNumField)
  return NfToGFMor_easy(f, K)
end

function extend_easy(f::Hecke.NfOrdToGFFmpzMor, K::AbsSimpleNumField)
  return NfToGFFmpzMor_easy(f, K)
end

function extend_easy(f::Hecke.NfOrdToFqFieldMor, K::AbsSimpleNumField)
  return NfToFqFieldMor_easy(f, K)
end

mutable struct NfToFqFieldMor_easy <: Map{AbsSimpleNumField, FqField, HeckeMap, NfToFqFieldMor_easy}
  header::MapHeader{AbsSimpleNumField, FqField}
  Fq::FqField
  s::FqFieldElem
  t::FqPolyRingElem
  function NfToFqFieldMor_easy(a::Map, k::AbsSimpleNumField)
    r = new()
    r.Fq = codomain(a)
    r.header = MapHeader(k, r.Fq)
    r.s = r.Fq()
    r.t = polynomial_ring(prime_field(r.Fq), cached = false)[1]()
    return r
  end
end

function image(mF::NfToFqFieldMor_easy, a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, quo::Int = 0)
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
      _nf_to_fq!(s, k, Fq)#, t)
      if iszero(s)
        throw(BadPrime(1))
      end
      if vv < 0
        ccall((:fq_default_inv, libflint), Nothing, (Ref{FqFieldElem}, Ref{FqFieldElem}, Ref{FqField}), s, s, Fq)
        vv = -vv
      end
      ccall((:fq_default_pow_ui, libflint), Nothing, (Ref{FqFieldElem}, Ref{FqFieldElem}, Int, Ref{FqField}), s, s, vv, Fq)
      mul!(q, q, s)
    end
  end
  return q
end

function image(mF::NfToFqFieldMor_easy, a::AbsSimpleNumFieldElem, n_quo::Int = 0)
  Fq = mF.Fq
  q = Fq()
  if denominator(a) % characteristic(Fq) == 0
    throw(BadPrime(characteristic(Fq)))
  end
  _nf_to_fq!(q, a, Fq)#, mF.t)
  return q
end

mutable struct NfToFqMor_easy <: Map{AbsSimpleNumField, FqPolyRepField, HeckeMap, NfToFqMor_easy}
  header::MapHeader{AbsSimpleNumField, FqPolyRepField}
  Fq::FqPolyRepField
  s::FqPolyRepFieldElem
  t::FpPolyRingElem
  function NfToFqMor_easy(a::Map, k::AbsSimpleNumField)
    r = new()
    r.Fq = codomain(a)
    r.header = MapHeader(k, r.Fq)
    r.s = r.Fq()
    r.t = polynomial_ring(Native.GF(characteristic(r.Fq), cached = false), cached = false)[1]()
    return r
  end
end

function image(mF::NfToFqMor_easy, a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, quo::Int = 0)
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
        ccall((:fq_inv, libflint), Nothing, (Ref{FqPolyRepFieldElem}, Ref{FqPolyRepFieldElem}, Ref{FqPolyRepField}), s, s, Fq)
        vv = -vv
      end
      ccall((:fq_pow_ui, libflint), Nothing, (Ref{FqPolyRepFieldElem}, Ref{FqPolyRepFieldElem}, Int, Ref{FqPolyRepField}), s, s, vv, Fq)
      mul!(q, q, s)
    end
  end
  return q
end

function image(mF::NfToFqMor_easy, a::AbsSimpleNumFieldElem, n_quo::Int = 0)
  Fq = mF.Fq
  q = Fq()
  if denominator(a) % characteristic(Fq) == 0
    throw(BadPrime(characteristic(Fq)))
  end
  _nf_to_fq!(q, a, Fq, mF.t)
  return q
end


mutable struct NfToFqNmodMor_easy <: Map{AbsSimpleNumField, fqPolyRepField, HeckeMap, NfToFqNmodMor_easy}
  header::MapHeader{AbsSimpleNumField, fqPolyRepField}
  Fq::fqPolyRepField
  s::fqPolyRepFieldElem
  t::fpPolyRingElem
  function NfToFqNmodMor_easy(a::Map, k::AbsSimpleNumField)
    r = new()
    r.Fq = codomain(a)
    r.header = MapHeader(k, r.Fq)
    r.s = r.Fq()
    r.t = polynomial_ring(Native.GF(UInt(characteristic(r.Fq)), cached=false), cached=false)[1]()
    return r
  end
end

function image(mF::NfToFqNmodMor_easy, a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, quo::Int = 0)
  Fq = mF.Fq
  q = one(Fq)
  t = mF.t
  s = mF.s
  oFq = order(Fq) # ZZRingElem
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
        ccall((:fq_nmod_inv, libflint), Nothing, (Ref{fqPolyRepFieldElem}, Ref{fqPolyRepFieldElem}, Ref{fqPolyRepField}), s, s, Fq)
      end
      if quo != 0
        ccall((:fq_nmod_pow_ui, libflint), Nothing, (Ref{fqPolyRepFieldElem}, Ref{fqPolyRepFieldElem}, Int, Ref{fqPolyRepField}), s, s, vv, Fq)
      else
        ccall((:fq_nmod_pow, libflint), Nothing, (Ref{fqPolyRepFieldElem}, Ref{fqPolyRepFieldElem}, Ref{ZZRingElem}, Ref{fqPolyRepField}), s, s, v, Fq)
      end
      mul!(q, q, s)
    end
  end
  return q
end

function image(mF::NfToFqNmodMor_easy, a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, D::Vector, cached::Bool, quo::Int = 0)
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
        Nemo.nf_elem_to_gfp_poly!(t, k)
        D[i] = zero(parent(t))
        set!(D[i], t)
      end
    end

    if (quo != 0 && vv != 0) || !iszero(v)
      if cached
        s = zero(Fq)
        ccall((:fq_nmod_set, libflint), Nothing,
          (Ref{fqPolyRepFieldElem}, Ref{fpPolyRingElem}, Ref{fqPolyRepField}), s, D[i], Fq)
        _reduce(s)
      else
        Nemo.nf_elem_to_gfp_poly!(t, k)
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
          (Ref{fqPolyRepFieldElem}, Ref{fpPolyRingElem}, Ref{fqPolyRepField}), s, D[i], Fq)
        _reduce(s)
      end
      if iszero(s)
        throw(BadPrime(1))
      end

      if inver
        ccall((:fq_nmod_inv, libflint), Nothing, (Ref{fqPolyRepFieldElem}, Ref{fqPolyRepFieldElem}, Ref{fqPolyRepField}), s, s, Fq)
      end
      if quo != 0
        ccall((:fq_nmod_pow_ui, libflint), Nothing, (Ref{fqPolyRepFieldElem}, Ref{fqPolyRepFieldElem}, Int, Ref{fqPolyRepField}), s, s, vv, Fq)
      else
        ccall((:fq_nmod_pow, libflint), Nothing, (Ref{fqPolyRepFieldElem}, Ref{fqPolyRepFieldElem}, Ref{ZZRingElem}, Ref{fqPolyRepField}), s, s, v, Fq)
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

function image(mF::NfToFqNmodMor_easy, a::AbsSimpleNumFieldElem, n_quo::Int = 0)
  Fq = mF.Fq
  q = Fq()
  if denominator(a) % characteristic(Fq) == 0
    throw(BadPrime(characteristic(Fq)))
  end
  _nf_to_fq!(q, a, Fq, mF.t)
  return q
end

function _nf_to_gfp_elem(b::AbsSimpleNumFieldElem, a_tmp::fpPolyRingElem, def_pol::fpPolyRingElem)
  Nemo.nf_elem_to_gfp_poly!(a_tmp, b)
  rem!(a_tmp, a_tmp, def_pol)
  return coeff(a_tmp, 0)
end

function _nf_to_gfp_elem(b::AbsSimpleNumFieldElem, a_tmp::FpPolyRingElem, def_pol::FpPolyRingElem)
  Nemo.nf_elem_to_gfp_fmpz_poly!(a_tmp, b)
  rem!(a_tmp, a_tmp, def_pol)
  return coeff(a_tmp, 0)
end

mutable struct NfToGFMor_easy <: Map{AbsSimpleNumField, fpField, HeckeMap, NfToGFMor_easy}
  header::MapHeader{AbsSimpleNumField, fpField}
  Fq::fpField
  defining_pol::fpPolyRingElem
  s::fpFieldElem
  t::fpPolyRingElem
  function NfToGFMor_easy(a::NfOrdToGFMor, k::AbsSimpleNumField)
    r = new()
    r.Fq = codomain(a)
    r.defining_pol = a.poly_of_the_field
    r.header = MapHeader(k, r.Fq)
    r.s = r.Fq()
    r.t = zero(parent(r.defining_pol))
    return r
  end
end

function image(mF::NfToGFMor_easy, a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, quo::Int = 0)
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

function image(mF::NfToGFMor_easy, a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, D::Vector, cached::Bool, quo::Int = 0)
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
      Nemo.nf_elem_to_gfp_poly!(t, k)
      set!(D[i], t)
    end

    if !iszero(vv)
      if cached
        s = evaluate_raw(D[i], evaluateat)
      else
        Nemo.nf_elem_to_gfp_poly!(t, k)
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

function image(mF::NfToGFMor_easy, a::AbsSimpleNumFieldElem, n_quo::Int = 0)
  Fq = mF.Fq
  p = mF.defining_pol
  t = mF.t
  if denominator(a) % characteristic(Fq) == 0
    throw(BadPrime(characteristic(Fq)))
  end
  return _nf_to_gfp_elem(a, t, p)
end

function image(mF::NfToGFMor_easy, a::AbsSimpleNumFieldElem, D::Vector, cached::Bool, n_quo::Int = 0)
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
    Nemo.nf_elem_to_gfp_poly!(t, a)
    D[1] = deepcopy(t)
    #rem!(t, t, p)
    #s = coeff(t, 0)
    s = evaluate_raw(t, evaluateat)
  end
  return s
end


mutable struct NfToGFFmpzMor_easy <: Map{AbsSimpleNumField, Nemo.FpField, HeckeMap, NfToGFFmpzMor_easy}
  header::MapHeader{AbsSimpleNumField, Nemo.FpField}
  Fq::Nemo.FpField
  defining_pol::Nemo.FpPolyRingElem
  s::Nemo.FpFieldElem
  t::Nemo.FpPolyRingElem
  function NfToGFFmpzMor_easy(a::NfOrdToGFFmpzMor, k::AbsSimpleNumField)
    r = new()
    r.Fq = codomain(a)
    r.header = MapHeader(k, r.Fq)
    r.s = r.Fq()
    r.defining_pol = a.poly_of_the_field
    r.t = zero(parent(a.poly_of_the_field))
    return r
  end
end

function image(mF::NfToGFFmpzMor_easy, a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, quo::Int = 0)
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

function image(mF::NfToGFFmpzMor_easy, a::AbsSimpleNumFieldElem, n_quo::Int = 0)
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

mutable struct AbsOrdToAlgAssMor{S, T} <: Map{S, StructureConstantAlgebra{T}, HeckeMap, AbsOrdToAlgAssMor}
  header::MapHeader

  function AbsOrdToAlgAssMor{S, T}(O::S, A::StructureConstantAlgebra{T}, _image::Function, _preimage::Function) where {S <: Union{ AbsNumFieldOrder, AlgAssAbsOrd }, T}
    z = new{S, T}()
    z.header = MapHeader(O, A, _image, _preimage)
    return z
  end
end

function AbsOrdToAlgAssMor(O::Union{ AbsNumFieldOrder, AlgAssAbsOrd }, A::StructureConstantAlgebra{T}, _image, _preimage) where {T}
  return AbsOrdToAlgAssMor{typeof(O), T}(O, A, _image, _preimage)
end


# Helper



function mul_mod(x::UInt, y::ZZRingElem, R)
  d = ccall((:fmpz_fdiv_ui, libflint), UInt, (Ref{ZZRingElem}, UInt), y, R.n)
  r = ccall((:n_mulmod2_preinv, libflint), UInt, (UInt, UInt, UInt, UInt),
             x, d, R.n, R.ninv)
  return r
end

function evaluate_raw(x::fpPolyRingElem, y::fpFieldElem)
  z = ccall((:nmod_poly_evaluate_nmod, libflint), UInt,
              (Ref{fpPolyRingElem}, UInt), x, y.data)
  return parent(y)(z)
end

function fmpz_mod_ui(x::ZZRingElem, y::UInt)
  return ccall((:fmpz_fdiv_ui, libflint), UInt, (Ref{ZZRingElem}, UInt), x, y)
end


