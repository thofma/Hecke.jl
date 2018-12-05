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

    function _image(x::NfOrdElem)
      u = F()
      gg = parent(nf(O).pol)(elem_in_nf(x))::fmpq_poly
      fmpq_poly_to_gfp_poly_raw!(tmp_gfp_poly, gg)
      ccall((:nmod_poly_rem, :libflint), Nothing,
            (Ref{gfp_poly}, Ref{gfp_poly}, Ref{gfp_poly}, Ptr{Nothing}),
            tmp_gfp_poly, tmp_gfp_poly, g, pointer_from_objref(F)+sizeof(fmpz))
      ccall((:fq_nmod_set, :libflint), Nothing,
            (Ref{fq_nmod}, Ref{gfp_poly}, Ref{FqNmodFiniteField}),
            u, tmp_gfp_poly, F)
      ccall((:fq_nmod_reduce, :libflint), Nothing,
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
      _mod!(zz.elem_in_nf, p)
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
      @assert d == cols(b[i])
      for j in 1:d
        setcoeff!(c, j - 1, b[i][1, j])
      end
      ccall((:fq_nmod_set, :libflint), Nothing, (Ref{fq_nmod}, Ref{gfp_poly}, Ref{FqNmodFiniteField}), ib, c, F)
      imageofbasis[i] = ib
    end

    powers[1] = a.elem_in_nf
    for i in 2:d
      powers[i] = powers[i - 1] * a.elem_in_nf
    end

    tempF = F()

    function _image(x::NfOrdElem)
      v = elem_in_basis(x, Val{false})
      zz = zero(F)
      for i in 1:n
        ccall((:fq_nmod_mul_fmpz, :libflint), Nothing,
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
      _mod!(zz.elem_in_nf, p)
      return zz
    end

    z.header = MapHeader{NfOrd, FqNmodFiniteField}(O, F, _image, _preimage)
    return z
  end
end

_mod!(x::nf_elem, y::Integer) = _mod!(x, fmpz(y))

function _mod!(x::nf_elem, y::fmpz)
  zden = denominator(x)
  zden2 = denominator(x)
  mul!(x, x, zden)
  mul!(zden, zden, y)
  mod!(x, zden)
  divexact!(x, x, zden2)
  return x
end

# S is the type of the order, T the type of the ideal and U the elem_type of the order, which define the quotient ring
mutable struct AbsOrdQuoMap{S, T, U} <: Map{S, AbsOrdQuoRing{S, T}, HeckeMap, AbsOrdQuoMap}
  header::MapHeader{S, AbsOrdQuoRing{S, T}}

  function AbsOrdQuoMap{S, T, U}(O::S, Q::AbsOrdQuoRing{S, T}) where {S, T, U}
    z = new()

    _image = function (x::U)
      return Q(x)
    end

    _preimage = function (x::AbsOrdQuoRingElem{S, T, U})
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

function Mor(K::AnticNumberField, L::AnticNumberField, y::nf_elem)
  z = NfToNfMor(K, L, y)
  return z
end

function _get_coeff_raw(x::fq_nmod, i::Int)
  u = ccall((:nmod_poly_get_coeff_ui, :libflint), UInt, (Ref{fq_nmod}, Int), x, i)
  return u
end

function _get_coeff_raw(x::fq, i::Int)
  t = FlintIntegerRing()
  ccall((:fmpz_poly_get_coeff_fmpz, :libflint), Nothing, (Ref{fmpz}, Ref{fq}, Int), t, x, i)
  return t
end

# this is super slow
# improve
function (f::NfOrdQuoMap)(I::NfOrdIdl)
  O = domain(f)
  Q = codomain(f)
  B = Q.ideal + I
  nB = norm(B)
  b = basis(B, Val{false})

  z = O()

  nQ = norm(Q.ideal)
  OnQ = ideal(O, nQ)
  range1nQ2 = fmpz(1):nQ^2

  while true
    z = rand!(z, b, range1nQ2)
    #z = sum(rand(range1nQ2) * b[i] for i in 1:degree(O))
    if norm(ideal(O, z) + OnQ) == nB
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

# Assume A is mxd, B is mxl and there is a unique X of size lxd
# with A = B * X
# this function will find it!
function _solve_unique(A::nmod_mat, B::nmod_mat)
  X = zero_matrix(base_ring(A), cols(B), rows(A))

  #println("solving\n $A \n = $B * X")
  r, per, L, U = lu(B) # P*M1 = L*U

  inv!(per)

  @assert B == per*L*U
  Ap = inv(per)*A
  Y = parent(A)()

  #println("first solve\n $Ap = $L * Y")

  for i in 1:cols(Y)
    for j in 1:rows(Y)
      s = Ap[j, i]
      for k in 1:j-1
        s = s - Y[k, i]*L[j, k]
      end
      Y[j, i] = s
    end
  end

  @assert Ap == L*Y

  #println("solving \n $Y \n = $U * X")

  YY = sub(Y, 1:r, 1:cols(Y))
  UU = sub(U, 1:r, 1:r)
  X = _inv(UU)*YY

  @assert Y == U * X

  @assert B*X == A
  return X
end

function _solve_unique(A::Generic.Mat{Generic.Res{fmpz}}, B::Generic.Mat{Generic.Res{fmpz}})
  X = zero_matrix(base_ring(A), cols(B), rows(A))

  #println("solving\n $A \n = $B * X")
  r, per, L, U = _lu(B) # P*M1 = L*U
  inv!(per)

  @assert B == per*L*U
  Ap = inv(per)*A
  Y = zero_matrix(base_ring(A), rows(A), cols(A))

  #println("first solve\n $Ap = $L * Y")

  for i in 1:cols(Y)
    for j in 1:rows(Y)
      s = Ap[j, i]
      for k in 1:j-1
        s = s - Y[k, i]*L[j, k]
      end
      Y[j, i] = s
    end
  end

  @assert Ap == L*Y

  #println("solving \n $Y \n = $U * X")

  YY = sub(Y, 1:r, 1:cols(Y))
  UU = sub(U, 1:r, 1:r)
  X = _inv(UU)*YY

  @assert Y == U * X

  @assert B*X == A
  return X
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
    @assert d == cols(b[i])
    for j in 1:d
      setcoeff!(c, j - 1, b[i][1, j])
    end
    ccall((:fq_set, :libflint), Nothing, (Ref{fq}, Ref{gfp_fmpz_poly}, Ref{FqFiniteField}), ib, c, F)
    imageofbasis[i] = ib
  end

  powers[1] = a.elem_in_nf
  for i in 2:d
    powers[i] = powers[i - 1] * a.elem_in_nf
  end

  tempF = F()

  function _image(x::NfOrdElem)
    v = elem_in_basis(x, Val{false})
    zz = zero(F)
    for i in 1:n
      ccall((:fq_mul_fmpz, :libflint), Nothing,
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
    _mod!(zz.elem_in_nf, p)
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
    gg = parent(nf(O).pol)(elem_in_nf(x))::fmpq_poly
    fmpq_poly_to_gfp_fmpz_poly_raw!(f.tmp_gfp_fmpz_poly, gg, f.t_fmpz_poly, f.t_fmpz)
    ccall((:fmpz_mod_poly_rem, :libflint), Nothing, (Ref{gfp_fmpz_poly}, Ref{gfp_fmpz_poly}, Ref{gfp_fmpz_poly}), f.tmp_gfp_fmpz_poly, f.tmp_gfp_fmpz_poly, f.poly_of_the_field)
    ccall((:fq_set, :libflint), Nothing, (Ref{fq}, Ref{gfp_fmpz_poly}, Ref{FqFiniteField}), u, f.tmp_gfp_fmpz_poly, F)
    ccall((:fq_reduce, :libflint), Nothing, (Ref{fq}, Ref{FqFiniteField}), u, F)
    return u
  else
    return f.header.image(x)
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

    return O(zz, false)
  else
    @assert isdefined(f.header, :preimage)
    return f.header.preimage(x)
  end
end


function Mor(O::NfOrd, F::FqFiniteField, h::gfp_fmpz_poly)
  return NfOrdToFqMor(O, F, h)
end

function sub(M::Nemo.MatElem{T}, r::UnitRange{<:Integer}, c::UnitRange{<:Integer}) where {T}
  z = similar(M, length(r), length(c))
  for i in 1:length(r)
    for j in 1:length(c)
      z[i, j] = M[r[i], c[j]]
    end
  end
  return z
end

_inv(a::nmod_mat) = inv(a)

function _inv(a::MatElem{Generic.Res{fmpz}})
  b, d = inv(a)
  return divexact(b, d)
end

mutable struct NfToFqNmodMor <: Map{AnticNumberField, FqNmodFiniteField, HeckeMap, NfToFqNmodMor}
  header::MapHeader{AnticNumberField, FqNmodFiniteField}

  function NfToFqNmodMor()
    r = new()
    r.header = MapHeader{AnticNumberField, FqNmodFiniteField}()
    return r
  end
end

mutable struct NfToFqMor <: Map{AnticNumberField, FqFiniteField, HeckeMap, NfToFqMor}
  header::MapHeader{AnticNumberField, FqFiniteField}

  function NfToFqMor()
    r = new()
    r.header = MapHeader{AnticNumberField, FqFiniteField}()
    return r
  end
end

function extend(f::Union{NfOrdToFqNmodMor, NfOrdToFqMor}, K::AnticNumberField)
  nf(domain(f)) != K && error("Number field is not the number field of the order")

  if f isa NfOrdToFqNmodMor
    z = NfToFqNmodMor()
  elseif f isa NfOrdToFqMor
    z = NfToFqMor()
  end

  z.header.domain = K
  z.header.codomain = f.header.codomain

  p = characteristic(z.header.codomain)
  Zx = PolynomialRing(FlintIntegerRing(), "x", cached = false)[1]
  y = f(NfOrdElem(domain(f), gen(K)))
  pia = anti_uniformizer(f.P)
  O = domain(f)
  P = f.P

  #function _image(x::nf_elem)
  #  g = parent(K.pol)(x)
  #  u = inv(z.header.codomain(denominator(g)))

  #  g = Zx(denominator(g)*g)
  #  return u*evaluate(g, y)
  #end
  function _image(x::nf_elem)
    m = denominator(x, domain(f))
    l = valuation(m, P)
    if l == 0
      return f(O(m*x))//f(O(m))
    else
      return f(O(pia^l * m * x))//f(O(pia^l * m))
    end
  end

  function _preimage(x::Union{fq, fq_nmod})
    return elem_in_nf(preimage(f, x))
  end

  z.header.image = _image
  z.header.preimage = _preimage

  return z
end

function (f::NfOrdToFqNmodMor)(p::PolyElem{NfOrdElem})
  F = codomain(f)
  Fx,_ = PolynomialRing(F, "_\$", cached = false)

  ar = NfOrdElem[ coeff(p, i) for i in 0:degree(p) ]

  z = Fx(map(f, ar))

  return z
end

function (f::NfOrdToFqMor)(p::PolyElem{NfOrdElem})
  F = codomain(f)
  Fx,_ = PolynomialRing(F, "_\$", cached = false)

  ar = NfOrdElem[ coeff(p, i) for i in 0:degree(p) ]

  z = Fx(map(f, ar))

  return z
end

mutable struct NfOrdToAlgAssMor{T} <: Map{NfOrd, AlgAss{T}, HeckeMap, NfOrdToAlgAssMor}
  header::MapHeader

  function NfOrdToAlgAssMor{T}(O::NfOrd, A::AlgAss{T}, _image::Function, _preimage::Function) where T
    z = new{T}()
    z.header = MapHeader(O, A, _image, _preimage)
    return z
  end
end
