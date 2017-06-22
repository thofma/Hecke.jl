export extend

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

function show(io::IO, h::NfToNfMor)
  if domain(h) == codomain(h)
    println(io, "Automorphism of ", domain(h))
  else
    println(io, "Injection of ", domain(h), " into ", codomain(h))
  end
  println(io, "defined by ", gen(domain(h)), " -> ", h.prim_img)
end

type NfOrdToFqNmodMor <: Map{NfOrd, FqNmodFiniteField}
  header::MapHeader{NfOrd, FqNmodFiniteField}
  poly_of_the_field::nmod_poly
  P::NfOrdIdl

  function NfOrdToFqNmodMor()
    r = new()
    r.header = MapHeader{NfOrd, FqNmodFiniteField}()
    return r
  end

  function NfOrdToFqNmodMor(O::NfOrd, F::FqNmodFiniteField, g::nmod_poly)
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

    z.header = MapHeader{NfOrd, FqNmodFiniteField}(O, F, _image, _preimage)

    return z
  end

  function NfOrdToFqNmodMor(O::NfOrd, P::NfOrdIdl)
    z = new()

    @assert abs(minimum(P)) <= typemax(Int)

    p = Int(abs(minimum(P)))

    R = ResidueRing(FlintZZ, p)

    OP = quoringalg(O, P, p)
    x = quoelem(OP, zero(O))
    f = PolynomialRing(R, "x")[1]()
    d = length(OP.basis)

    while true
      r = rand(0:p-1, d)
      x = quoelem(OP, dot([ x for x in OP.basis], r))
      f = minpoly(x)
      if degree(f) == d
        break
      end
    end

    F = FqNmodFiniteField(f, Symbol("_\$"))

    M2 = MatrixSpace(R, degree(O), d)()

    for i in 1:d
      coords = elem_in_basis((x^(i-1)).elem)
      for j in 1:degree(O)
        M2[j, i] = coords[j]
      end
    end

    M3 = MatrixSpace(R, degree(O), degree(O))()

    for i in 1:degree(O)
      coords = elem_in_basis(mod(basis(O)[i], OP.ideal))
      for j in 1:degree(O)
        M3[j, i] = coords[j]
      end
    end

    X = _solve_unique(M3, M2)

    #for i in 1:degree(O)
    #  @assert quoelem(OP, basis(O)[i]) == quoelem(OP, dot([(x^j).elem for j in 0:d-1], _lift([ X[j, i] for j in 1:d ])))
    #end

    Mats = MatrixSpace(R, degree(O), 1)

    function _image(y::NfOrdElem)
      co = Mats()
      coeff = elem_in_basis(mod(y, P))

      for i in 1:degree(O)
        co[i, 1] = coeff[i]
      end

      co = X*co

      z = F(lift(co[1, 1])) # totally inefficient

      for i in 2:rows(co)
        z = z  + F(lift(co[i, 1]))*gen(F)^(i-1)
      end

      return z
    end

    function _preimage(y::fq_nmod)
      z = nf(O)()

      for i in 0:degree(F)-1
        z = z + _get_coeff_raw(y, i)*(x.elem.elem_in_nf)^i
      end

      return mod(O(z, false), P)
    end

    z.header = MapHeader{NfOrd, FqNmodFiniteField}(O, F, _image, _preimage)
    z.P = P

    return z
  end

  function NfOrdToFqNmodMor(O::NfOrd, F::FqNmodFiniteField, y::fq_nmod)
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

    z.header = MapHeader{NfOrd, FqNmodFiniteField}(O, F, _image, _preimage)

    return z
  end
end

type NfOrdQuoMap <: Map{NfOrd, NfOrdQuoRing}
  header::MapHeader{NfOrd, NfOrdQuoRing}

  function NfOrdQuoMap(O::NfOrd, Q::NfOrdQuoRing)
    z = new()

    _image = function (x::NfOrdElem)
      return Q(x)
    end

    _preimage = function (x::NfOrdQuoRingElem)
      return x.elem
    end

    z.header = MapHeader(O, Q, _image, _preimage)
    return z
  end
end

function Mor(O::NfOrd, F::FqNmodFiniteField, y::fq_nmod)
  return NfOrdToFqNmodMor(O, F, y)
end

function Mor(O::NfOrd, F::FqNmodFiniteField, h::nmod_poly)
  return NfOrdToFqNmodMor(O, F, h)
end

type NfToFqNmodMor <: Map{AnticNumberField, FqNmodFiniteField}
  header::MapHeader

  function NfToFqNmodMor()
    r = new()
    r.header = MapHeader{AnticNumberField, FqNmodFiniteField}()
    return r
  end
end

function extend(f::NfOrdToFqNmodMor, K::AnticNumberField)
  nf(domain(f)) != K && error("Number field is not the number field of the order")

  z = NfToFqNmodMor()
  z.header.domain = K
  z.header.codomain = f.header.codomain

  p = characteristic(z.header.codomain)
  Zx = PolynomialRing(FlintIntegerRing(), "x")[1]
  y = f(NfOrdElem(domain(f), gen(K)))
  pia = anti_uniformizer(f.P)
  O = domain(f)
  P = f.P

  #function _image(x::nf_elem)
  #  g = parent(K.pol)(x)
  #  u = inv(z.header.codomain(den(g)))

  #  g = Zx(den(g)*g)
  #  return u*evaluate(g, y)
  #end
  function _image(x::nf_elem)
    m = den(x, domain(f))
    l = valuation(m, P)
    if l == 0
      return f(O(m*x))//f(O(m))
    else
      return f(O(pia^l * m * x))//f(O(pia^l * m))
    end
  end

  function _preimage(x::fq_nmod)
    return elem_in_nf(preimage(f, x))
  end

  z.header.image = _image
  z.header.preimage = _preimage

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

function (f::NfOrdToFqNmodMor)(p::PolyElem{NfOrdElem})
  F = codomain(f)
  Fx,_ = PolynomialRing(F, "_\$")

  ar = NfOrdElem[ coeff(p, i) for i in 0:degree(p) ]

  z = Fx(map(f, ar))

  return z
end

# this is super slow
# improve
function (f::NfOrdQuoMap)(I::NfOrdIdl)
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


function (f::NfOrdQuoMap)(p::PolyElem{NfOrdElem})
  F = codomain(f)
  Fx,_ = PolynomialRing(F, "_\$")

  ar = NfOrdElem[ coeff(p, i) for i in 0:degree(p) ]

  z = Fx(map(f, ar))

  return z
end

base_ring(::NfOrd) = Union{}

Nemo.needs_parentheses(::NfOrdElem) = true

Nemo.isnegative(::NfOrdElem) = false

# Assume A is mxd, B is mxl and there is a unique X of size lxd
# with A = B * X
# this function will find it!
function _solve_unique(A::nmod_mat, B::nmod_mat)
  X = MatrixSpace(base_ring(A), cols(B), rows(A))()

  #println("solving\n $A \n = $B * X")

  r, per, L, U = lufact(B) # P*M1 = L*U
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

  #println("I got Y: $Y")

  #println("L*Y : $(L*Y)")
  #println("need Ap: $Ap")

  @assert Ap == L*Y

  #println("solving \n $Y \n = $U * X")

  YY = submat(Y, 1:r, 1:cols(Y))
  UU = submat(U, 1:r, 1:r)
  X = inv(UU)*YY

  @assert Y == U * X

  @assert B*X == A
  return X
end

