mutable struct NfOrdToFqNmodMor <: Map{NfOrd, FqNmodFiniteField}
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
      ccall((:nmod_poly_rem, :libflint), Void, (Ptr{nmod_poly}, Ptr{nmod_poly}, Ptr{nmod_poly}, Ptr{Void}), &tmp_nmod_poly, &tmp_nmod_poly, &g, pointer_from_objref(F)+sizeof(fmpz))
      ccall((:fq_nmod_set, :libflint), Void, (Ptr{fq_nmod}, Ptr{nmod_poly}, Ptr{FqNmodFiniteField}), &u, &tmp_nmod_poly, &F)

      ccall((:fq_nmod_reduce, :libflint), Void, (Ptr{fq_nmod}, Ptr{FqNmodFiniteField}), &u, &F)
      return u
    end

    function _preimage(x::fq_nmod)
      zz = nf(O)()

      # TODO: Make this better
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

    R = ResidueRing(FlintZZ, p, cached=false)

    OP = quoringalg(O, P, p)
    x = quoelem(OP, zero(O))
    f = PolynomialRing(R, "x", cached = false)[1]()
    d = length(OP.basis)

    while true
      r = rand(0:p-1, d)
      x = quoelem(OP, dot([ x for x in OP.basis], r))
      f = minpoly(x)
      if degree(f) == d
        break
      end
    end

    F = FqNmodFiniteField(f, Symbol("_\$"), false)

    M2 = zero_matrix(R, degree(O), d)

    for i in 1:d
      coords = elem_in_basis((x^(i-1)).elem)
      for j in 1:degree(O)
        M2[j, i] = coords[j]
      end
    end

    M3 = zero_matrix(R, degree(O), degree(O))

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

    function _image(y::NfOrdElem)
      co = zero_matrix(R, degree(O), 1)
      coeff = elem_in_basis(mod(y, P))

      for i in 1:degree(O)
        co[i, 1] = coeff[i]
      end

      co = X*co

      zz = F(lift(co[1, 1])) # totally inefficient

      for i in 2:rows(co)
        zz = zz  + F(lift(co[i, 1]))*gen(F)^(i-1)
      end

      return zz
    end

    function _preimage(y::fq_nmod)
      zz = nf(O)()

      for i in 0:degree(F)-1
        zz = zz + _get_coeff_raw(y, i)*(x.elem.elem_in_nf)^i
      end

      return mod(O(zz, false), P)
    end

    z.header = MapHeader{NfOrd, FqNmodFiniteField}(O, F, _image, _preimage)
    z.P = P

    return z
  end

  function NfOrdToFqNmodMor(O::NfOrd, F::FqNmodFiniteField, y::fq_nmod)
    z = new()

    p = characteristic(F)
    Zx = PolynomialRing(FlintIntegerRing(), "x", cached = false)[1]
    a = gen(nf(O))
    h = Zx()
    t_fq_nmod = F()
    tt_fq_nmod = F()
    t_fmpz = fmpz()

    function _image(x::NfOrdElem)
      g = parent(nf(O).pol)(elem_in_nf(x))

      #pseudocode:
      #u = inv(F(denominator(g)))
      #return u*evaluate(numerator(g), y)

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

mutable struct NfOrdQuoMap <: Map{NfOrd, NfOrdQuoRing}
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

base_ring(::NfOrd) = Union{}

Nemo.needs_parentheses(::NfOrdElem) = true

Nemo.isnegative(::NfOrdElem) = false

# Assume A is mxd, B is mxl and there is a unique X of size lxd
# with A = B * X
# this function will find it!
function _solve_unique(A::nmod_mat, B::nmod_mat)
  X = zero_matrix(base_ring(A), cols(B), rows(A))

  #println("solving\n $A \n = $B * X")
  r, per, L, U = lufact(B) # P*M1 = L*U

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
  r, per, L, U = _lufact(B) # P*M1 = L*U
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

function _lufact!(P::Generic.perm, A::Nemo.MatElem{T}) where {T}
   m = rows(A)
   n = cols(A)
   rank = 0
   r = 1
   c = 1
   R = base_ring(A)
   t = R()
   while r <= m && c <= n
      if A[r, c] == 0
         i = r + 1
         while i <= m
            if !iszero(A[i, c])
               for j = 1:n
                  A[i, j], A[r, j] = A[r, j], A[i, j]
               end
               P[r], P[i] = P[i], P[r]
               break
            end
            i += 1
         end
         if i > m
            c += 1
            continue
         end
      end
      rank += 1
      d = -inv(A[r, c])
      for i = r + 1:m
         q = A[i, c]*d
         for j = c + 1:n
            t = mul!(t, A[r, j], q)
            A[i, j] = addeq!(A[i, j], t)
         end
         A[i, c] = R()
         A[i, rank] = -q
      end
      r += 1
      c += 1
   end
   inv!(P)
   return rank
end

function _lufact(A::Nemo.MatElem{T}, P = PermGroup(rows(A))) where {T}
   m = rows(A)
   n = cols(A)
   P.n != m && error("Permutation does not match matrix")
   p = P()
   R = base_ring(A)
   U = deepcopy(A)
   L = similar(A, m, m)
   rank = _lufact!(p, U)
   for i = 1:m
      for j = 1:n
         if i > j
            L[i, j] = U[i, j]
            U[i, j] = R()
         elseif i == j
            L[i, j] = R(1)
         elseif j <= m
            L[i, j] = R()
         end
      end
   end
   return rank, p, L, U
end


mutable struct NfOrdToFqMor <: Map{NfOrd, FqFiniteField}
  header::MapHeader{NfOrd, FqFiniteField}
  poly_of_the_field::fmpz_mod_poly
  P::NfOrdIdl
  fastpath::Bool
  # Some temporary variables
  tmp_fmpz_mod_poly::fmpz_mod_poly
  t_fmpz_poly::fmpz_poly
  t_fmpz::fmpz
  a::nf_elem

  function NfOrdToFqMor(O::NfOrd, F::FqFiniteField, g::fmpz_mod_poly)
    # assume that F = F_p[X]/(g) and g is a factor of f mod p

    z = new()
    z.fastpath = true
    p = characteristic(F)
    z.tmp_fmpz_mod_poly = parent(g)()
    z.t_fmpz_poly = fmpz_poly()
    z.t_fmpz = fmpz()

    z.a = gen(nf(O))
    z.poly_of_the_field = g

    z.header = MapHeader{NfOrd, FqFiniteField}(O, F)# _image, _preimage)

    return z
  end
  
  function NfOrdToFqMor(O::NfOrd, P::NfOrdIdl)
    z = new()

    z.fastpath = false

    p = abs(minimum(P))

    R = ResidueRing(FlintZZ, p, cached=false)

    OP = quoringalg(O, P, p)
    x = quoelem(OP, zero(O))
    f = PolynomialRing(R, "x", cached = false)[1]()
    d = length(OP.basis)

    while true
      r = rand(0:p-1, d)
      x = quoelem(OP, dot([ x for x in OP.basis], r))
      f = minpoly(x)
      if degree(f) == d
        break
      end
    end

    F = FqFiniteField(f, Symbol("_\$"), false)

    M2 = zero_matrix(R, degree(O), d)

    for i in 1:d
      coords = elem_in_basis((x^(i-1)).elem)
      for j in 1:degree(O)
        M2[j, i] = coords[j]
      end
    end

    M3 = zero_matrix(R, degree(O), degree(O))

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

    function _image(y::NfOrdElem)
      co = zero_matrix(R, degree(O), 1)
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

    function _preimage(y::fq)
      z = nf(O)()

      for i in 0:degree(F)-1
        z = z + coeff(y, i)*(x.elem.elem_in_nf)^i
      end

      return mod(O(z, false), P)
    end

    z.header = MapHeader{NfOrd, FqFiniteField}(O, F, _image, _preimage)
    z.P = P

    return z
  end

end

function image(f::NfOrdToFqMor, x::NfOrdElem)
  if f.fastpath
    F = codomain(f)
    O = domain(f)
    u = F()
    gg = parent(nf(O).pol)(elem_in_nf(x))::fmpq_poly
    fmpq_poly_to_fmpz_mod_poly_raw!(f.tmp_fmpz_mod_poly, gg, f.t_fmpz_poly, f.t_fmpz)
    ccall((:fmpz_mod_poly_rem, :libflint), Void, (Ptr{fmpz_mod_poly}, Ptr{fmpz_mod_poly}, Ptr{fmpz_mod_poly}), &f.tmp_fmpz_mod_poly, &f.tmp_fmpz_mod_poly, &f.poly_of_the_field)
    ccall((:fq_set, :libflint), Void, (Ptr{fq}, Ptr{fmpz_mod_poly}, Ptr{FqFiniteField}), &u, &f.tmp_fmpz_mod_poly, &F)
    ccall((:fq_reduce, :libflint), Void, (Ptr{fq}, Ptr{FqFiniteField}), &u, &F)
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


function Mor(O::NfOrd, F::FqFiniteField, h::fmpz_mod_poly)
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

mutable struct NfToFqNmodMor <: Map{AnticNumberField, FqNmodFiniteField}
  header::MapHeader{AnticNumberField, FqNmodFiniteField}

  function NfToFqNmodMor()
    r = new()
    r.header = MapHeader{AnticNumberField, FqNmodFiniteField}()
    return r
  end
end

mutable struct NfToFqMor <: Map{AnticNumberField, FqFiniteField}
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


