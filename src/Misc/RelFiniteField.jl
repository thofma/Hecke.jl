###############################################################################
#
#  Types
#
################################################################################

mutable struct RelFinField{T} <: FinField
  defining_polynomial::PolyRingElem{T}
  var::Symbol
  absolute_field::Nemo.FinFieldMorphism
  basis_tr::Vector{T}

  function RelFinField(f::PolyRingElem{T}, v::Symbol) where T
    K = new{T}()
    K.defining_polynomial = f
    K.var = v
    return K
  end
end

mutable struct RelFinFieldElem{S, T} <: FinFieldElem
  parent::S
  data::T
end

################################################################################
#
#  Show functions
#
################################################################################

function Base.show(io::IO, F::RelFinField)
  print(io, "Field extension defined by $(defining_polynomial(F)) over $(base_field(F)) ")
end

function Base.show(io::IO, a::RelFinFieldElem)
  print(io, AbstractAlgebra.obj_to_string(a, context = io))
end

function AbstractAlgebra.expressify(a::RelFinFieldElem; context = nothing)
  return AbstractAlgebra.expressify(a.data, var(parent(a)),
                                    context = context)
end

############################################################################
#
#  Basic properties
#
############################################################################

var(F::RelFinField) = F.var

prime_field(F::RelFinField; cached::Bool = true) = prime_field(base_field(F), cached = cached)

function defining_polynomial(F::RelFinField{T}) where T
  return F.defining_polynomial::dense_poly_type(T)
end

base_field(F::RelFinField{S}) where S= base_ring(F.defining_polynomial)::parent_type(S)

characteristic(F::RelFinField) = characteristic(base_field(F))

order(F::RelFinField) = order(base_field(F))^degree(F)

degree(F::RelFinField) = degree(defining_polynomial(F))

################################################################################
#
#  Absolute degree
#
################################################################################

absolute_degree(F::RelFinField) = degree(F)*absolute_degree(base_field(F))
absolute_degree(F::FinField) = degree(F)

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(x::RelFinFieldElem{S, T}, id::IdDict) where {S, T}
  return RelFinFieldElem{S, T}(x.parent, Base.deepcopy_internal(x.data, id))
end

################################################################################
#
#  Promotion rules
#
################################################################################

AbstractAlgebra.promote_rule(::Type{RelFinFieldElem{S, T}}, ::Type{ZZRingElem}) where {S, T} = RelFinFieldElem{S, T}

AbstractAlgebra.promote_rule(::Type{ZZRingElem}, ::Type{RelFinFieldElem{S, T}}) where {S, T} = RelFinFieldElem{S, T}

function AbstractAlgebra.promote_rule(::Type{RelFinFieldElem{RelFinField{S}, T}}, ::Type{V}) where {S, T, V <: Union{fqPolyRepFieldElem, FqPolyRepFieldElem, fpFieldElem, FpFieldElem}}
  U = AbstractAlgebra.promote_rule(S, fqPolyRepFieldElem)
  if U === S
    return RelFinFieldElem{RelFinField{S}, T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{V}, ::Type{RelFinFieldElem{RelFinField{S}, T}}) where {S, T, V <: Union{fqPolyRepFieldElem, FqPolyRepFieldElem, fpFieldElem, FpFieldElem}}
  U = AbstractAlgebra.promote_rule(S, fqPolyRepFieldElem)
  if U === S
    return RelFinFieldElem{RelFinField{S}, T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{RelFinFieldElem{RelFinField{S}, T}}, ::Type{RelFinFieldElem{RelFinField{U}, V}}) where {S <: FinFieldElem, T, U <: FinFieldElem, V}
  NT = AbstractAlgebra.promote_rule(S, U)
  if NT === S
    return RelFinFieldElem{RelFinField{S}, T}
  elseif NT === U
    return RelFinFieldElem{RelFinField{U}, V}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{Hecke.RelFinFieldElem{Hecke.RelFinField{S},T}}, ::Type{Hecke.RelFinFieldElem{Hecke.RelFinField{S},T}}) where {S <: FinFieldElem, T}
  return Hecke.RelFinFieldElem{Hecke.RelFinField{S},T}
end

################################################################################
#
#  Basic properties of elements
#
################################################################################

parent(a::RelFinFieldElem) = a.parent
data(a::RelFinFieldElem) = a.data

iszero(x::RelFinFieldElem) = iszero(x.data)
isone(x::RelFinFieldElem) = isone(x.data)
is_unit(x::RelFinFieldElem) = !iszero(x)

==(x::RelFinFieldElem{S, T}, y::RelFinFieldElem{S, T}) where {S, T} = x.data == y.data

coeff(a::RelFinFieldElem, i::Int) = coeff(a.data, i)

one(F::RelFinField{S}) where {S} = F(one(parent(defining_polynomial(F))))

zero(F::RelFinField{S}) where {S} = F(parent(defining_polynomial(F))())

function zero!(x::RelFinFieldElem)
  zero!(x.data)
  return x
end

elem_type(::Type{RelFinField{T}}) where T = RelFinFieldElem{RelFinField{T}, dense_poly_type(T)}

parent_type(::Type{RelFinFieldElem{S, T}}) where {S, T}  = S

gen(F::RelFinField) = F(gen(parent(defining_polynomial(F))))

################################################################################
#
#  Special Coercion
#
################################################################################

function (F::RelFinField)()
  x = parent(defining_polynomial(F))()
  return RelFinFieldElem{typeof(F), typeof(x)}(F, x)
end

function (F::RelFinField{T})(x::S) where {S <: IntegerUnion, T}
  return F(parent(defining_polynomial(F))(x))
end

function (F::RelFinField{T})(x::PolyRingElem{T}) where T
  r = mod(x, defining_polynomial(F))
  return RelFinFieldElem{typeof(F), typeof(r)}(F, r)
end

function (F::RelFinField{T})(x::T) where {T}
  Kx = parent(defining_polynomial(F))
  r = Kx(x)
  return RelFinFieldElem{typeof(F), typeof(r)}(F, r)
end

function (F::RelFinField{T})(x::RelFinFieldElem{RelFinField{T}, S}) where {S, T}
  @assert parent(x) == F
  return x
end

function (F::RelFinField{T})(x::fqPolyRepFieldElem) where T
  y = base_field(F)(x)
  return F(parent(defining_polynomial(F))(y))
end

function (F::RelFinField{T})(x::fpFieldElem) where T
  y = base_field(F)(x)
  return F(parent(defining_polynomial(F))(y))
end

function (F::RelFinField{T})(x::FqPolyRepFieldElem) where T
  y = base_field(F)(x)
  return F(parent(defining_polynomial(F))(y))
end

function (F::RelFinField{T})(x::FpFieldElem) where T
  y = base_field(F)(x)
  return F(parent(defining_polynomial(F))(y))
end

function (F::RelFinField{T})(x::S) where {S, T}
  U = AbstractAlgebra.promote_rule(elem_type(F), S)
  if U == S
    #I an trying to coerce x to the subfield F!
    g = data(x)
    for i = 1:degree(g)
      @assert iszero(coeff(g, i)) "Element not coercible!"
    end
    return F(coeff(g, 0))
  else
    #I an trying to coerce x to the overfield F!
    @assert U == elem_type(F)
    return F(base_field(F)(x))
  end
end

function (F::fpField)(a::RelFinFieldElem)
  for i = 1:degree(parent(a))-1
    @assert iszero(coeff(a, i))
  end
  return F(coeff(a, 0))
end

function (F::FpField)(a::RelFinFieldElem)
  for i = 1:degree(parent(a))-1
    @assert iszero(coeff(a, i))
  end
  return F(coeff(a, 0))
end


################################################################################
#
#  Basic operations
#
################################################################################

function Base.:(+)(x::RelFinFieldElem{S, T}, y::RelFinFieldElem{S, T}) where {S, T}
  return RelFinFieldElem{S, T}(parent(x), x.data+y.data)
end

function Base.:(-)(x::RelFinFieldElem{S, T}, y::RelFinFieldElem{S, T}) where {S, T}
  return RelFinFieldElem{S, T}(parent(x), x.data-y.data)
end

function Base.:(-)(x::RelFinFieldElem{S, T}) where {S, T}
  return RelFinFieldElem{S, T}(parent(x), -x.data)
end

function Base.:(*)(x::RelFinFieldElem{S, T}, y::RelFinFieldElem{S, T}) where {S, T}
  F = parent(x)
  @assert F === parent(y)
  return F(x.data*y.data)
end

function mul!(z::RelFinFieldElem{S, T}, x::RelFinFieldElem{S, T}, y::RelFinFieldElem{S, T}) where {S, T}
  z.parent = x.parent
  z.data = mul!(z.data, x.data, y.data)
  z.data = rem!(z.data, z.data, defining_polynomial(z.parent))
  return z
end

function add!(z::RelFinFieldElem{S, T}, x::RelFinFieldElem{S, T}, y::RelFinFieldElem{S, T}) where {S, T}
  z.parent = x.parent
  z.data = add!(z.data, x.data, y.data)
  z.data = rem!(z.data, z.data, defining_polynomial(z.parent))
  return z
end

function sub!(z::RelFinFieldElem{S, T}, x::RelFinFieldElem{S, T}, y::RelFinFieldElem{S, T}) where {S, T}
  z.parent = x.parent
  z.data = sub!(z.data, x.data, y.data)
  z.data = rem!(z.data, z.data, defining_polynomial(z.parent))
  return z
end

function Base.div(x::RelFinFieldElem{S, T}, y::RelFinFieldElem{S, T}) where {S, T}
  return x*inv(y)
end

function divexact(x::RelFinFieldElem{S, T}, y::RelFinFieldElem{S, T}; check::Bool = true) where {S, T}
  return x*inv(y)
end

function inv(x::RelFinFieldElem{S, T}) where {S, T}
  if iszero(x)
    error("Element not invertible")
  end
  d, a, b = gcdx(x.data, defining_polynomial(parent(x)))
  @assert isone(d)
  return RelFinFieldElem{S, T}(parent(x), a)
end

function Base.:(^)(a::RelFinFieldElem, b::Int)
  if b < 0
    return inv(a)^(-b)
  elseif b == 0
    return parent(a)(1)
  elseif b == 1
    return deepcopy(a)
  elseif mod(b, 2) == 0
    c = a^(div(b, 2))
    c = mul!(c, c, c)
    return c
  else
    #mod(b, 2) == 1
    b = a^(b - 1)
    b = mul!(b, b, a)
    return b
  end
end

################################################################################
#
#  Norm and Trace
#
################################################################################

#TODO: resultant or conjugates?
function norm(x::RelFinFieldElem)
  return resultant(defining_polynomial(parent(x)), x.data)
end

function norm_via_powering(x::RelFinFieldElem)
  q = order(base_field(parent(x)))
  n = degree(parent(x))
  y = x^divexact(q^n - 1, q - 1)
  return y
end

function assure_traces(F::RelFinField{T}) where T
  if isdefined(F, :basis_tr)
    return nothing
  end
  res = T[base_field(F)(degree(F))]
  append!(res, polynomial_to_power_sums(defining_polynomial(F), degree(F)-1))
  F.basis_tr = res
  return nothing
end

function tr(x::RelFinFieldElem)
  F = parent(x)
  assure_traces(F)
  res = base_field(F)()
  t = base_field(F)()
  for i = 0:degree(data(x))
    t = mul!(t, F.basis_tr[i+1], coeff(x, i))
    res = add!(res, res, t)
  end
  return res
end

################################################################################
#
#  Minpoly
#
################################################################################

function minpoly(a::T, Rx::PolyRing = polynomial_ring(base_field(parent(a)), "x", cached = false)[1]) where T <:RelFinFieldElem
  F = parent(a)
  d = degree(F)
  p = order(base_field(F))
  conjs = T[a]
  el = a
  for i = 2:d
    el = el^p
    if el != a
      push!(conjs, el)
    else
      break
    end
  end
  Fx, x = polynomial_ring(F, "x", cached = false)
  minp = prod([x - Fx(y) for y in conjs])

  Fp = base_ring(Rx)
  coeffs = Vector{elem_type(Fp)}(undef, degree(minp)+1)
  for i = 0:degree(minp)
    coeffs[i+1] = Fp(coeff(minp, i))
  end
  return Rx(coeffs)
end

################################################################################
#
#  Absolute norm and trace
#
################################################################################

function absolute_norm(x::FinFieldElem)
  F = prime_field(parent(x))
  return F(norm(x))::elem_type(F)
end
function absolute_norm(x::RelFinFieldElem)
  return absolute_norm(norm(x))::elem_type(prime_field(parent(x), cached = false))
end

function absolute_tr(x::FinFieldElem)
  return prime_field(parent(x))(tr(x))
end

function absolute_tr(x::RelFinFieldElem)
  return absolute_tr(tr(x))
end

################################################################################
#
#  Absolute minpoly
#
################################################################################

function absolute_minpoly(a::T, Rx::PolyRing = polynomial_ring(prime_field(parent(a), cached = false), "x", cached = false)[1]) where T <: FinFieldElem
  F = parent(a)
  d = absolute_degree(F)
  p = characteristic(F)
  conjs = T[a]
  el = a
  for i = 2:d
    el = el^p
    if el != a
      push!(conjs, el)
    else
      break
    end
  end
  Fx, x = polynomial_ring(F, "x", cached = false)
  minp = prod(typeof(x)[x - Fx(y) for y in conjs])

  #Now, I need to coerce the polynomial down to a fpPolyRingElem/FpPolyRingElem
  Fp = base_ring(Rx)
  coeffs = Vector{elem_type(Fp)}(undef, degree(minp)+1)
  for i = 0:degree(minp)
    coeffs[i+1] = Fp(coeff(minp, i))
  end
  return Rx(coeffs)
end

#Special function in case one knows the degree of the result
function _minpoly(a::T, d::Int) where T <: FinFieldElem
  Fp = prime_field(parent(a))
  tr_in_K = Vector{elem_type(Fp)}(undef, 2*d)
  tr_in_K[1] = absolute_tr(a)
  el = one(parent(a))
  mul!(el, el, a)
  for i = 2:2*d
    mul!(el, el, a)
    tr_in_K[i] = absolute_tr(el)
  end
  fl, res = berlekamp_massey(tr_in_K)
  return res
end

################################################################################
#
#  Absolute basis and coordinates
#
################################################################################

function absolute_basis(F::RelFinField{T}) where T <: FinFieldElem
  BK = absolute_basis(base_field(F))
  BK = F.(BK)
  gF = gen(F)
  BF = Vector{elem_type(F)}(undef, absolute_degree(F))
  ind = 1
  a = one(F)
  for i = 0:degree(F)-1
    for j = 1:length(BK)
      BF[ind] = a*BK[j]
      ind += 1
    end
    a = a*gF
  end
  return BF
end

function absolute_basis(F::T) where T <: FinField
  return powers(gen(F), degree(F)-1)
end

function absolute_basis(F::FqField)
  return powers(Nemo._gen(F), absolute_degree(F) - 1)
end

function absolute_coordinates(x::FqFieldElem)
  F = prime_field(parent(x))
  return FqFieldElem[F(Nemo._coeff(x, i)) for i in 0:Nemo._degree(parent(x))-1]
end

function absolute_coordinates(x::FinFieldElem)
  F = parent(x)
  Fp = prime_field(F)
  v = Vector{elem_type(Fp)}(undef, degree(F))
  if iszero(x)
    for i = 1:length(v)
      v[i] = Fp()
    end
    return v
  end
  for i = 1:length(v)
    v[i] = Fp(coeff(x, i-1))
  end
  return v
end

function absolute_coordinates(x::RelFinFieldElem)
  F = parent(x)
  f = data(x)
  Fp = prime_field(F)
  v = Vector{elem_type(Fp)}(undef, absolute_degree(F))
  ind = 1
  for i = 0:degree(F)-1
    c = coeff(f, i)
    vc = absolute_coordinates(c)
    for j = 1:length(vc)
      v[ind] = vc[j]
      ind += 1
    end
  end
  return v
end

################################################################################
#
#  Random element
#
################################################################################

function rand(F::RelFinField)
  Rx = parent(defining_polynomial(F))
  return F(rand(Rx, 0:degree(F)-1)::elem_type(Rx))
end

################################################################################
#
#  Interface
#
################################################################################

function Native.finite_field(f::T, s::VarName = :a; cached::Bool = true, check::Bool = true) where T <: Union{fqPolyRepPolyRingElem, FqPolyRepPolyRingElem}
  if check
    @assert is_irreducible(f)
  end
  k = base_ring(f)
  F = RelFinField(f, Symbol(s))
  return F, gen(F)
end

function Native.finite_field(f::PolyRingElem{T}, s::VarName = :a; cached::Bool = true, check::Bool = true) where T <: RelFinFieldElem
  if check
    @assert is_irreducible(f)
  end
  F = RelFinField(f, Symbol(s))
  return F, gen(F)
end

################################################################################
#
#  Morphisms
#
################################################################################

function id_hom(F::FinField)
  return Nemo.FinFieldMorphism(F, F, x -> identity(x), x -> identity(x))
end

function inv(f::Nemo.FinFieldMorphism)
  if absolute_degree(domain(f)) != absolute_degree(codomain(f))
    error("Not invertible!")
  end
  return Nemo.FinFieldMorphism(codomain(f), domain(f), inverse_fn(f), image_fn(f))
end

function hom(F::FinField, K::RelFinField, a::RelFinFieldElem; check::Bool = true)
  @assert parent(a) == K

  if check
    @assert iszero(defining_polynomial(F)(a))
  end

  #We need a preimage function
  p = characteristic(K)
  Kp = prime_field(K)
  Kpx = polynomial_ring(Kp, "x", cached = false)[1]
  Fp = prime_field(F)
  Fpx = polynomial_ring(Fp, "x", cached = false)[1]
  M = zero_matrix(Kp, absolute_degree(F), absolute_degree(K))
  el = one(K)
  M[1, 1] = one(Kp)
  for i = 2:nrows(M)
    el = mul!(el, el, a)
    v = absolute_coordinates(el)
    for j = 1:ncols(M)
      M[i, j] = Kp(v[j])
    end
  end

  aux = zero_matrix(Kp, 1, absolute_degree(F))
  aux1 = zero_matrix(Kp, 1, absolute_degree(K))
  bF = absolute_basis(F)
  bK = absolute_basis(K)
  function img(x::FinFieldElem)
    @assert parent(x) == F
    cx = absolute_coordinates(x)
    for i = 1:absolute_degree(F)
      aux[1, i] = Kp(cx[i])
    end
    mul!(aux1, aux, M)
    pol = sum(aux1[1, i]*bK[i] for i = 1:absolute_degree(K))
    return pol
  end

  function preimg(x::FinFieldElem)
    @assert parent(x) == K
    cx = absolute_coordinates(x)
    for i = 1:absolute_degree(K)
      aux1[1, i] = Kp(cx[i])
    end
    fl, y = can_solve_with_solution(M, aux1, side = :left)
    if !fl
      error("The element is not in the image!")
    end
    polF = sum(y[1, i]*bF[i] for i = 1:absolute_degree(F))
    return polF
  end

  return Nemo.FinFieldMorphism(F, K, img, preimg)
end

################################################################################
#
#  Absolute Field
#
################################################################################

function _char(F::Union{FqPolyRepField, FqField, FpField})
  return characteristic(F)
end

function _char(F::Union{fpField, fqPolyRepField})
  return Int(characteristic(F))
end

function _char(F::RelFinField)
  return _char(base_field(F))
end

function absolute_field(F::T) where T <: FinField
  return F, id_hom(F)
end

function absolute_field(F::RelFinField{T}; cached::Bool = true) where T <: FinFieldElem
  if isdefined(F, :absolute_field)
    res_map = F.absolute_field
    return domain(res_map), res_map
  end
  p = _char(F)
  d = absolute_degree(F)
  K, gK = Native.finite_field(p, d, "a", cached = cached)
  k, mk = absolute_field(base_field(F))
  def_pol_new = map_coefficients(pseudo_inv(mk), defining_polynomial(F), cached = false)
  img_gen_k = roots(K, defining_polynomial(k))[1]
  mp = hom(k, K, img_gen_k)
  g = map_coefficients(mp, def_pol_new, cached = false)
  img_gen_F = roots(g)[1]
  img_basis_k = powers(img_gen_k, degree(k)-1)
  img_absolute_basis = Vector{elem_type(K)}(undef, degree(K))
  ind = 1
  el = one(K)
  for i = 0:degree(F)-1
    for j = 1:length(img_basis_k)
      img_absolute_basis[ind] = el*img_basis_k[j]
      ind += 1
    end
    el *= img_gen_F
  end
  #Now, I need to construct the hom.
  Fp = prime_field(K)
  M = zero_matrix(Fp, degree(K), degree(K))
  for i = 1:length(img_absolute_basis)
    for j = 0:degree(K)-1
      M[i, j+1] = coeff(img_absolute_basis[i], j)
    end
  end
  Minv = inv(M)
  abs_basis = absolute_basis(F)
  aux = zero_matrix(Fp, 1, degree(K))
  function img(x::FinFieldElem)
    @assert parent(x) == K
    for j = 1:degree(K)
      aux[1, j] = coeff(x, j-1)
    end
    mul!(aux, aux, Minv)
    el = F()
    for i = 1:degree(K)
      if !iszero(aux[1, i])
        el += F(aux[1, i])*abs_basis[i]
      end
    end
    return el
  end

  Fpx = polynomial_ring(Fp)[1]

  function preimg(x::RelFinFieldElem)
    @assert parent(x) == F
    v = absolute_coordinates(x)
    for j = 1:degree(K)
      aux[1, j] = v[j]
    end
    mul!(aux, aux, M)
    v1 = typeof(v[1])[aux[1, j] for j = 1:ncols(aux)]
    return K(Fpx(v1))
  end

  return K, Nemo.FinFieldMorphism(K, F, img, preimg)
end

################################################################################
#
#  Polynomial factorization
#
################################################################################

function factor(f::PolyRingElem{T}) where T <: RelFinFieldElem
  K = base_ring(f)
  Kx = parent(f)
  F, mF = absolute_field(K)
  imF = inv(mF)
  @assert domain(imF) == K
  fF = map_coefficients(imF, f, cached = false)
  lfF = factor(fF)
  facs = Dict{typeof(f), Int}()
  for (p, k) in lfF
    facs[map_coefficients(mF, p, parent = Kx)] = k
  end
  return Fac(map_coefficients(mF, lfF.unit, parent = Kx), facs)
end

function is_irreducible(f::PolyRingElem{T}) where T <: RelFinFieldElem
  l = factor(f)
  return length(l.fac) == 1
end



function norm(f::PolyRingElem{fqPolyRepFieldElem})
  Fx = parent(f)
  Fp = prime_field(base_ring(Fx))
  Fpx = polynomial_ring(Fp, "x", cached = false)[1]
  Fpxy = polynomial_ring(Fpx, "y", cached = false)[1]

  dp = defining_polynomial(base_ring(Fx), Fpx)
  T = Fpxy()
  for i = 0:degree(dp)
    setcoeff!(T, i, Fpx(coeff(dp, i)))
  end
  h = fq_nmod_to_xy(f, Fpxy, Fpx)
  res = resultant(T, h)
  return res
end

function fq_nmod_to_xy(f, Qxy::PolyRing, Qx::PolyRing)
  K = base_ring(f)
  Qy = parent(defining_polynomial(K, prime_field(K)))
  y = gen(Qx)

  res = zero(Qxy)
  for i=degree(f):-1:0
    res *= y
    res += change_base_ring(Qx, Qy(coeff(f, i)), parent = Qxy)
  end
  return res
end


