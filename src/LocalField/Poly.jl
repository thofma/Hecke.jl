add_assert_scope(:padic_poly)

################################################################################
#
#  setprecision
#
################################################################################

function setprecision!(f::Generic.Poly{qadic}, N::Int)
  for i=1:length(f)
    f.coeffs[i].N = N
  end
  return f
end

function Base.setprecision(f::Generic.Poly{qadic}, N::Int)
  f = deepcopy(f)
  f = setprecision!(f, N)
  return f
end

function setprecision_fixed_precision(f::Generic.Poly{qadic}, N::Int)
  f = deepcopy(f)
  f = setprecision!(f, N)
  for i = length(f):-1:1
    if f.coeffs[i].val < N && !iszero(f.coeffs[i])
      set_length!(f, i)
      break
    end
  end
  return f
end

function setprecision_fixed_precision(a::LocalFieldElem, n::Int)
  return setprecision(a, n)
end

function Nemo.setprecision(f::Generic.Poly{<:LocalFieldElem}, n::Int)
  f = deepcopy(f)
  f = setprecision!(f, n)
  return f
end

function setprecision!(f::Generic.Poly{<:LocalFieldElem}, n::Int)
  for i = 1:length(f.coeffs)
    f.coeffs[i] = setprecision!(f.coeffs[i], n)
  end
  return f
end

function setprecision_fixed_precision(f::Generic.Poly{<:LocalFieldElem}, n::Int)
  fr = map_coefficients(x -> setprecision_fixed_precision(x, n), f, parent = parent(f))
  return fr
end

################################################################################
#
#  Lift
#
################################################################################

@doc Markdown.doc"""
    lift(a::T, K::PadicField) where T <: Union{Nemo.nmod, Generic.Res{fmpz}, gfp_elem} -> padic

Computes a lift of the element from the residue ring.
"""
function lift(a::T, K::PadicField) where T <: Union{Nemo.nmod, Nemo.fmpz_mod, Generic.Res{fmpz}, gfp_elem}
  n = modulus(parent(a))
  p = prime(K)
  v, fl = remove(n, p)
  @assert isone(fl)
  return Hecke.lift(a) + O(K, p^v)
end

function lift(a::FinFieldElem, K::LocalField)
  k, mk = ResidueField(K)
  @assert k === parent(a)
  return mk\a
end


@doc Markdown.doc"""
    lift(f::T, Kt) where T <: Union{nmod_poly, fmpz_mod_poly, gfp_poly} -> Generic.Poly{padic}

Computes a lift of the polynomial lifting every coefficient of the residue ring.
"""
function lift(f::T, Kt::PolyRing) where T <: FinFieldElem
  return map_coefficients(x -> lift(x, K), f, Kt)
end

@doc Markdown.doc"""
    lift(x::fq_nmod, Q::QadicField) -> qadic

Computes a lift of the element from the residue ring.
"""
function lift(x::fq_nmod, Q::QadicField)
  z = Q()
  for i=0:degree(Q)-1
    setcoeff!(z, i, coeff(x, i))
  end
  return setprecision(z, 1)
end

@doc Markdown.doc"""
    lift(x::fq_nmod_poly, Kt) -> Generic.Poly{qadic}

Computes a lift of the polynomial lifting every coefficient of the residue ring.
"""
function lift(x::fq_nmod_poly, Kt)
  K = base_ring(Kt)
  coeffs = Vector{qadic}(undef, degree(x)+1)
  for i = 1:degree(x)+1
    coeffs[i] = lift(coeff(x, i-1), K)
  end
  return Kt(coeffs)
end

function _content(f::Generic.Poly{T}) where T <: Union{padic, qadic, LocalFieldElem}
  K = base_ring(f)
  @assert !iszero(f)
  c = coeff(f, 0)
  i = 0
  while iszero(c)
    i += 1
    c = coeff(f, i)
  end
  v = valuation(c)
  for j = i+1:degree(f)
    c = coeff(f, j)
    if !iszero(c)
      v = min(v, valuation(c))
    end
  end
  if iszero(v)
    return one(K)
  end
  e = v*absolute_ramification_index(K)
  @assert isone(denominator(e))
  return uniformizer(K)^numerator(e)
end

function rem!(x::AbstractAlgebra.Generic.Poly{T}, y::AbstractAlgebra.Generic.Poly{T}, z::AbstractAlgebra.Generic.Poly{T}) where T <:Union{padic, qadic, LocalFieldElem}
  x = rem(y, z)
  return x
end

################################################################################
#
#  Fun factor
#
################################################################################

function fun_factor(g::Generic.Poly{padic})
  K = base_ring(g)
  Kt = parent(g)
  v = precision(g)
  pv = prime(K)^v
  R = ResidueRing(FlintZZ, pv, cached = false)
  Rt = PolynomialRing(R, "t", cached = false)[1]
  fR = Rt([R(Hecke.lift(coeff(g, i))) for i = 0:degree(g)])
  u, g1 = Hecke.fun_factor(fR)
  fun = x -> lift(x, K)
  return map_coefficients(fun, u, parent = Kt), map_coefficients(fun, g1, parent = Kt)
end

function fun_factor(f::Generic.Poly{S}) where S <: Union{qadic, LocalFieldElem}
  K = base_ring(f)
  Kt = parent(f)
  v = precision(f)
  f = setprecision_fixed_precision(f, v)
  @assert isone(_content(f))
  if iszero(valuation(leading_coefficient(f)))
    return one(Kt), g
  end
  ind = degree(f) -1
  while !iszero(valuation(coeff(f, ind)))
    ind -= 1
  end
  g = setprecision_fixed_precision(Kt([coeff(f, i) for i = ind:degree(f)]), 1)
  h = setprecision_fixed_precision(Kt([divexact(coeff(f, i), coeff(f, ind)) for i = 0:ind]), 1) 
  s = setprecision_fixed_precision(Kt(inv(coeff(g, 0))), 2)
  t = setprecision_fixed_precision(zero(Kt), 2)
  ch = Int[v]
  while ch[end] > 2
    push!(ch, div(ch[end]+1, 2))
  end
  reverse!(ch)
  for pr = 1:length(ch)-1
    i = ch[pr]
    g = setprecision_fixed_precision(g, i)
    h = setprecision_fixed_precision(h, i)
    s = setprecision_fixed_precision(s, ch[pr+1])
    t = setprecision_fixed_precision(t, ch[pr+1])
    e = f - g*h
    q, r = divrem(s*e, h)
    gn = g+t*e+q*g
    hn = h+r
    b = s*gn+t*hn-1
    c, d = divrem(s*b, hn)
    sn = s - d
    tn = t- t*b- c*gn
    g = gn
    h = hn
    s = sn
    t = tn
  end
  i = ch[end]
  g = setprecision_fixed_precision(g, v)
  h = setprecision_fixed_precision(h, v)
  e = f - g*h
  q, r = divrem(s*e, h)
  res1 = g+t*e+q*g
  res2 = h+r
  return setprecision_fixed_precision(res1, v), setprecision_fixed_precision(res2, v)
end

################################################################################
#
#  Gcd
#
################################################################################


function Nemo.precision(g::Generic.Poly{T}) where T <: Union{padic, qadic}
  N = precision(coeff(g, 0))
  for i = 1:degree(g)
    N = min(N, precision(coeff(g, i)))
  end
  return N
end


function Base.gcd(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{padic, qadic, LocalFieldElem}
  if degree(f) < degree(g)
    f, g = g, f
  end
  f = setprecision(f, precision(f))
  g = setprecision(g, precision(g))
  while true
    cf = _content(f)
    if !isone(cf)
      f = divexact(f, cf)
    end
    cg = _content(g)
    if !isone(cg)
      g = divexact(g, cg)
    end
    if !iszero(valuation(leading_coefficient(g)))
      u, g1 = fun_factor(g)
      if iszero(valuation(leading_coefficient(f)))
        g = g1#*reverse(gcd(reverse(f), reverse(u)))
      else
        v, f1 = fun_factor(f)
        return reverse(gcd(reverse(u), reverse(v)))*gcd(f1, g1)
      end
    end
    f = mod(f, g)
    if degree(f) < 1
      if iszero(f)
        return g
      else
        return divexact(f, leading_coefficient(f))
      end
    else
      f, g = g, f
    end
  end
end

################################################################################
#
#  Invmod
#
################################################################################

function invmod(u::Generic.Poly{padic}, f::Generic.Poly{padic})
  if !iszero(valuation(leading_coefficient(f)))
    error("Not yet implemented")
  end
  if !iszero(valuation(coeff(u, 0))) || !all(x -> x > 0, [valuation(coeff(u, i)) for i = 1:degree(u)])
    g, s, t = gcdx(u, f)
    return s
  end
  K = base_ring(f)
  Kt = parent(f)
  v = min(precision(f), precision(u))
  pv = prime(K)^v
  R = ResidueRing(FlintZZ, pv, cached = false)
  Rt = PolynomialRing(R, "t", cached = false)[1]
  fR = Rt([R(Hecke.lift(coeff(f, i))) for i = 0:degree(f)])
  uR = Rt([R(Hecke.lift(coeff(u, i))) for i = 0:degree(u)])
  iuR = invmod(uR, fR)
  return map_coefficients(x -> lift(x, K), iuR, parent = Kt)
end

function invmod(f::Generic.Poly{T}, M1::Generic.Poly{T}) where T <: Union{qadic, LocalFieldElem}
  if !iszero(valuation(leading_coefficient(M1)))
    error("Not yet implemented")
  end
  M = setprecision(M1, precision(M1))
  f = rem(f, M)
  if !iszero(valuation(coeff(f, 0))) || !all(x -> x > 0, [valuation(coeff(f, i)) for i = 1:degree(f)])
    g, s, t = gcdx(f, M)
    return s
  end
  K = base_ring(f)
  Kt = parent(f)
  invc = inv(constant_coefficient(f))
  g = parent(f)(invc)
  c = f*g
  c = rem!(c, c, M)
  while !isone(c)
    g = mul!(g, g, 2-c)
    g = rem!(g, g, M)
    c = mul!(c, f, g)
    c = rem!(c, c, M)
    c = setprecision!(c, precision(M))
  end
  return g
end


################################################################################
#
#  xgcd
#
################################################################################

#TODO: The implementation is recursive. Change it to an iterative implementation.
function gcdx(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{padic, qadic, LocalFieldElem}
  if degree(f) < degree(g)
    r1, r2, r3 = gcdx(g, f)
    return r1, r3, r2
  end
  Kx = parent(f)
  if length(g) <= 1
    if iszero(g)
      return f, one(Kx), zero(Kx)
    else
      s = Kx(inv(coeff(g, 0)))
      @hassert one(Kx) == s*g
      return one(Kx), zero(Kx), s
    end
  end
  cf = _content(f)
  if !isone(cf)
    f1 = divexact(f, cf)
    d, u, v = gcdx(f1, g)
    @hassert :padic_poly 1 f*divexact(u, cf) + v*g == d
    return d, divexact(u, cf), v
  end
  cg = _content(g)
  if !isone(cg)
    g1 = divexact(g, cg)
    d, u, v = gcdx(f, g1)
    @hassert :padic_poly 1  f*u+divexact(v, cg)*g == d
    return d, u, divexact(v, cg)
  end
  if iszero(valuation(leading_coefficient(g)))
    q, f1 = divrem(f, g)
    d, u, v = gcdx(g, f1)
    @hassert :padic_poly 1  d == f*v+(u-v*q)*g
    return d, v, u-v*q
  end
  ug, gg = fun_factor(g)
  if iszero(valuation(leading_coefficient(f)))
    s = invmod(ug, f)
    to_be_div = 1-s*ug
    t = divexact(to_be_div, f)
    @hassert :padic_poly 1  t*f == 1-s*ug
    d, u, v = gcdx(f, gg)
    @hassert :padic_poly 1  d == u*f + v*gg
    @hassert :padic_poly 1  d == (u+v*t*gg)*f + v*s*g
    return d, u+v*t*gg, v*s
  end
  uf, ff = fun_factor(f)
  d, u, v = gcdx(ff, gg)
  if degree(gg) >= 1
    s = invmod(uf, gg)
    t = divexact(1-s*uf, gg)
    @hassert :padic_poly 1  t*gg == 1-s*uf
  else
    #gg = 1. Easy to compute Bezout coefficients...
    s = zero(Kx)
    t = one(Kx)
  end
  U = u*s
  V = u*ff*t + v*t*gg+s*uf*v
  d1, u1, v1 = gcdx(reverse(uf), reverse(ug))
  d1 = reverse(d1)
  u1 = reverse(u1)
  v1 = reverse(v1)
  @hassert :padic_poly 1  d1 == u1*uf+v1*ug
  if degree(ff) >= 1
    t1 = invmod(ug, ff)
    s1 = divexact(1-t1*ug, ff)
    @hassert :padic_poly 1  t1*ug + s1*ff == one(Kx)
  else
    t1 = zero(Kx)
    s1 = one(Kx)
    @hassert :padic_poly 1  s1*ff + t1*ug == one(Kx)
  end
  U1 = u1*s1
  V1 = s1*ff*v1+t1*u1*uf+t1*v1*ug

  DD = d*d1
  UU = U*U1*f + U1*V*gg+U*V1*ug
  VV = V*V1
  @hassert :padic_poly 1  DD == UU*f + VV*g
  return DD, UU, VV
end

function divexact(f1::AbstractAlgebra.PolyElem{T}, g1::AbstractAlgebra.PolyElem{T}) where T <: Union{padic, qadic, LocalFieldElem}
   check_parent(f1, g1)
   iszero(g1) && throw(DivideError())
   if iszero(f1)
      return zero(parent(f1))
   end
   lenq = length(f1) - length(g1) + 1
   d = Array{T}(undef, lenq)
   for i = 1:lenq
      d[i] = zero(base_ring(f1))
   end
   f = deepcopy(f1)
   g = deepcopy(g1)
   x = gen(parent(f1))
   leng = length(g1)
   while length(f) >= leng
      lenf = length(f)
      d[lenf - leng + 1] = divexact(coeff(f, lenf - 1), coeff(g, leng - 1))
      f = f - shift_left(d[lenf - leng + 1]*g, lenf - leng)
      if length(f) == lenf # inexact case
         set_length!(f, normalise(f, lenf - 1))
      end
   end
   q = parent(f1)(d)
   set_length!(q, lenq)
   K = base_ring(f)
   Kt = parent(f1)
   p = prime(K)
   while !iszero(q*g1 - f1)
     q = setprecision(q, precision(q)-1)
   end
   return q
end



################################################################################
#
#  Resultant and characteristic polynomial
#
################################################################################

reduced_resultant(f::T, g::T) where T <: PolyElem = rres(f, g)
reduced_discriminant(f::PolyElem) = rres(f, derivative(f))

function rres(f::Generic.Poly{padic}, g::Generic.Poly{padic})
  Kt = parent(f)
  K = base_ring(Kt)
  p = prime(K)
  v = min(precision(f), precision(g))
  R = ResidueRing(FlintZZ, p^v, cached = false)
  cf = Vector{elem_type(R)}(undef, degree(f)+1)
  for i = 1:length(cf)
    cf[i] = R(Hecke.lift(coeff(f, i-1)))
  end
  cg = Vector{elem_type(R)}(undef, degree(g)+1)
  for i = 1:length(cg)
    cg[i] = R(Hecke.lift(coeff(g, i-1)))
  end
  Rt = PolynomialRing(R, "t", cached = false)[1]
  r = Hecke.rres_sircana_pp(Rt(cf), Rt(cg))
  return lift(r, K)
end


function resultant(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{padic, qadic, LocalFieldElem}
  Nemo.check_parent(f, g)
  #First, we need to make the polynomials integral
  Rt = parent(f)
  R = base_ring(Rt)
  res = one(R)
  f = setprecision(f, precision(f))
  g = setprecision(g, precision(g))
  c1 = _content(f)
  if valuation(c1) < 0
    res *= c1^degree(g)
    f = divexact(f, c1)
  end
  c2 = _content(g)
  if valuation(c2) < 0
    res *= c2^degree(f)
    g = divexact(g, c2)
  end
  return res * _resultant(f, g)
end

function _resultant(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{padic, qadic, LocalFieldElem}
  Rt = parent(f)
  R = base_ring(Rt)
  res = one(R)
  while true
    if degree(f) < 1 && degree(g) < 1
      if iszero(f) || iszero(g)
        return zero(R)
      end
      return res
    elseif degree(f) < 1
      res *= leading_coefficient(f)^degree(g)
      return res
    elseif degree(g) < 1
      res *= leading_coefficient(g)^degree(f)
      return res
    end

    cf = _content(f)
    if !isone(cf)
      f = divexact(f, cf)
      res *= cf^degree(g)
    end

    cg = _content(g)
    if !isone(cg)
      g = divexact(g, cg)
      res *= cg^degree(f)
    end

    if degree(f) < degree(g)
      if !iszero(mod(degree(f)*degree(g), 2))
        res = -res
      end
      f, g = g, f
    end

    if valuation(leading_coefficient(g)) == 0
      r = rem(f, g)
      res *= leading_coefficient(g)^(degree(f) - degree(r))
      if !iszero(mod(degree(g)*(degree(f) - degree(r)), 2))
        res = -res
      end
      f = r
    else
      break
    end
  end
  g1, g2 = fun_factor(g)
  res1 = _resultant(f, g2)
  g1r = reverse(g1)
  fr = reverse(f)
  res2 = (-1)^(degree(f)*degree(g1))*(constant_coefficient(g1)^(degree(f) - degree(fr)))*_resultant(fr, g1r)
  return res*res1*res2
end

degree(::FlintPadicField) = 1
base_field(Q::FlintQadicField) = base_ring(defining_polynomial(Q))

function norm(f::PolyElem{T}) where T <: Union{qadic, LocalFieldElem}
  Kx = parent(f)
  K = base_ring(f)
  f, i = deflate(f)
  P = polynomial_to_power_sums(f, degree(f)*degree(K))
  PQ = elem_type(base_field(K))[tr(x) for x in P]
  N = power_sums_to_polynomial(PQ)
  return inflate(N, i)
end

function norm(f::PolyElem{padic})
  return f
end

@doc Markdown.doc"""
    characteristic_polynomial(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{padic, qadic} -> Generic.Poly{T}

Computes $\mathrm{Res}_x(f(x), t- g(x))$.
"""
function characteristic_polynomial(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{padic, qadic, LocalFieldElem}
  Kt = parent(f)
  Ktx, x = PolynomialRing(Kt, "x")
  fcoeffs = typeof(f)[Kt(coeff(f, i)) for i = 0:degree(f)]
  gcoeffs = typeof(f)[Kt(-coeff(g, i)) for i = 0:degree(g)]
  f1 = Ktx(fcoeffs)
  g1 = Ktx(gcoeffs) + gen(Kt)
  return resultant(f1, g1)
end

#=
function characteristic_polynomial(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{padic, qadic}
  K = base_ring(f)
  Kt = parent(f)
  p = prime(K)
  d = degree(K)
  if p^d <= degree(f)
    if d > 1
      error("Not yet implemented")
    end
    d1 = clog(fmpz(degree(f)+1), p)
    L = QadicField(p, d1, min(precision(f), precision(g)))
    Lt = PolynomialRing(L, "t")[1]
    fL = change_base_ring(f, L, Lt)
    gL = change_base_ring(g, L, Lt)
    cp = characteristic_polynomial(fL, gL)
    #cp will have coefficients over K, so I need to change the base ring.
    cf = [coeff(coeff(cp, i), 0) for i = 0:degree(cp)]
    return Kt([setprecision(K(lift(cf[i])), precision(cf[i])) for i = 1:length(cf)])
  end
  #The resultant will be a polynomial of degree degree(f1). So I need degree(f1)+1 interpolation points.
  ev_points = interpolation_points(K, degree(f)+1)
  res = Vector{typeof(f)}(undef, degree(f)+1)
  for i = 1:length(res)
    res[i] = Kt(resultant(f, ev_points[i] - g))
  end
  int_ideals = Vector{typeof(f)}(undef, length(ev_points))
  for i = 1:length(int_ideals)
    int_ideals[i] = Kt(T[-ev_points[i], K(1)])
  end
  crtctx = crt_env(int_ideals)
  resu = crt(res, crtctx)
  return resu
end
=#

function interpolation_points(K, n::Int)
  p = prime(K)
  if n < p
    return [K(i) for i = 1:n]
  end
  int_points = Vector{elem_type(K)}(undef, n)
  k, mk = ResidueField(K)
  ind = 1
  for el in k
    int_points[ind] = mk\el
    ind += 1
    if ind > n
      break
    end
  end
  @assert ind > n
  return int_points

end

################################################################################
#
#  Hensel factorization
#
################################################################################
@doc Markdown.doc"""
    Hensel_factorization(f::Generic.Poly{T}) where T <: Union{padic, qadic} -> Dict{Generic.Poly{T}, Generic.Poly{T}}

Computes a factorization of $f$ such that every factor has a unique irreducible factor over the residue field.
The output is a dictionary whose keys are lifts of the irreducible factors over the residue field and values the corresponding factors of $f$.
"""
function Hensel_factorization(f::Generic.Poly{T}) where T <: Union{padic, qadic, LocalFieldElem}
  cf = _content(f)
  f = divexact(f, cf)
  Kt = parent(f)
  D = Dict{Generic.Poly{T}, Generic.Poly{T}}()
  @assert iszero(valuation(leading_coefficient(f)))
  K = base_ring(Kt)
  k, mk = ResidueField(K)
  kt = PolynomialRing(k, "t", cached = false)[1]
  fp = kt(elem_type(k)[mk(coeff(f, i)) for i = 0:degree(f)])
  lfp = factor(fp).fac
  if length(lfp) == 1
    #The Hensel factorization is trivial...
    phi = setprecision(map_coefficients(pseudo_inv(mk), first(keys(lfp)), parent = Kt), precision(f))
    D[phi] = f
    return D
  end
  vlfp = Vector{dense_poly_type(elem_type(k))}(undef, length(lfp))
  ind = 1
  ks = Vector{Generic.Poly{T}}(undef, length(vlfp))
  for (k1, v) in lfp
    vlfp[ind] = k1^v
    ks[ind] = setprecision(map_coefficients(pseudo_inv(mk), k1, parent = Kt), precision(f))
    ind += 1
  end
  H = HenselCtxdr{T}(f, vlfp)
  lift(H, precision(f))
  for i = 1:H.n
    D[ks[i]] = H.lf[i]
  end
  return D
end


mutable struct HenselCtxdr{S}
  f::PolyElem{S}
  lf::Array{PolyElem{S}, 1}
  la::Array{PolyElem{S}, 1}
  p::S
  n::Int

  function HenselCtxdr{qadic}(f::Generic.Poly{qadic}, lfp::Vector{Generic.Poly{qadic}}, la::Vector{Generic.Poly{qadic}}, p::qadic, n::Int)
    return new(f, lfp, la, p, n)
  end

  function HenselCtxdr{S}(f::PolyElem{S}, lfp::Vector{T}) where {S, T}
    @assert sum(map(degree, lfp)) == degree(f)
    Q = base_ring(f)
    Qx = parent(f)
    i = 1
    la = Array{PolyElem{S}, 1}()
    n = length(lfp)
    while i < length(lfp)
      f1 = lfp[i]
      f2 = lfp[i+1]
      g, a, b = gcdx(f1, f2)
      @assert isone(g)
      push!(la, map_coefficients(x -> setprecision(lift(x, Q), 1), a, parent = Qx))
      push!(la, map_coefficients(x -> setprecision(lift(x, Q), 1), b, parent = Qx))
      push!(lfp, f1*f2)
      i += 2
    end
    return new(f, map(x -> map_coefficients(y -> setprecision(lift(y, Q), 1), x, parent = Qx), lfp), la, uniformizer(Q), n)
  end

  function HenselCtxdr{S}(f::PolyElem{S}) where S
    Q = base_ring(f)
    K, mK = ResidueField(Q)
    fp = change_base_ring(f, mK)
    fac = factor(fp).fac
    lfp = Vector{keytype(fac)}(undef, length(fac))
    ind = 1
    for (k, v) in fac
      lfp[ind] = k^v
      ind += 1
    end
    return HenselCtxQadic{S}(f, lfp)
  end
end

function lift(C::HenselCtxdr, mx::Int)
  p = C.p
  N = denominator(valuation(p))
#  @show map(precision, coefficients(C.f)), N, precision(parent(p))
  #have: N need mx
  ch = Int[mx]
  while ch[end] > N
    push!(ch, div(ch[end]+1, 2))
  end
  @vprint :PolyFactor 1 "using lifting chain ", ch
  for k=length(ch)-1:-1:1
    N2 = ch[k]
    i = length(C.lf)
    j = i-1
    p = setprecision(p, N2)
    while j > 0
      if i == length(C.lf)
        f = setprecision(C.f, N2)
      else
        f = setprecision(C.lf[i], N2)
      end
      #formulae and names from the Flint doc
      h = C.lf[j]
      g = C.lf[j-1]
      b = C.la[j]
      a = C.la[j-1]
      h = setprecision(h, N2)
      g = setprecision(g, N2)
      a = setprecision(a, N2)
      b = setprecision(b, N2)
      fgh = (f-g*h)*inv(p)
      G = rem(fgh*b, g)*p+g
      H = rem(fgh*a, h)*p+h
      t = (1-a*G-b*H)*inv(p)
      B = rem(t*b, g)*p+b
      A = rem(t*a, h)*p+a
      if i < length(C.lf)
        C.lf[i] = G*H
      end
      C.lf[j-1] = G
      C.lf[j] = H
      C.la[j-1] = A
      C.la[j] = B
      i -= 1
      j -= 2
    end
  end
  return nothing
end

################################################################################
#
#  Slope factorization
#
################################################################################

@doc Markdown.doc"""
    slope_factorization(f::Generic.Poly{T}) where T <: Union{padic, qadic} -> Dict{Generic.Poly{T}, Int}

Computes a factorization of $f$ such that every factor has a one-sided generalized Newton polygon.
The output is a dictionary whose keys are the factors of $f$ and the corresponding value is the multiplicity.
"""
function slope_factorization(f::Generic.Poly{T}) where T <: Union{padic, qadic, LocalFieldElem}

  K = base_ring(f)
  Kt = parent(f)
  fact = Dict{Generic.Poly{T}, Int}()
  cf = _content(f)
  f = divexact(f, cf)
  if !iszero(valuation(leading_coefficient(f)))
    u, f = fun_factor(f)
    u1 = reverse(u)
    sf = slope_factorization(u1)
    for (ff, eff) in sf
      fact[reverse(ff)] = eff
    end
  end
  sqf = factor_squarefree(f)
  for (g, v) in sqf
    hg = Hensel_factorization(g)
    for (phi, fphi) in hg
      if degree(phi) == degree(fphi)
        fact[fphi] = v
        continue
      end
      NP = newton_polygon(fphi, phi)
      L = lines(NP)
      L1 = sort(L, rev = true, by = x -> slope(x))
      for l in L1
        if l == L1[end]
          fact[fphi] = v
          break
        end
        s = slope(l)
        mu = divexact(phi^Int(denominator(s)), uniformizer(K)^(-(Int(numerator(s)))))
        chi = characteristic_polynomial(fphi, mu)
        hchi = Hensel_factorization(chi)
        for (ppp, fff) in hchi
          if ppp == gen(Kt)
            continue
          end
          com = fff(mu)
          com = divexact(com, _content(com))
          gc = gcd(com, fphi)
          fact[gc] = v
          fphi1 = divexact(fphi, gc)
          if gc*fphi1 != fphi
            error("problem!")
          end
          fphi = fphi1
        end
      end
    end
  end
  return fact
end

function newton_test(mu::Generic.Poly{T}, f::Generic.Poly{T}) where T <: Union{padic, qadic, LocalFieldElem}
  s = characteristic_polynomial(f, mu)
  N = newton_polygon(s, gen(parent(s)))
  pols = typeof(f)[]
  if isone_sided(N)
    return true, pols
  end
  lf = slope_factorization(s)
  for g in keys(lf)
    push!(pols, gcd(g(mu), f))
  end
  @assert prod(pols) == f
  return false, pols
end

function hensel_test(mu::Generic.Poly{T}, f::Generic.Poly{T}) where T <: Union{padic, qadic, LocalFieldElem}
  s = characteristic_polynomial(f, mu)
  lf = Hensel_factorization(s)
  if length(lf) == 1
    return true, typeof(f)[first(keys(lf))]
  end
  pols = typeof(f)[]
  for g in values(lf)
    push!(pols, gcd(g(mu), f))
  end
  @assert prod(pols) == f
  return false, pols
end

function _compute_EF_phi(phi::Generic.Poly{T}, f::Generic.Poly{T}) where T <: Union{padic, qadic, LocalFieldElem}
  K = base_ring(phi)
  e = absolute_ramification_index(K)
  s = characteristic_polynomial(f, mu)
  E = Int(denominator(fmpq(Int(valuation(constant_coefficient(s))*absolute_ramification_index), degree(s))))
  k, mk = ResidueField(K)
  sp = map_coefficients(mk, s)
  sq = factor_squarefree(sp)
  @assert length(sq) == 1
  F = degree(first(keys(sq)))
  return E, F
end

function _factor(f::Generic.Poly{T}) where T <: Union{padic, qadic, LocalFieldElem}
  Kx = parent(f)
  K = base_ring(Kx)
  phi = gen(Kx)
  E = 1
  tf = typeof(f)
  pols = tf[]
  res = Tuple{tf, Tuple{tf, tf}}[]
  while true
    fl, facts = newton_test(phi, f)
    if !fl
      for g in facts
        append!(res, _factor(g))
      end
      return res
    end
    Ephi, Fphi = _compute_EF_phi(phi, f)
    if !divides(E, Ephi)[1]
      push!(pols, phi)
      S = divexact(lcm(E, Ephi), E)
      E = S*E
      phi = phi^S
      if E == deg(f1)
        #Produce a certificate...
      end


      fl, facts = hensel_test(gamma, f)
      if !fl
        for g in facts
          append!(res, _factor(g))
        end
        return res
      end
      if degree(facts[1])*E == degree(f)
        #Produce a certificate
      end
      if degree(facts[1]) > 1
        #Extend the base field
        F, gF = unramified_extension(K, degree(facts[1]), precision(K))
        fF = map_coefficients(F, f) 
        lf = Hensel_factorization(fF)
        fnew = first(values(lf))
        lfF = _factor()
      end
    end

  
  end
  

  

end
