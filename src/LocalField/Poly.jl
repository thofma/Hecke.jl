
add_assert_scope(:padic_poly)

@doc Markdown.doc"""
    lift(a::T, K::PadicField) where T <: Union{Nemo.nmod, Generic.Res{fmpz}, gfp_elem} -> padic

Computes a lift of the element from the residue ring.
"""
function lift(a::T, K::PadicField) where T <: Union{Nemo.nmod, Generic.Res{fmpz}, gfp_elem}
  n = modulus(parent(a))
  p = prime(K)
  v, fl = remove(n, p)
  @assert isone(fl)
  return Hecke.lift(a) + O(K, p^v)
end

@doc Markdown.doc"""
    lift(f::T, Kt) where T <: Union{nmod_poly, fmpz_mod_poly, gfp_poly} -> Generic.Poly{padic}

Computes a lift of the polynomial lifting every coefficient of the residue ring.
"""
function lift(f::T, Kt) where T <: Union{nmod_poly, fmpz_mod_poly, gfp_poly}
  K = base_ring(Kt)
  coeffs = Vector{padic}(undef, degree(f)+1)
  for i = 1:degree(f)+1
    coeffs[i] = lift(coeff(f, i-1), K)
  end
  return Kt(coeffs)
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

function _content(f::Generic.Poly{T}) where T <: Union{padic, qadic}
  K = base_ring(f)
  p = uniformizer(K)
  v = valuation(coeff(f, 0))
  for i = 1:degree(f)
    v = min(v, valuation(coeff(f, i)))
  end
  return p^v
end

function rem!(x::AbstractAlgebra.Generic.Poly{T}, y::AbstractAlgebra.Generic.Poly{T}, z::AbstractAlgebra.Generic.Poly{T}) where T <:Union{padic, qadic}
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
  return lift(u, Kt), lift(g1, Kt)
end

function fun_factor(f::Generic.Poly{qadic})
  K = base_ring(f)
  Kt = parent(f)
  v = precision(f)
  @assert isone(_content(f))
  if iszero(valuation(lead(f)))
    return one(Kt), g
  end
  ind = degree(f) -1
  while !iszero(valuation(coeff(f, ind)))
    ind -= 1
  end
  g = Kt([coeff(f, i) for i = ind:degree(f)])
  h = Kt([divexact(coeff(f, i), coeff(f, ind)) for i = 0:ind])
  s = Kt(inv(coeff(g, 0)))
  t = zero(Kt)
  k = Int(clog(fmpz(v), 2))+1
  for i = 1:k
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
  return g, h
end

################################################################################
#
#  Gcd
#
################################################################################

function Nemo.precision(g::Generic.Poly{T}) where T <: Union{padic, qadic}
  N = coeff(g, 0).N
  for i = 1:degree(g)
    N = min(N, coeff(g, i).N)
  end
  return N
end


function Base.gcd(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{padic, qadic}
  if degree(f) < degree(g)
    f, g = g, f
  end
  while true
    cf = _content(f)
    if !isone(cf)
      f = divexact(f, cf)
    end
    cg = _content(g)
    if !isone(cg)
      g = divexact(g, cg)
    end
    if !iszero(valuation(lead(g)))
      u, g1 = fun_factor(g)
      if iszero(valuation(lead(f)))
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
        return divexact(f, lead(f))
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
  if !iszero(valuation(lead(f)))
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
  return lift(iuR, Kt)
end

function invmod(f::Generic.Poly{qadic}, M::Generic.Poly{qadic})
  if !iszero(valuation(lead(M)))
    error("Not yet implemented")
  end
  f = rem(f, M)
  if !iszero(valuation(coeff(f, 0))) || !all(x -> x > 0, [valuation(coeff(f, i)) for i = 1:degree(f)])
    g, s, t = gcdx(f, M)
    return s
  end
  K = base_ring(f)
  Kt = parent(f)
  v = min(precision(f), precision(M))
  g = parent(f)(inv(trailing_coefficient(f)))
  c = f*g
  c = rem!(c, c, M)
  while !isone(c)
    g = mul!(g, g, 2-c)
    g = rem!(g, g, M)
    c = mul!(c, f, g)
    c = rem!(c, c, M)
  end
  return g
end


################################################################################
#
#  xgcd
#
################################################################################

#TODO: The implementation is recursive. Change it to an iterative implementation.
function gcdx(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{padic, qadic}
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
  if iszero(valuation(lead(g)))
    q, f1 = divrem(f, g)
    d, u, v = gcdx(g, f1)
    @hassert :padic_poly 1  d == f*v+(u-v*q)*g
    return d, v, u-v*q
  end
  ug, gg = fun_factor(g)
  if iszero(valuation(lead(f)))
    s = invmod(ug, f)
    t = divexact(1-s*ug, f)
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

function divexact(f::AbstractAlgebra.PolyElem{T}, g::AbstractAlgebra.PolyElem{T}) where T<: Union{padic, qadic}
   check_parent(f, g)
   f1 = deepcopy(f)
   g1 = deepcopy(g)
   iszero(g) && throw(DivideError())
   if iszero(f)
      return zero(parent(f))
   end
   lenq = length(f) - length(g) + 1
   d = Array{T}(undef, lenq)
   for i = 1:lenq
      d[i] = zero(base_ring(f))
   end
   x = gen(parent(f))
   leng = length(g)
   while length(f) >= leng
      lenf = length(f)
      q1 = d[lenf - leng + 1] = divexact(coeff(f, lenf - 1), coeff(g, leng - 1))
      f = f - shift_left(q1*g, lenf - leng)
      if length(f) == lenf # inexact case
         set_length!(f, normalise(f, lenf - 1))
      end
   end
   q = parent(f)(d)
   set_length!(q, lenq)
   K = base_ring(f)
   Kt = parent(f)
   p = prime(K)
   while !iszero(q*g1 - f1)
     q = Kt(T[coeff(q, i) + O(K, p^(precision(q)-1)) for i = 0:degree(q)])
   end
   return q
end



################################################################################
#
#  Resultant and characteristic polynomial
#
################################################################################

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

function resultant(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{padic, qadic}
  Nemo.check_parent(f, g)
  Rt = parent(f)
  R = base_ring(Rt)
  res = one(R)

  while true
    if degree(f) < 1 && degree(g) < 1
      if iszero(f) || iszero(g)
        return res *= zero(R)
      end
      return res
    end

    if degree(f) < 1
      res *= lead(f)^degree(g)
      return res
    end

    if degree(g) < 1
      res *= lead(g)^degree(f)
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

    if isunit(lead(g))
      r = rem(f, g)
      res *= lead(g)^(degree(f) - degree(r))
      if !iszero(mod(degree(g)*(degree(f) - degree(r)), 2))
        res = -res
      end
      f = r
    else
      break
    end
  end

  g1, g2 = fun_factor(g)
  res1 = resultant(f, g2)
  g1r = reverse(g1)
  fr = reverse(f)
  res2 = (constant_coefficient(g1)^(degree(f)- degree(fr)))*resultant(fr, g1r)
  return res*res1*res2
end

degree(::FlintPadicField) = 1

@doc Markdown.doc"""
    characteristic_polynomial(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{padic, qadic} -> Generic.Poly{T}

Computes $\mathrm{Res}_x(f(x), t- g(x))$.
"""
function characteristic_polynomial(f::Generic.Poly{padic}, g::Generic.Poly{padic})
  Kt = parent(f)
  Ktx, x = PolynomialRing(Kt, "x")
  fcoeffs = Generic.Poly{padic}[Kt(coeff(f, i)) for i = 0:degree(f)]
  gcoeffs = Generic.Poly{padic}[Kt(-coeff(g, i)) for i = 0:degree(g)]
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
function Hensel_factorization(f::Generic.Poly{T}) where T <: Union{padic, qadic}
  D = Dict{Generic.Poly{T}, Generic.Poly{T}}()
  Kt = parent(f)
  K = base_ring(Kt)
  k, mk = ResidueField(K)
  kt = PolynomialRing(k, "t", cached = false)[1]
  fp = kt([mk(coeff(f, i)) for i = 0:degree(f)])
  lfp = factor(fp).fac
  if length(lfp) == 1
    #The Hensel factorization is trivial...
    phi = setprecision(lift(first(keys(lfp)), Kt), precision(f))
    D[phi] = f
    return D
  end
  vlfp = Vector{dense_poly_type(elem_type(k))}(undef, length(lfp))
  ind = 1
  ks = Vector{Generic.Poly{T}}(undef, length(vlfp))
  for (k1, v) in lfp
    vlfp[ind] = k1^v
    ks[ind] = setprecision(lift(k1, Kt), precision(f))
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
      push!(la, map_coeffs(x -> setprecision(lift(x, Q), 1), a, parent = Qx))
      push!(la, map_coeffs(x -> setprecision(lift(x, Q), 1), b, parent = Qx))
      push!(lfp, f1*f2)
      i += 2
    end
    return new(f, map(x -> map_coeffs(y -> setprecision(lift(y, Q), 1), x, parent = Qx), lfp), la, uniformizer(Q), n)
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
  N = valuation(p)
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
function slope_factorization(f::Generic.Poly{T}) where T <: Union{padic, qadic}

  K = base_ring(f)
  Kt = parent(f)
  fact = Dict{Generic.Poly{T}, Int}()
  cf = _content(f)
  f = divexact(f, cf)
  if !iszero(valuation(lead(f)))
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
      NP = NewtonPolygon(fphi, phi)
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
