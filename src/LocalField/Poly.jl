add_assertion_scope(:padic_poly)

################################################################################
#
#  setprecision
#
################################################################################


function setprecision_fixed_precision(f::Generic.Poly{QadicFieldElem}, N::Int)
  f = setprecision(f, N)
  return f
end

function setprecision_fixed_precision(a::LocalFieldElem, n::Int)
  return setprecision(a, n)
end

function Nemo.setprecision(f::Generic.Poly{<:LocalFieldElem}, n::Int)
  f = map_coefficients(x->setprecision(x, n), f, parent = parent(f))
  @assert iszero(f) || !iszero(f.coeffs[f.length])
  return f
end

function setprecision!(f::Generic.Poly{<:LocalFieldElem}, n::Int)
  for i = 1:length(f.coeffs)
    f.coeffs[i] = setprecision(f.coeffs[i], n)
  end
  set_length!(f, normalise(f, length(f)))
  @assert iszero(f) || !iszero(f.coeffs[f.length])
  return f
end

function setprecision_fixed_precision(f::Generic.Poly{<:LocalFieldElem}, n::Int)
  fr = map_coefficients(x -> setprecision_fixed_precision(x, n), f, parent = parent(f))
  @assert iszero(fr) || !iszero(fr.coeffs[fr.length])
  return fr
end

#in the local case, we have to also set coeffs to 0
#otherwise the precision is lost:
#an empty poly is "filled" with 0 in precision of the ring
#a zero (in a) might have a different precision....
function setcoeff!(c::Generic.Poly{T}, n::Int, a::T) where {T <: Union{PadicFieldElem, QadicFieldElem, Hecke.LocalFieldElem}}
   fit!(c, n + 1)
   c.coeffs[n + 1] = a
   c.length = max(length(c), n + 1)
   return c
end

#TODO: find better crossover points
#  qp = PadicField(3, 10);
#  qpt, t = qp["t"]
#  E = eisenstein_extension(cyclotomic(3, gen(Hecke.Globals.Zx))(t+1))[1]
#  Es, s = E["s"]
#  roots(s^9-1) #at precision 100, drops from 3 to 1 sec..
function Nemo.use_karamul(a::PolyRingElem{T}, b::PolyRingElem{T}) where T <: Union{PadicFieldElem, QadicFieldElem, Hecke.LocalFieldElem}

   return length(a) > 50 && length(b) > 50
end

################################################################################
#
#  Lift
#
################################################################################

@doc raw"""
    lift(a::T, K::PadicField) where T <: Union{Nemo.zzModRingElem, EuclideanRingResidueRingElem{ZZRingElem}, fpFieldElem} -> PadicFieldElem

Computes a lift of the element from the residue ring.
"""
function lift(a::T, K::PadicField) where T <: Union{Nemo.zzModRingElem, Nemo.ZZModRingElem, EuclideanRingResidueRingElem{ZZRingElem}, fpFieldElem}
  n = modulus(parent(a))
  p = prime(K)
  v, fl = remove(n, p)
  @assert isone(fl)
  return Hecke.lift(a) + O(K, p^v)
end

function lift(a::FqFieldElem, K::PadicField)
  return Hecke.lift(ZZ, a) + O(K, prime(K))
end

function lift(a::FinFieldElem, K::LocalField)
  k, mk = residue_field(K)
  @assert k === parent(a)
  return mk\a
end


@doc raw"""
    lift(f::T, Kt) where T <: Union{zzModPolyRingElem, ZZModPolyRingElem, fpPolyRingElem} -> Generic.Poly{PadicFieldElem}

Computes a lift of the polynomial lifting every coefficient of the residue ring.
"""
function lift(f::T, Kt::PolyRing) where T <: FinFieldElem
  return map_coefficients(x -> lift(x, K), f, Kt)
end

@doc raw"""
    lift(x::fqPolyRepFieldElem, Q::QadicField) -> QadicFieldElem

Computes a lift of the element from the residue ring.
"""
function lift(x::fqPolyRepFieldElem, Q::QadicField)
  z = Q()
  for i=0:degree(Q)-1
    setcoeff!(z, i, coeff(x, i))
  end
  return setprecision(z, 1)
end

@doc raw"""
    lift(x::fqPolyRepPolyRingElem, Kt) -> Generic.Poly{QadicFieldElem}

Computes a lift of the polynomial lifting every coefficient of the residue ring.
"""
function lift(x::fqPolyRepPolyRingElem, Kt)
  K = base_ring(Kt)
  coeffs = Vector{QadicFieldElem}(undef, degree(x)+1)
  for i = 1:degree(x)+1
    coeffs[i] = lift(coeff(x, i-1), K)
  end
  return Kt(coeffs)
end

function _content(f::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}
  K = base_ring(f)
  @assert !iszero(f)
  c = coeff(f, 0)
  i = 0
  while iszero(c)
    i += 1
    i > length(f) && error("bad poly")
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

function rem!(x::AbstractAlgebra.Generic.Poly{T}, y::AbstractAlgebra.Generic.Poly{T}, z::AbstractAlgebra.Generic.Poly{T}) where {T<:LocalFieldElem}
  x = rem(y, z)
  return x
end

################################################################################
#
#  Fun factor
#
################################################################################

function fun_factor(g::Generic.Poly{PadicFieldElem})
  K = base_ring(g)
  Kt = parent(g)
  v = precision(g)
  pv = prime(K)^v
  R = residue_ring(FlintZZ, pv, cached = false)[1]
  Rt = polynomial_ring(R, "t", cached = false)[1]
  fR = Rt([R(Hecke.lift(ZZ, coeff(g, i))) for i = 0:degree(g)])
  u, g1 = Hecke.fun_factor(fR)
  liftu = Kt(elem_type(K)[lift(coeff(u, i), K) for i in 0:degree(u)])
  liftg1 = Kt(elem_type(K)[lift(coeff(g1, i), K) for i in 0:degree(g1)])
  return (liftu, liftg1)::Tuple{typeof(g), typeof(g)}
end

function fun_factor(f::Generic.Poly{S}) where S <: Union{QadicFieldElem, LocalFieldElem}
  K = base_ring(f)
  Kt = parent(f)
  v = precision(f)
  f = setprecision_fixed_precision(f, v)
  @assert isone(_content(f))
  if iszero(valuation(leading_coefficient(f)))
    return one(Kt), f
  end
  ind = degree(f) -1
  while iszero(coeff(f, ind)) || !iszero(valuation(coeff(f, ind)))
    ind -= 1
  end
  g = setprecision_fixed_precision(Kt(S[coeff(f, i) for i = ind:degree(f)]), 1)
  h = setprecision_fixed_precision(Kt(S[divexact(coeff(f, i), coeff(f, ind)) for i = 0:ind]), 1)
  s = setprecision_fixed_precision(Kt(inv(coeff(g, 0))), 2)
  t = setprecision_fixed_precision(zero(Kt), 2)
  ch = Int[v]
  while ch[end] > 2
    push!(ch, div(ch[end]+1, 2))
  end
  reverse!(ch)
  for pr = 1:length(ch)
    i = ch[pr]
    g = setprecision_fixed_precision(g, i)
    h = setprecision_fixed_precision(h, i)
    s = setprecision_fixed_precision(s, i)# ch[pr+1])
    t = setprecision_fixed_precision(t, i)# ch[pr+1])
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
  return g, h
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


function Nemo.precision(g::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem}
  N = precision(coeff(g, 0))
  for i = 1:degree(g)
    N = min(N, precision(coeff(g, i)))
  end
  return N
end


function Base.gcd(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}
  if degree(f) < degree(g)
    f, g = g, f
  end
  if iszero(f)
    return g::Generic.Poly{T}
  end
  if iszero(g)
    return f::Generic.Poly{T}
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
        return (reverse(gcd(reverse(u), reverse(v)))*gcd(f1, g1))::Generic.Poly{T}
      end
    end
    f = mod(f, g)
    if degree(f) < 1
      if iszero(f)
        return divexact(g, leading_coefficient(g))::Generic.Poly{T}
      else
        return divexact(f, leading_coefficient(f))::Generic.Poly{T}
      end
    else
      f, g = g, f
    end
  end
  error("cannot be reached")
end

################################################################################
#
#  Invmod
#
################################################################################

function invmod(u::Generic.Poly{PadicFieldElem}, f::Generic.Poly{PadicFieldElem})
  if !iszero(valuation(leading_coefficient(f)))
    error("Not yet implemented")
  end
  if !iszero(valuation(coeff(u, 0))) || !all(x -> x > 0, Int[valuation(coeff(u, i)) for i = 1:degree(u)])
    s = gcdx(u, f)[2]::Generic.Poly{PadicFieldElem}
    return s
  end
  K = base_ring(f)
  Kt = parent(f)
  v = min(precision(f), precision(u))
  vu = maximum(valuation, coefficients(u))
  v += max(maximum(valuation, coefficients(f)), vu)
  #= The Problem:
    in R = Z/p^v everything is killed at precision v (fixed precision)
    but in K not: (p+O(p^v)) is never 0
    invmod needs to have enough precision to allow for all coefficients
    of the product to be "correct"
    s = invmod(u, f)
    then
    s*u = 1 mod f
    up to the precision of f and u
    e.g. if u has valuation in the leading coeff, then this causes problems
  =#
  while true
    pv = prime(K)^v
    R = residue_ring(FlintZZ, pv, cached = false)[1]
    Rt = polynomial_ring(R, "t", cached = false)[1]
    fR = Rt(elem_type(R)[R(Hecke.lift(ZZ, coeff(f, i))) for i = 0:degree(f)])
    uR = Rt(elem_type(R)[R(Hecke.lift(ZZ, coeff(u, i))) for i = 0:degree(u)])
    iuR = invmod(uR, fR)
    s = map_coefficients(x -> lift(x, K), iuR, parent = Kt)
    if maximum(valuation, coefficients(s)) + vu < v
      return s
    end
    v *= 2
    #TODO: maybe use lifting instead of invmod?
    # as done below?
  end
end

function invmod(f::Generic.Poly{T}, M1::Generic.Poly{T}) where T <: Union{QadicFieldElem, LocalFieldElem}
  @assert !iszero(f)
  if !iszero(valuation(leading_coefficient(M1)))
    error("Not yet implemented")
  end
  M = setprecision(M1, precision(M1))
  f = rem(f, M)
  if iszero(coeff(f, 0)) || !iszero(valuation(coeff(f, 0))) || !all(x -> x >= 0, [valuation(coeff(f, i)) for i = 1:degree(f) if !iszero(coeff(f, i))])
    s = gcdx(f, M)[2]
    return s
  end

  K = base_ring(f)
  Kt = parent(f)
  k, mk = residue_field(K)
  fk = map_coefficients(mk, f, cached = false)
  M1k = map_coefficients(mk, M1, parent = parent(fk))
  invc = map_coefficients(x->preimage(mk, x), invmod(fk, M1k), parent = parent(f))
  g = invc
  c = f*g
  c = rem!(c, c, M)
  i = 1
  while !isone(c)
    g = mul!(g, g, 2-c)
    g = rem!(g, g, M)
    c = mul!(c, f, g)
    c = rem!(c, c, M)
    c = setprecision!(c, precision(M))
    @assert precision(c) == precision(M)
    i += 1
    if i > nbits(precision(M))+1
      error("lifting did not converge")
    end
  end
  return g
end


################################################################################
#
#  xgcd
#
################################################################################

#TODO: The implementation is recursive. Change it to an iterative implementation.
function gcdx(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}
  if degree(f) < degree(g)
    r1, r2, r3 = gcdx(g, f)::Tuple{Generic.Poly{T}, Generic.Poly{T}, Generic.Poly{T}}
    return (r1, r3, r2)::Tuple{Generic.Poly{T}, Generic.Poly{T}, Generic.Poly{T}}
  end
  Kx = parent(f)
  if length(g) <= 1
    if iszero(g)
      return (f, one(Kx), zero(Kx))::Tuple{Generic.Poly{T}, Generic.Poly{T}, Generic.Poly{T}}
    else
      s = Kx(inv(coeff(g, 0)))
      @hassert :padic_poly one(Kx) == s*g
      return (one(Kx), zero(Kx), s)::Tuple{Generic.Poly{T}, Generic.Poly{T}, Generic.Poly{T}}
    end
  end
  cf = _content(f)
  if !isone(cf)
    f1 = divexact(f, cf)
    d, u, v = gcdx(f1, g)::Tuple{Generic.Poly{T}, Generic.Poly{T}, Generic.Poly{T}}
    @hassert :padic_poly 1 f*divexact(u, cf) + v*g == d
    return (d, divexact(u, cf), v)::Tuple{Generic.Poly{T}, Generic.Poly{T}, Generic.Poly{T}}
  end
  cg = _content(g)
  if !isone(cg)
    g1 = divexact(g, cg)
    d, u, v = gcdx(f, g1)::Tuple{Generic.Poly{T}, Generic.Poly{T}, Generic.Poly{T}}
#    @show f*u+divexact(v, cg)*g - d
#    @hassert :padic_poly 1  f*u+divexact(v, cg)*g == d
# tricky: fails the tests as the precision is not large enough
    return (d, u, divexact(v, cg))::Tuple{Generic.Poly{T}, Generic.Poly{T}, Generic.Poly{T}}
  end
  if iszero(valuation(leading_coefficient(g)))
    q, f1 = divrem(f, g)
    d, u, v = gcdx(g, f1)::Tuple{Generic.Poly{T}, Generic.Poly{T}, Generic.Poly{T}}
    @hassert :padic_poly 1  d == f*v+(u-v*q)*g
    return (d, v, u-v*q)::Tuple{Generic.Poly{T}, Generic.Poly{T}, Generic.Poly{T}}
  end
  ug, gg = fun_factor(g)
  if iszero(valuation(leading_coefficient(f)))
    s = invmod(ug, f)
    to_be_div = setprecision(one(Kx)-s*ug, precision(f))
    t = divexact(to_be_div, f)
    @hassert :padic_poly 1  t*f == 1-s*ug
    d, u, v = gcdx(f, gg)::Tuple{Generic.Poly{T}, Generic.Poly{T}, Generic.Poly{T}}
    @hassert :padic_poly 1  d == u*f + v*gg
    @hassert :padic_poly 1  d == (u+v*t*gg)*f + v*s*g
    return (d, u+v*t*gg, v*s)::Tuple{Generic.Poly{T}, Generic.Poly{T}, Generic.Poly{T}}
  end
  uf, ff = fun_factor(f)
  d, u, v = gcdx(ff, gg)::Tuple{Generic.Poly{T}, Generic.Poly{T}, Generic.Poly{T}}
  if degree(gg) >= 1
    s = invmod(uf, gg)
    t = divexact(one(Kx)-s*uf, gg)
    @hassert :padic_poly 1  t*gg == 1-s*uf
  else
    #gg = 1. Easy to compute Bezout coefficients...
    s = zero(Kx)
    t = one(Kx)
  end
  U = u*s
  V = u*ff*t + v*t*gg+s*uf*v
  d1, u1, v1 = gcdx(reverse(uf), reverse(ug))::Tuple{Generic.Poly{T}, Generic.Poly{T}, Generic.Poly{T}}
  d1 = reverse(d1)
  u1 = reverse(u1)
  v1 = reverse(v1)
  @hassert :padic_poly 1  d1 == u1*uf+v1*ug
  if degree(ff) >= 1
    t1 = invmod(ug, ff)
    s1 = divexact(one(Kx)-t1*ug, ff)
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
  return (DD, UU, VV)::Tuple{Generic.Poly{T}, Generic.Poly{T}, Generic.Poly{T}}
end

function divexact(f1::AbstractAlgebra.PolyRingElem{T}, g1::AbstractAlgebra.PolyRingElem{T}; check::Bool=true) where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}
   check_parent(f1, g1)
   iszero(g1) && throw(DivideError())
   if iszero(f1)
      return zero(parent(f1))
   end
   lenq = length(f1) - length(g1) + 1
   if lenq < 0
     error("division not exact")
   end
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
     pr = precision(q)
     q = setprecision(q, pr-1)
     if iszero(q)
       error("division was not exact:\n$f1\nby\n$g1")
     end
     @assert precision(q) < pr
   end
   return q
end



################################################################################
#
#  Resultant and characteristic polynomial
#
################################################################################

reduced_resultant(f::T, g::T) where T <: PolyRingElem = rres(f, g)
reduced_discriminant(f::PolyRingElem) = rres(f, derivative(f))

function rres(f::Generic.Poly{PadicFieldElem}, g::Generic.Poly{PadicFieldElem})
  Kt = parent(f)
  K = base_ring(Kt)
  p = prime(K)
  v = min(precision(f), precision(g))
  R = residue_ring(FlintZZ, p^v, cached = false)[1]
  cf = Vector{elem_type(R)}(undef, degree(f)+1)
  for i = 1:length(cf)
    cf[i] = R(Hecke.lift(ZZ, coeff(f, i-1)))
  end
  cg = Vector{elem_type(R)}(undef, degree(g)+1)
  for i = 1:length(cg)
    cg[i] = R(Hecke.lift(ZZ, coeff(g, i-1)))
  end
  Rt = polynomial_ring(R, "t", cached = false)[1]
  r = Hecke.rres_sircana_pp(Rt(cf), Rt(cg))
  return lift(r, K)
end


function resultant(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}
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

function check_data(a::LocalFieldElem)
  iszero(a) ||!iszero(a.data.coeffs[a.data.length]) || error("elem inconsistent")
end
function check_data(f::Generic.Poly{<:LocalFieldElem})
  map(check_data, coefficients(f))
end
function check_data(f::Generic.Poly{PadicFieldElem})
end
function check_data(f::Generic.Poly{QadicFieldElem})
end

function _resultant(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}
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

function rres(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{QadicFieldElem, LocalFieldElem}
  Nemo.check_parent(f, g)
  @assert is_monic(f) || is_monic(g) "One of the two polynomials must be monic!"
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
  @assert isone(c1) || isone(c2) "One of the two polynomials must be monic!"
  return res * _rres(f, g)
end

function _rres(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}
  Rt = parent(f)
  R = base_ring(Rt)
  res = one(R)
  e = absolute_ramification_index(R)
  while true
    if degree(f) < 1 && degree(g) < 1
      return uniformizer(R)^min(valuation(coeff(f, 0)), valuation(coeff(g, 0)))
    elseif degree(f) < 1
      v = numerator(e*valuation(coeff(f, 0)))
      if iszero(v)
        return res
      end
      for j = 1:degree(g)
        if !iszero(coeff(g, j)) && e*valuation(coeff(g, j)) < v
          return res*uniformizer(R)^v
        end
      end
      res *= uniformizer(R)^min(v, numerator(e*valuation(coeff(g, 0))))
      return res
    elseif degree(g) < 1
      v = numerator(e*valuation(coeff(g, 0)))
      if iszero(v)
        return res
      end
      for j = 1:degree(f)
        if !iszero(coeff(f, j)) && numerator(e*valuation(coeff(f, j))) < v
          return res*uniformizer(R)^v
        end
      end
      res *= uniformizer(R)^min(v, numerator(e*valuation(coeff(f, 0))))
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

    if iszero(valuation(leading_coefficient(g)))
      f = rem(f, g)
    else
      break
    end
  end
  g1, g2 = fun_factor(g)
  res1 = _rres(f, g2)
  return res*res1
end

base_field(Q::QadicField) = base_ring(defining_polynomial(Q))

function norm(f::PolyRingElem{T}) where T <: Union{QadicFieldElem, LocalFieldElem}
  Kx = parent(f)
  K = base_ring(f)
  f, i = deflate(f)
  P = polynomial_to_power_sums(f, degree(f)*degree(K))
  PQ = elem_type(base_field(K))[tr(x) for x in P]
  N = power_sums_to_polynomial(PQ)
  return inflate(N, i)
end

@doc raw"""
    characteristic_polynomial(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem} -> Generic.Poly{T}

Computes $\mathrm{ResidueRingElem}_x(f(x), t- g(x))$.
"""
function characteristic_polynomial(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}
  Kt = parent(f)
  Ktx, x = polynomial_ring(Kt, "x")
  fcoeffs = typeof(f)[Kt(coeff(f, i)) for i = 0:degree(f)]
  gcoeffs = typeof(f)[Kt(-coeff(g, i)) for i = 0:degree(g)]
  f1 = Ktx(fcoeffs)
  g1 = Ktx(gcoeffs) + gen(Kt)
  return resultant(f1, g1)
end

#=
function characteristic_polynomial(f::Generic.Poly{T}, g::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem}
  K = base_ring(f)
  Kt = parent(f)
  p = prime(K)
  d = degree(K)
  if p^d <= degree(f)
    if d > 1
      error("Not yet implemented")
    end
    d1 = clog(ZZRingElem(degree(f)+1), p)
    L = QadicField(p, d1, min(precision(f), precision(g)))
    Lt = polynomial_ring(L, "t")[1]
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
  k, mk = residue_field(K)
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
@doc raw"""
    Hensel_factorization(f::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem} -> Dict{Generic.Poly{T}, Generic.Poly{T}}

Computes a factorization of $f$ such that every factor has a unique irreducible factor over the residue field.
The output is a dictionary whose keys are lifts of the irreducible factors over the residue field and values the corresponding factors of $f$.
"""
function Hensel_factorization(f::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}
  cf = _content(f)
  f = divexact(f, cf)
  Kt = parent(f)
  D = Dict{Generic.Poly{T}, Generic.Poly{T}}()
  _f = f
  if !iszero(valuation(leading_coefficient(f)))
    vf, f = fun_factor(f)
  else
    vf = one(Kt)
  end
  @assert iszero(valuation(leading_coefficient(f)))
  K = base_ring(Kt)
  k, mk = residue_field(K)
  kt = polynomial_ring(k, "t", cached = false)[1]
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
    D[ks[i]] = setprecision(H.lf[i], precision(f))
  end
  return D
end


mutable struct HenselCtxdr{S}
  f::PolyRingElem{S}
  lf::Vector{PolyRingElem{S}}
  la::Vector{PolyRingElem{S}}
  p::S #always the uniformizer
  n::Int

  function HenselCtxdr{QadicFieldElem}(f::Generic.Poly{QadicFieldElem}, lfp::Vector{Generic.Poly{QadicFieldElem}}, la::Vector{Generic.Poly{QadicFieldElem}}, p::QadicFieldElem, n::Int)
    @assert p == uniformizer(parent(p))
    return new(f, lfp, la, p, n)
  end

  function HenselCtxdr{T}(f::S, lfp::Vector{S}) where {S <: PolyRingElem{T}} where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}
    # @assert sum(map(degree, lfp)) == degree(f)
#    if sum(map(degree, lfp)) < degree(f)
#      push!(lfp, one(parent(lfp[1])))
#    end
    Q = base_ring(f)
    Qx = parent(f)
    i = 1
    la = Vector{S}()
    n = length(lfp)
    while i < length(lfp)
      f1 = lfp[i]
      f2 = lfp[i+1]
      g, a, b = gcdx(f1, f2)
      @assert isone(g)
      push!(la, a)
      push!(la, b)
      push!(lfp, f1*f2)
      i += 2
    end
    return new(f, lfp, la, uniformizer(Q), n)
  end

  function HenselCtxdr{S}(f::PolyRingElem{S}, lfp::Vector{T}) where {S, T}
#    if sum(map(degree, lfp)) < degree(f)
#      push!(lfp, one(parent(lfp[1])))
#    end
#    @assert sum(map(degree, lfp)) == degree(f)
    Q = base_ring(f)
    Qx = parent(f)
    @assert residue_field(Q)[1] === coefficient_ring(lfp[1])
    k, Qtok = residue_field(Q)
    i = 1
    la = Vector{typeof(f)}()
    n = length(lfp)
    while i < length(lfp)
      f1 = lfp[i]
      f2 = lfp[i+1]
      g, a, b = gcdx(f1, f2)
      @assert isone(g)
      push!(la, map_coefficients(x -> setprecision(Qtok\x, 1), a, parent = Qx))
      push!(la, map_coefficients(x -> setprecision(Qtok\x, 1), b, parent = Qx))
      push!(lfp, f1*f2)
      i += 2
    end
    return new(f, map(x -> map_coefficients(y -> setprecision(Qtok\y, 1), x, parent = Qx), lfp), la, uniformizer(Q), n)
  end

  function HenselCtxdr{S}(f::PolyRingElem{S}) where S
    Q = base_ring(f)
    K, mK = residue_field(Q)
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
  if length(C.lf) == 1
    return nothing
  end
  N = minimum([precision(x) for x in C.lf])
  N = min(N, minimum([precision(x) for x in C.la]))
  #have: N need mx
  one = setprecision(parent(p), mx) do
    Base.one(parent(p))
  end
  ch = Int[mx]
  while ch[end] > N
    push!(ch, div(ch[end]+1, 2))
  end
  e = absolute_ramification_index(parent(p))
  @vprintln :PolyFactor 1 "using lifting chain $ch"
  for k=length(ch)-1:-1:1
    N2 = ch[k]
    N2 += e - mod(N2, e)
    i = length(C.lf)
    j = i-1

    p = uniformizer(parent(p), ch[k+1], prec = N2)
    ip = uniformizer(parent(p), -ch[k+1], prec = N2)
#    _mp = map(x-> iszero(x) ? -1 : valuation(x), coefficients(prod(setprecision(x, mx) for x = C.lf[1:C.n]) - C.f))
#      @show _mp, valuation(p)
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
      fgh = (f-g*h)*ip
      G = rem(fgh*b, g)*p+g
      H = rem(fgh*a, h)*p+h
      t = (one-a*G-b*H)*ip
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
#    _mp = map(x-> iszero(x) ? -1 : valuation(x), coefficients(prod(setprecision(x, mx) for x = C.lf[1:C.n]) - C.f))
#      @show _mp, valuation(p)
  return nothing
end

################################################################################
#
#  Slope factorization
#
################################################################################

@doc raw"""
    slope_factorization(f::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem} -> Dict{Generic.Poly{T}, Int}

Computes a factorization of $f$ such that every factor has a one-sided generalized Newton polygon.
The output is a dictionary whose keys are the factors of $f$ and the corresponding value is the multiplicity.
"""
function slope_factorization(f::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}

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
      factfphi = Vector{typeof(f)}()
      if degree(phi) == degree(fphi)
        fact[fphi] = v
        continue
      end
      fphi1 = fphi
      NP = newton_polygon(fphi, phi)
      L = lines(NP)
      L1 = sort(L, rev = true, by = x -> slope(x))
      last_s = QQFieldElem(0)
      for l in L1
        if l == L1[end]
          push!(factfphi, fphi1)
          break
        end
        s = slope(l)
#        nu = divexact(phi^Int(denominator(s)), uniformizer(K)^(-(Int(numerator(s)))))
        mu = phi^Int(denominator(s)) * uniformizer(K, Int(numerator(s)), prec = precision(phi))

        chi = characteristic_polynomial(fphi1, mu)
        hchi = Hensel_factorization(chi)
        for (ppp, fff) in hchi
          if ppp == gen(Kt)
            continue
          end
          com = fff(mu)
          com = divexact(com, _content(com))
          gc = gcd(com, fphi1)
          @assert degree(gc) > 0
          if degree(gc) < 1
            continue
          end
          push!(factfphi, gc)
          fphi1 = divexact(fphi1, gc)
        end
      end
      #factfphi = lift_factorization(fphi, factfphi)
      for fg in factfphi
        fact[fg] = v
      end
    end
  end
  return fact
end

function lift_factorization(f, factors)
  ctx = HenselCtxdr{elem_type(base_ring(f))}(f, copy(factors))
  lift(ctx, precision(f))
  return typeof(f)[ctx.lf[i] for i = 1:ctx.n]
end

################################################################################
#
#   Factorization
#
################################################################################

function newton_test(mu::Generic.Poly{T}, f::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}
  s = characteristic_polynomial(f, mu)
  N = newton_polygon(s, gen(parent(s)))
  pols = typeof(f)[]
  if is_one_sided(N)
    return true, pols
  end
  lf = slope_factorization(s)
  for g in keys(lf)
    push!(pols, gcd(g(mu), f))
  end
  @assert prod(pols) == f
  return false, pols
end

function hensel_test(mu::Generic.Poly{T}, f::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}
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

function _compute_EF_phi(phi::Generic.Poly{T}, f::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}
  K = base_ring(phi)
  e = absolute_ramification_index(K)
  s = characteristic_polynomial(f, mu)
  E = Int(denominator(QQFieldElem(Int(valuation(constant_coefficient(s))*absolute_ramification_index), degree(s))))
  k, mk = residue_field(K)
  sp = map_coefficients(mk, s, cached = false)
  sq = factor_squarefree(sp)
  @assert length(sq) == 1
  F = degree(first(keys(sq)))
  return E, F
end

function _factor(f::Generic.Poly{T}) where T <: Union{PadicFieldElem, QadicFieldElem, LocalFieldElem}
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
        fF = map_coefficients(F, f, cached = false)
        lf = Hensel_factorization(fF)
        fnew = first(values(lf))
        lfF = _factor()
      end
    end


  end




end
