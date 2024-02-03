"""
  The ring ZZ<x> := {c f/g | c in ZZ, f, g in ZZ[x], primitive, pos leading coeff}
  is a PID, even euclidean

  The key interest is
  IntCls(Z[x], F) = IntCls(Z<x>, F) cap IntCls(Q[x], F)
  Since Z<x> and Q[x] are PID (even euclidean) the last 2 can be
  computed using the Round2

  The name is bad, but stems from Florian Hess' PhD thesis,
  Chapter 2.10
  (Actually he covers that for a Dedekind ring R we have that
   R<x> is also Dedekind. The Round2, fundamentally would work
   for Dedekind rings, using PMats)
"""
module HessQRModule
using Hecke
import Hecke.AbstractAlgebra, Hecke.Nemo
import Base: +, -, *, gcd, lcm, divrem, div, rem, mod, ^, ==
export HessQR
import AbstractAlgebra: expressify

struct HessQR <: AbstractAlgebra.Ring
  R::ZZPolyRing
  Qt::Generic.RationalFunctionField{QQFieldElem}

  function HessQR(R::ZZPolyRing, Qt::Generic.RationalFunctionField)
    new(R, Qt)
  end
end

function Base.show(io::IO, R::HessQR)
  print(io, AbstractAlgebra.obj_to_string(R, context = io))
end

function expressify(R::HessQR; context = nothing)
  return Expr(:sequence, Expr(:text, "extended valuation ring over "),
                         expressify(R.R, context = context),
                         Expr(:text, " in "),
                         expressify(R.Qt, context = context))
end

mutable struct HessQRElem <: RingElem
  parent::HessQR
  c::ZZRingElem
  f::ZZPolyRingElem
  g::ZZPolyRingElem

  function HessQRElem(P::HessQR, c::ZZRingElem, f::ZZPolyRingElem, g::ZZPolyRingElem)
    if iszero(c) || iszero(f)
      r = new(P, ZZRingElem(0), zero(P.R), one(P.R))
      @assert parent(r.f) == P.R
      @assert parent(r.g) == P.R
      return r
    end
    if parent(f) != P.R
      f = map_coefficients(FlintZZ, f, parent = P.R)
    end
    if parent(g) != P.R
      g = map_coefficients(FlintZZ, g, parent = P.R)
    end
    gc = gcd(f, g)
    f = divexact(f, gc)
    g = divexact(g, gc)
    cf = content(f)*sign(leading_coefficient(f))
    cg = content(g)*sign(leading_coefficient(g))
    @assert (c*cf) % cg == 0
    r = new(P, divexact(c*cf, cg), divexact(f, cf), divexact(g, cg))
    @assert parent(r.f) == P.R
    @assert parent(r.g) == P.R
    return r
  end
  function HessQRElem(P::HessQR, q::Generic.RationalFunctionFieldElem{QQFieldElem})
    f = numerator(q)
    g = denominator(q)
    return HessQRElem(P, f, g)
  end
  function HessQRElem(P::HessQR, f::QQPolyRingElem)
    return HessQRElem(P, f, one(parent(f)))
  end
  function HessQRElem(P::HessQR, f::QQPolyRingElem, g::QQPolyRingElem)
    df = reduce(lcm, map(denominator, coefficients(f)), init = ZZRingElem(1))
    dg = reduce(lcm, map(denominator, coefficients(g)), init = ZZRingElem(1))
    ff = map_coefficients(FlintZZ, df*f, parent = P.R)
    gg = map_coefficients(FlintZZ, dg*g, parent = P.R)
    #ff/df//gg/dg = dg/df * ff/gg
    return HessQRElem(P, divexact(dg, df), ff, gg)
  end
  function HessQRElem(P::HessQR, c::ZZRingElem)
    r = new(P, c, one(P.R), one(P.R))
    @assert parent(r.f) == P.R
    @assert parent(r.g) == P.R
    return r
  end
  function HessQRElem(P::HessQR, c::ZZPolyRingElem)
    d = content(c)*sign(leading_coefficient(c))
    r = new(P, d, divexact(c, d), one(P.R))
    @assert parent(r.f) == P.R
    @assert parent(r.g) == P.R
    return r
  end
end

function Base.show(io::IO, a::HessQRElem)
  print(io, AbstractAlgebra.obj_to_string(a, context = io))
end

function expressify(a::HessQRElem; context = nothing)
  return  Expr(:call, :*, expressify(a.c, context = context),
             Expr(:call, ://, expressify(a.f, context = context),
                              expressify(a.g, context = context)))
end

check_parent(a::HessQRElem, b::HessQRElem) = parent(a) == parent(b) || error("Incompatible rings")

function Hecke.integral_split(a::Generic.RationalFunctionFieldElem{QQFieldElem}, S::HessQR)
  if iszero(a)
    return zero(S), one(S)
  end
  n = numerator(a)
  d = denominator(a)
  dn = reduce(lcm, map(denominator, coefficients(n)), init = ZZRingElem(1))
  dd = reduce(lcm, map(denominator, coefficients(d)), init = ZZRingElem(1))
  zn = S.R(n*dn)
  zd = S.R(d*dd)
  cn = content(zn)
  cd = content(zd)
  zn = divexact(zn, cn)
  zd = divexact(zd, cd)
  cn *= dd
  cd *= dn
  g = gcd(cn, cd)
  cn = divexact(cn, g)
  cd = divexact(cd, g)
  return HessQRElem(S, cn, zn, zd), S(cd)
end

function Hecke.numerator(a::Generic.RationalFunctionFieldElem, S::HessQR)
  return integral_split(a, S)[1]
end

function Hecke.denominator(a::Generic.RationalFunctionFieldElem, S::HessQR)
  return integral_split(a, S)[2]
end

Nemo.elem_type(::Type{HessQR}) = HessQRElem
Nemo.parent_type(::Type{HessQRElem}) = HessQR
Nemo.is_domain_type(::Type{HessQRElem}) = true

Base.parent(a::HessQRElem) = a.parent

(R::HessQR)(a::Generic.RationalFunctionFieldElem{QQFieldElem}) = HessQRElem(R, a)
(R::HessQR)(a::ZZRingElem) = HessQRElem(R, a)
(R::HessQR)(a::Integer) = HessQRElem(R, ZZRingElem(a))
(R::HessQR)(a::ZZPolyRingElem) = HessQRElem(R, a)
(R::HessQR)(a::QQPolyRingElem) = HessQRElem(R, a)
(R::HessQR)(a::HessQRElem) = a
(R::HessQR)() = R(0)

(F::Generic.RationalFunctionField)(a::HessQRElem) = a.c*F(a.f)//F(a.g)


Nemo.iszero(a::HessQRElem) = iszero(a.c)
Nemo.isone(a::HessQRElem) = isone(a.c) && isone(a.f) && isone(a.g)

Nemo.zero(R::HessQR) = R(0)
Nemo.one(R::HessQR) = R(1)
Nemo.canonical_unit(a::HessQRElem) = HessQRElem(parent(a), ZZRingElem(sign(a.c)), a.f, a.g)

Base.deepcopy_internal(a::HessQRElem, dict::IdDict) = HessQRElem(parent(a), Base.deepcopy_internal(a.c, dict), Base.deepcopy_internal(a.f, dict), Base.deepcopy_internal(a.g, dict))

Base.hash(a::HessQRElem, u::UInt=UInt(12376599)) = hash(a.g, hash(a.f, hash(a.c, u)))

+(a::HessQRElem, b::HessQRElem) = check_parent(a, b) && HessQRElem(parent(a), ZZRingElem(1), a.c*a.f*b.g+b.c*b.f*a.g, a.g*b.g)
-(a::HessQRElem, b::HessQRElem) = check_parent(a, b) && HessQRElem(parent(a), ZZRingElem(1), a.c*a.f*b.g-b.c*b.f*a.g, a.g*b.g)
-(a::HessQRElem) = HessQRElem(parent(a), -a.c, a.f, a.g)
*(a::HessQRElem, b::HessQRElem) = check_parent(a, b) && HessQRElem(parent(a), a.c*b.c, a.f*b.f, a.g*b.g)

==(a::HessQRElem, b::HessQRElem) = check_parent(a, b) && a.c*a.f == b.c *b.f && a.g == b.g

Base.:^(a::HessQRElem, n::Int) = HessQRElem(parent(a), a.c^n, a.f^n, a.g^n)

function Hecke.mul!(a::HessQRElem, b::HessQRElem, c::HessQRElem)
  d = b*c
  @assert parent(a.f) == parent(d.f)
  @assert parent(a.g) == parent(d.g)
  a.c = d.c
  a.f = d.f
  a.g = d.g
  return a
end

function Hecke.add!(a::HessQRElem, b::HessQRElem, c::HessQRElem)
  d = b+c
  @assert parent(a.f) == parent(d.f)
  @assert parent(a.g) == parent(d.g)
  a.c = d.c
  a.f = d.f
  a.g = d.g
  return a
end

function Hecke.addeq!(a::HessQRElem, b::HessQRElem)
  d = a+b
  @assert parent(a.f) == parent(d.f)
  @assert parent(a.g) == parent(d.g)
  a.c = d.c
  a.f = d.f
  a.g = d.g
  return a
end

function divrem(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)
  if iszero(b)
    error("div by 0")
  end
  if iszero(a)
    return a, a
  end
  #= af/g mod b:
    it is enough to figure this out for b in Z>0, the rest is units
    that will disappaear into the quotient q

    - c = cont(g mod d), then since cont(g) is 1, c is a unit mod d
    - cd = 1 mod d, then
    - cont(g(cx^?+1) mod d) = 1 if ? = deg(g)+1 (or larger):
      g(cx?+1) = cg x^? + g and cont(cg mod d = 1)...
    - af/g -d/(cx^?+1) now has a denominator with cont( mod d) = 1
    - af/g - (af - du)/(g - dv) =
      (af(g-dv) -g(af-du))/(g(g-dv)) = d*..., so once cont(g %d) =1,
      we can replace f and g mod d (and figure out the quotient afterwards)

    - for d = p a prime, the rep is unique, thus F_p(t)

    - other approach:
      af/g = (af mod b)/(g mod b) mod b:

      (af + bA)  af    (af + bA)g - af       bAg
      -------- - -- =  --------------- =  ---------- = b * ....
        g + bB    g     (g + bB) g        (g + bB) g

      the tricky thing is that reducing af and g mod b they may no longer be
      coprime... and gcd mod b is non-trivial to compute. gcd_sircana might work
  =#
  r = rem(a,b)
  return divexact(a-r, b), r

  return HessQRElem(parent(a), q, a.f*b.g, a.g*b.f), HessQRElem(parent(a), r, a.f, a.g)
end

function div(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)
  if iszero(a)
    return a
  end
  return divexact(a-rem(a, b), b)
  q = div(a.c, b.c)
  return HessQRElem(parent(a), q, a.f*b.g, a.g*b.f)
end

function rem(a::HessQRElem, b::HessQRElem)
#  @show :rem, a, b
  #NOT unique...., e.g. gcd(f,g mod b) might be <> 1....
  check_parent(a, b)
  if iszero(a)
    return a
  end
  #see above for reasoning
  d = abs(b.c)
  if isone(d)
    return zero(parent(a))
  end
  R = parent(a).R
  F, mF = quo(ZZ, d)
  aa = map_coefficients(mF, a.c*a.f, cached = false)
  if iszero(aa)
    z = mF(one(domain(mF)))
  else
    z, aa = Hecke.primsplit!(aa)
  end
  bb = map_coefficients(mF, a.g, parent = parent(aa))
  _, f, g = Hecke.gcd_sircana(aa, bb)
  f *= z
  gg = lift(R, g)
  cg = content(gg)
  if !isone(cg)
    c = inv(canonical_unit(mF(cg)))
    gg = lift(R, c*g)
    @assert isone(content(gg))
    f *= c
  end
  ff = lift(R, f)
  cf = content(ff)
  if !iszero(cf)
    ff = divexact(ff, cf)
  end
  r = HessQRElem(parent(a), cf, ff, gg)
  @assert r.c < b.c
#  divexact(a-r, b)
  return r
end

function Nemo.divexact(a::HessQRElem, b::HessQRElem; check::Bool = false)
  check_parent(a, b)
#  @show :divexact, a, b
  q = HessQRElem(parent(a), divexact(a.c, b.c; check = true), a.f*b.g, a.g*b.f)
  @assert q*b == a
  return q
end

function gcd(a::HessQRElem, b::HessQRElem)
  return HessQRElem(parent(a), gcd(a.c, b.c))
end

function Nemo.gcdx(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)
  R = parent(a)
  g, u, v = Nemo.gcdx(a.c, b.c)
  q,w, e =  R(g), HessQRElem(R, u, a.g, a.f), HessQRElem(R, v, b.g, b.f)
  @assert q == w*a+e*b
  return q, w, e
end

function lcm(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)
  return HessQRElem(parent(a), lcm(a.c, b.c))
end

Hecke.is_unit(a::HessQRElem) = is_unit(a.c)

function Nemo.residue_field(a::HessQR, b::HessQRElem)
  @assert parent(b) == a
  @assert is_prime(b.c)
  F = GF(b.c)
  Ft, t = rational_function_field(F, String(var(a.R)), cached = false)
  R = parent(numerator(t))
  S = a.R
  return Ft, MapFromFunc(a, Ft,
                         x->F(x.c)*Ft(map_coefficients(F, x.f, parent = R))//Ft(map_coefficients(F, x.g, parent = R)),
                         y->HessQRElem(a, ZZRingElem(1), map_coefficients(z -> lift(ZZ, z), numerator(y), parent = S), map_coefficients(z -> lift(ZZ, z), denominator(y), parent = S)))
end

function Nemo.residue_ring(a::HessQR, b::HessQRElem)
  F = residue_ring(FlintZZ, b.c)[1]
  Fx, x = polynomial_ring(F, cached = false)
  Q = fraction_field(Fx, cached = false)
  return Q, MapFromFunc(
     a, Q,
     x->map_coefficients(F, x.c*x.f, parent = Fx)//map_coefficients(F, x.g, parent = Fx),
     y->HessQRElem(a, ZZRingElem(1), lift(parent(b.f), numerator(y, false)), lift(parent(b.f), denominator(y, false))))
end

function +(a::FracElem{T}, b::FracElem{T}) where T <: PolyRingElem{<:ResElem{S}} where S <: Hecke.IntegerUnion
  na = numerator(a, false)
  da = denominator(a, false)

  nb = numerator(b, false)
  db = denominator(b, false)

  nc = na*db + da*nb
  dc = da*db
  _, da, db = Hecke.gcd_sircana(nc, dc)
  return parent(a)(da, db)
end

function -(a::FracElem{T}, b::FracElem{T}) where T <: PolyRingElem{<:ResElem{S}} where S <: Hecke.IntegerUnion
  na = numerator(a, false)
  da = denominator(a, false)

  nb = numerator(b, false)
  db = denominator(b, false)

  nc = na*db - da*nb
  dc = da*db
  _, da, db = Hecke.gcd_sircana(nc, dc)
  return parent(a)(da, db)
end

function *(a::FracElem{T}, b::FracElem{T}) where T <: PolyRingElem{<:ResElem{S}} where S <: Hecke.IntegerUnion
  na = numerator(a, false)
  da = denominator(a, false)

  nb = numerator(b, false)
  db = denominator(b, false)

  nc = na*nb
  dc = da*db
  _, da, db = Hecke.gcd_sircana(nc, dc)
  return parent(a)(da, db)
end



function Hecke.factor(a::HessQRElem)
  f = factor(a.c)
  R = parent(a)
  return Fac(R(a.f), Dict((R(p),k) for (p,k) = f.fac))
end

function Hecke.factor(R::HessQR, a::Generic.RationalFunctionFieldElem)
  d1 = reduce(lcm, map(denominator, coefficients(numerator(a))), init = ZZRingElem(1))
  f1 = factor(R(d1*numerator(a)))
  d2 = reduce(lcm, map(denominator, coefficients(denominator(a))), init = ZZRingElem(1))
  f2 = factor(R(d1*denominator(a)))

  for (p,k) = f2.fac
    if haskey(f1.fac, p)
      f1.fac[p] -= k
    else
      f1.fac[p] = k
    end
  end
  f1.unit = divexact(f1.unit, f2.unit)
  return f1
end

function Hecke.is_constant(a::HessQRElem)
  return iszero(a) || (is_constant(a.f) && is_constant(a.g))
end

end

using .HessQRModule

