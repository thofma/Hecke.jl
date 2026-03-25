module HessQRModule
using Hecke
import Hecke.AbstractAlgebra, Hecke.Nemo
import Base: +, -, *, gcd, lcm, divrem, div, rem, mod, ^, ==
export HessQR
import AbstractAlgebra: expressify

# ZZ<x> := {c * f/g | c in ZZ, f, g in ZZ[x] primitive and with positive leading coefficient}
#
# Motivation:
# Every rational function in QQ(x) can be uniquely written as c' * f/g
#   where f,g are primitive with positive leading coefficient and c' is rational
# ZZ<x> consists of those with c' in ZZ
# In Hess' PhD Thesis "Zur Divisorenklassengruppenberechnung in globalen Funktionenkoerpern", chapter 2.10
#   IntCls(Z[x], F) = IntCls(Z<x>, F) intersect IntCls(Q[x], F)
# ZZ[x] by itself is not a PID, so Round-2 does not work,
#   but QQ[x] and Z<x> are PID (and even Euclidean),
#   so we can compute their integral closures easily using Round-2
#
# NB: All non-constant irreducible polynomials in Z[x] are primitive,
#     hence they are units in Z<x>; so the only primes in Z<x> are prime integers.
#     The factorization of c * f/g is, up to units, the factorization of c
#
# NB: the name is bad, but it is taken from the notation of Hess' thesis

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

  # this is the main constructor (all others just transform data and call this one)
  # it ensures that f//g is reduced, and both numerator and denominator are
  #   primitive with positive leading coefficient
  function HessQRElem(P::HessQR, c::ZZRingElem, f::ZZPolyRingElem, g::ZZPolyRingElem)
    # canonical zero representation
    if iszero(c) || iszero(f)
      return new(P, ZZRingElem(0), one(P.R), one(P.R))
    end

    # coerce to the polynomial ring of P
    if parent(f) != P.R
      f = map_coefficients(ZZ, f; parent = P.R)
    end
    if parent(g) != P.R
      g = map_coefficients(ZZ, g; parent = P.R)
    end

    # simplify fraction
    d = gcd(f, g)
    f = divexact(f, d; check = false)
    g = divexact(g, d; check = false)

    # extract constant
    cf = content(f)*sign(leading_coefficient(f))
    cg = content(g)*sign(leading_coefficient(g))
    (c*cf) % cg == 0 || error("not an element of Z<x>")

    c = divexact(c*cf, cg; check = false)
    f = divexact(f, cf; check = false)
    g = divexact(g, cg; check = false)

    return new(P, c, f, g)
  end

  function HessQRElem(P::HessQR, q::Generic.RationalFunctionFieldElem{QQFieldElem})
    return HessQRElem(P, numerator(q), denominator(q))
  end
  function HessQRElem(P::HessQR, f::QQPolyRingElem)
    return HessQRElem(P, f, one(parent(f)))
  end
  function HessQRElem(P::HessQR, f::ZZPolyRingElem)
    d = content(f)*sign(leading_coefficient(f))
    return HessQRElem(P, d, divexact(f, d; check = false), one(P.R))
  end
  function HessQRElem(P::HessQR, c::ZZRingElem)
    return new(P, c, one(P.R), one(P.R))
  end

  function HessQRElem(P::HessQR, f::QQPolyRingElem, g::QQPolyRingElem)
    # bring both to common denominator (and cancel it)
    d = reduce(lcm, map(denominator, coefficients(f)); init = ZZRingElem(1))
    d = reduce(lcm, map(denominator, coefficients(g)); init = d)

    f, g = map_coefficients(ZZ, d*f; parent = P.R), map_coefficients(ZZ, d*g; parent = P.R)

    return HessQRElem(P, ZZRingElem(1), f, g)
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

Hecke.characteristic(::HessQR) = 0

function Hecke.integral_split(a::Generic.RationalFunctionFieldElem{QQFieldElem}, S::HessQR)
  if iszero(a)
    return zero(S), one(S)
  end
  n = numerator(a)
  d = denominator(a)
  dn = reduce(lcm, map(denominator, coefficients(n)), init = ZZRingElem(1))
  dd = reduce(lcm, map(denominator, coefficients(d)), init = ZZRingElem(1))
  zn = change_base_ring(base_ring(S.R), n*dn; parent = S.R)
  zd = change_base_ring(base_ring(S.R), d*dd; parent = S.R)
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

function (F::Generic.RationalFunctionField)(a::HessQRElem)
  K = AbstractAlgebra.Generic.underlying_fraction_field(F)
  R = base_ring(K)
  a.c*F(change_base_ring(base_ring(R), a.f; parent = R))//F(change_base_ring(base_ring(R), a.g; parent = R))
end


Base.deepcopy_internal(a::HessQRElem, dict::IdDict) = HessQRElem(parent(a), Base.deepcopy_internal(a.c, dict), Base.deepcopy_internal(a.f, dict), Base.deepcopy_internal(a.g, dict))

Base.hash(a::HessQRElem, h::UInt) = hash(a.g, hash(a.f, hash(a.c, h)))

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
  F = residue_ring(ZZ, b.c)[1]
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
  return Fac(R(a.f), Dict((R(p),k) for (p,k) in f))
end

function Hecke.factor(R::HessQR, a::Generic.RationalFunctionFieldElem)
  d1 = reduce(lcm, map(denominator, coefficients(numerator(a))), init = ZZRingElem(1))
  f1 = factor(R(d1*numerator(a)))
  d2 = reduce(lcm, map(denominator, coefficients(denominator(a))), init = ZZRingElem(1))
  f2 = factor(R(d1*denominator(a)))

  dic = Dict(p => k for (p, k) in f1)
  for (p, k) in f2
    if haskey(dic, p)
      dic[p] -= k
    else
      dic[p] = k
    end
  end
  return Fac(divexact(unit(f1), unit(f2)), dic)
end

function Hecke.is_constant(a::HessQRElem)
  return iszero(a) || (is_constant(a.f) && is_constant(a.g))
end

###############################################################################
#
#  Arithmetic
#
###############################################################################

function +(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)
  return HessQRElem(parent(a), ZZRingElem(1),
    a.c * a.f * b.g + b.c * b.f * a.g, a.g * b.g)
end
function -(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)
  return HessQRElem(parent(a), ZZRingElem(1),
    a.c * a.f * b.g - b.c * b.f * a.g, a.g * b.g)
end
function *(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)
  return HessQRElem(parent(a), a.c*b.c, a.f*b.f, a.g*b.g)
end
function ==(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)
  return a.c * a.f == b.c * b.f && a.g == b.g
end

function -(a::HessQRElem)
  return HessQRElem(parent(a), -a.c, a.f, a.g)
end

function ^(a::HessQRElem, n::Int)
  return HessQRElem(parent(a), a.c^n, a.f^n, a.g^n)
end

# note that HessQRElem constructor does the heavy lifting of ensuring the canonical representation
# thus we implement mutating add!/mul! via the non-mutating versions

function Hecke.add!(a::HessQRElem, b::HessQRElem, c::HessQRElem)
  d = b + c

  a.c, a.f, a.g = d.c, d.f, d.g
  return a
end

function Hecke.mul!(a::HessQRElem, b::HessQRElem, c::HessQRElem)
  d = b * c

  a.c, a.f, a.g = d.c, d.f, d.g
  return a
end

Nemo.zero(R::HessQR) = R(0)
Nemo.one(R::HessQR) = R(1)

Nemo.iszero(a::HessQRElem) = iszero(a.c)
Nemo.isone(a::HessQRElem) = isone(a.c) && isone(a.f) && isone(a.g)

Nemo.canonical_unit(a::HessQRElem) = HessQRElem(parent(a), sign(a.c), a.f, a.g)
Hecke.is_unit(a::HessQRElem) = is_unit(a.c)

###############################################################################
#
#  Euclidean division
#
###############################################################################

# As noted at the beginning, since primitive polynomials are units in Z<x>,
#   the only primes are prime integers, thus `mod b` is essentially `mod |b.c|`
# The main task is to obtain the *canonical* form of the remainder
# Let d = |b.c|. For starter we might reduce everything modulo d
# (cf + dA)     cf      d·(Ag - afB)
# --------- -  ---- = --------------- = d · (...)
#  g + dB        g       (g + dB)·g
# That is: reducing numerator/denominator modulo d independently changes the
#   value of a by a multiple of d, which is perfectly fine for `mod d` computation
# The caveat: after reducing f, g modulo d (mapping into (Z/dZ)[x])
#   they may stop being coprime. And since Z/dZ is not necessarily a domain (for composite d)
#   we cannot use normal GCD, so we use gcd_sircana

function rem(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)

  iszero(a) && return a
  iszero(b) && throw(DivideError())

  d = abs(b.c)
  isone(d) && return zero(parent(a))

  # map to (Z/dZ)[x]
  R = parent(a).R
  F, mapF = residue_ring(ZZ, d; cached = false)

  aa = map_coefficients(mapF, a.c*a.f; cached = false)
  bb = map_coefficients(mapF, a.g; parent = parent(aa))

  cont_aa = one(F)
  if !iszero(aa)
    cont_aa, aa = Hecke.primsplit!(aa)
  end

  # reduce fraction in (Z/dZ)[x]
  _, f, g = Hecke.gcd_sircana(aa, bb)
  f *= cont_aa

  # lift to Z<x>

  # ensure that lift of g is primitive
  gg = lift(R, g)
  cont_gg = content(gg)
  if !isone(cont_gg)
    # Sircana gcd algorithm guarantees cofactors with unit content
    cont_g = mapF(cont_gg)
    @assert is_unit(cont_g)

    # multiply both numerator and denominator by inverse of content of g
    cf = inv(cont_g)
    f *= cf
    gg = lift(R, cf*g)
    @assert isone(content(gg))
  end

  # f might be not primitive, but its content will be pushed into c
  r = HessQRElem(parent(a), ZZ(1), lift(R, f), gg)
  @assert abs(r.c) < d

  return r
end

function divrem(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)
  iszero(b) && throw(DivideError())
  iszero(a) && return a, a

  r = rem(a, b)
  return divexact(a - r, b; check = false), r
end

function div(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)
  return divrem(a, b)[1]
end

function Nemo.divexact(a::HessQRElem, b::HessQRElem; check::Bool = false)
  check_parent(a, b)
  iszero(b) && throw(DivideError())
  iszero(a) && return a

  check && a.c % b.c != 0 && error("$a not divisible by $b in Z<x>")
  q = HessQRElem(parent(a), divexact(a.c, b.c; check = false), a.f*b.g, a.g*b.f)

  @assert q*b == a
  return q
end

###############################################################################
#
#  GCD
#
###############################################################################

function gcd(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)
  return HessQRElem(parent(a), gcd(a.c, b.c))
end

function Nemo.gcdx(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)

  cd, cu, cv = Nemo.gcdx(a.c, b.c)

  R = parent(a)
  d, u, v = R(cd), HessQRElem(R, cu, a.g, a.f), HessQRElem(R, cv, b.g, b.f)
  @assert d == u * a + v * b
  return d, u, v
end

function lcm(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)
  return HessQRElem(parent(a), lcm(a.c, b.c))
end

end

using .HessQRModule

