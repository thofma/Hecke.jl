################################################################################
#
#          EllCrv/EllCrv.jl : Elliptic curves over general fields
#
# This file is part of Hecke.
#
# Copyright (c) 2015, 2016: Claus Fieker, Tommy Hofmann
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
# * Redistributions of source code must retain the above copyright notice, this
#   list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
# (C) 2016 Tommy Hofmann
# (C) 2016 Robin Ammon
# (C) 2016 Sofia Brenner
#
################################################################################

export EllCrv, EllCrvPt

export base_field, disc, division_polynomialE, EllipticCurve, infinity,
       isinfinite, isshort, ison_curve, j_invariant, Psi_polynomial,
       psi_poly_field, short_weierstrass_model, +, *

################################################################################
#
#  Types
#
################################################################################

mutable struct EllCrv{T}
  base_field::Ring
  short::Bool
  coeff::Array{T, 1}
  a_invars::Tuple{T, T, T, T, T}
  b_invars::Tuple{T, T, T, T}
  long_c::Array{T, 1}
  disc::T
  j::T

  torsion_points#::Array{EllCrvPt, 1}
  torsion_structure#Tuple{Array{Int, 1}, Array{EllCrvPt, 1}}

  function EllCrv{T}(coeffs::Array{T, 1}, check::Bool = true) where {T}
    if length(coeffs) == 2
      if check
        d = 4*coeffs[1]^3 + 27*coeffs[2]^2
        if d != 0
          E = new{T}()
          E.short = true
          # fixed on Nemo master
          E.coeff = [ deepcopy(z) for z in coeffs]
          E.base_field = parent(coeffs[1])
          #E.disc = d
        else
          error("discriminant is zero")
        end
      else
        E = new{T}()
        E.short = true
        E.coeff = [ deepcopy(z) for z in coeffs]
        E.base_field = parent(coeffs[1])
      end
    elseif length(coeffs) == 5 # coeffs = [a1, a2, a3, a4, a6]
      if check
        a1 = coeffs[1]
        a2 = coeffs[2]
        a3 = coeffs[3]
        a4 = coeffs[4]
        a6 = coeffs[5]

        b2 = a1^2 + 4*a2
        b4 = a1*a3 + 2*a4
        b6 = a3^2 + 4*a6
        b8 = a1^2*a6 - a1*a3*a4 + 4*a2*a6 + a2*a3^2 - a4^2

        d = (-b2^2*b8 - 8*b4^3 - 27*b6^2 + 9*b2*b4*b6)

        if d != 0
          E = new{T}()
          E.coeff = [ deepcopy(z) for z in coeffs]
          E.short = false
          E.b_invars = (b2, b4, b6, b8)
          E.a_invars = (a1, a2, a3, a4, a6)
          E.disc = d
          E.base_field = parent(coeffs[1])
        else
          error("Discriminant is zero")
        end
      else
        E = new{T}()
        E.short = false
        E.coeff = [ deepcopy(z) for z in coeffs]
        E.base_field = parent(coeffs[1])
      end
    else
      error("Length of coefficient array must be 2 or 5")
    end
    return E
  end
end

mutable struct EllCrvPt{T}
  coordx::T
  coordy::T
  isinfinite::Bool
  parent::EllCrv{T}

  function EllCrvPt{T}(E::EllCrv{T}, coords::Array{T, 1}, check::Bool = true) where {T}
    if check
      if ison_curve(E, coords)
        P = new{T}(coords[1], coords[2], false, E)
        return P
      else
        error("Point is not on the curve")
      end
    else
      P = new{T}(coords[1], coords[2], false, E)
      return P
    end
  end

  function EllCrvPt{T}(E::EllCrv{T}) where {T}
    z = new{T}()
    z.parent = E
    z.isinfinite = true
    return z
  end
end

################################################################################
#
#  Constructors for users
#
################################################################################

function EllipticCurve(x::Array{T, 1}, check::Bool = true) where T
  E = EllCrv{T}(x, check)
  return E
end

#  Implicit promotion in characterstic 0
function EllipticCurve(x::Array{Int, 1}, check::Bool = true)
  return EllipticCurve(fmpq[ FlintQQ(z) for z in x], check)
end

function EllipticCurve(x::Array{fmpz, 1}, check::Bool = true)
  return EllipticCurve(fmpq[ FlintQQ(z) for z in x], check)
end

function (E::EllCrv{T})(coords::Array{S, 1}, check::Bool = true) where {S, T}
  if length(coords) != 2
    error("Need two coordinates")
  end

  if S == T
    parent(coords[1]) != base_field(E) &&
        error("Objects must be defined over same field")
    return EllCrvPt{T}(E, coords, check)
  else
    return EllCrvPt{T}(E, map(base_field(E), coords), check)
  end
end

################################################################################
#
#  Field access
#
################################################################################

function base_field(E::EllCrv{T}) where T
  return E.base_field::parent_type(T)
end

function Base.deepcopy_internal(E::EllCrv, dict::IdDict)
    return EllipticCurve(E.coeff)
end

function parent(P::EllCrvPt)
  return P.parent
end

function isfinite(P::EllCrvPt)
  return !P.isinfinite
end

function isinfinite(P::EllCrvPt)
  return P.isinfinite
end

function isshort(E::EllCrv)
  return E.short
end

function a_invars(E::EllCrv)
  if isdefined(E, :a_invars)
    return [ deepcopy(z) for z in E.a_invars ]
  else
    t = (E.coeff[1], E.coeff[2], E.coeff[3], E.coeff[4], E.coeff[5])
    E.a_invars = t
    return t
  end
end

function b_invars(E::EllCrv)
  if isdefined(E, :long_b)
    # fixed on Nemo master
    return deepcopy(E.b_invars)
  else
    a1 = E.coeff[1]
    a2 = E.coeff[2]
    a3 = E.coeff[3]
    a4 = E.coeff[4]
    a6 = E.coeff[5]

    b2 = a1^2 + 4*a2
    b4 = a1*a3 + 2*a4
    b6 = a3^2 + 4*a6
    b8 = a1^2*a6 - a1*a3*a4 + 4*a2*a6 + a2*a3^2 - a4^2

    E.b_invars = (b2, b4, b6, b8)
    return (b2, b4, b6, b8)
  end
end

################################################################################
#
# Changing the model
#
################################################################################

@doc Markdown.doc"""
    short_weierstrass_model(E::EllCrv{fmpq}) -> (EE::EllCrv, function(EllCrvPt), function(EllCrvPt))

Transforms a curve given in long Weierstrass form over QQ to short Weierstrass form
returns short form and both transformations for points on the curve; first transformation from E (long form) to EE (short form), second transformation the other way round
"""
function short_weierstrass_model(E::EllCrv)
  return _short_weierstrass_model(E)
end

function _short_weierstrass_model(E::EllCrv{T}) where T
  R = base_field(E)
  p = characteristic(R)

  if (p == 2) || (p == 3)
      error("Converting to short form not possible in characteristic 2 and 3")
  end

  a1 = E.coeff[1]
  a2 = E.coeff[2]
  a3 = E.coeff[3]
  a4 = E.coeff[4]
  a6 = E.coeff[5]

  b2, b4, b6, b8 = b_invars(E)

#  b2 = a1^2 + 4*a2
#  b4 = a1*a3 + 2*a4
#  b6 = a3^2 + 4*a6

  c4 = (b2^2 - 24*b4)
  c6 = (-b2^3 + 36* b2*b4 - 216* b6)

  Anew = -divexact(c4, 48)
  Bnew = -divexact(c6, 864)

  EE = EllipticCurve([Anew, Bnew])::EllCrv{T}

  # we are hitting https://github.com/JuliaLang/julia/issues/15276

  _b2 = deepcopy(b2)
  _a1 = deepcopy(a1)
  _a3 = deepcopy(a3)

  # transformes a point on E (long form) to a point on EE (short form)
  trafo = function(P::EllCrvPt)

    if P.isinfinite
      return infinity(EE)
    end

    xnew = P.coordx + divexact(_b2, 12)
    ynew = P.coordy + divexact(_a1*P.coordx + _a3, 2)
    Q = EE([xnew, ynew])::EllCrvPt{T}
    return Q
  end

  # transformes a point on EE (short form) back to a point on E (long form)
  ruecktrafo = function(R::EllCrvPt)
    if R.isinfinite
        return infinity(E)
    end

    xnew = R.coordx - divexact(_b2, 12)
    ynew = R.coordy - divexact(_a1*xnew + _a3, 2)
    S = E([xnew, ynew])
    return S::EllCrvPt{T}
  end

  # type annotation necessary due to #15276
  return EE::EllCrv{T}, trafo, ruecktrafo
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, E::EllCrv)
  print(io, "Elliptic curve with equation\n")
  if E.short
    print(io, "y^2 = ")
    sum = Expr(:call, :+)
    push!(sum.args, Expr(:call, :^, :x, 3))
    c = E.coeff[1]
    if !iszero(c)
      if isone(c)
        push!(sum.args, Expr(:call, :*, :x))
      else
        push!(sum.args, Expr(:call, :*, AbstractAlgebra.expressify(c, context = io), :x))
      end
    end
    c = E.coeff[2]
    if !iszero(c)
      push!(sum.args, AbstractAlgebra.expressify(c, context = io))
    end
    print(io, AbstractAlgebra.expr_to_string(AbstractAlgebra.canonicalize(sum)))
  else
    sum = Expr(:call, :+)
    push!(sum.args, Expr(:call, :^, :y, 2))
    c = E.coeff[1]
    if !iszero(c)
      if isone(c)
        push!(sum.args, Expr(:call, :*, :x, :y))
      else
        push!(sum.args, Expr(:call, :*, AbstractAlgebra.expressify(c, context = io), :x, :y))
      end
    end
    c = E.coeff[3]
    if !iszero(c)
      if isone(c)
        push!(sum.args, Expr(:call, :*, :y))
      else
        push!(sum.args, Expr(:call, :*, AbstractAlgebra.expressify(c, context = io), :y))
      end
    end
    print(io, AbstractAlgebra.expr_to_string(AbstractAlgebra.canonicalize(sum)))

    print(io, " = ")
    sum = Expr(:call, :+)
    push!(sum.args, Expr(:call, :^, :x, 3))

    c = E.coeff[2]
    if !iszero(c)
      if isone(c)
        push!(sum.args, Expr(:call, :*, Expr(:call, :^, :x, 2)))
      else
        push!(sum.args, Expr(:call, :*, AbstractAlgebra.expressify(c, context = io), Expr(:call, :^, :x, 2)))
      end
    end

    c = E.coeff[4]
    if !iszero(c)
      if isone(c)
        push!(sum.args, Expr(:call, :*, :x))
      else
        push!(sum.args, Expr(:call, :*, AbstractAlgebra.expressify(c, context = io), :x))
      end
    end

    c = E.coeff[5]
    if !iszero(c)
      push!(sum.args, AbstractAlgebra.expressify(c, context = io))
    end

    print(io, AbstractAlgebra.expr_to_string(AbstractAlgebra.canonicalize(sum)))
  end
end

function show(io::IO, P::EllCrvPt)
    if P.isinfinite
        print(io, "Point at infinity of $(P.parent)")
    else
        print(io, "Point $(P.coordx),$(P.coordy) of $(P.parent)")
    end
end

################################################################################
#
#  Point at infinity
#
################################################################################

@doc Markdown.doc"""
    infinity(E::EllCrv) -> EllCrvPt

Creates the point at infinity.
"""
function infinity(E::EllCrv{T}) where T
  infi = EllCrvPt{T}(E)
  return infi
end

################################################################################
#
#  Test for inclusion
#
################################################################################

@doc Markdown.doc"""
    ison_curve(E::EllCrv{T}, coords::Array{T, 1}) -> Bool

Returns true if `coords` defines a point on $E$ and false otherwise. The array
`coords` must have length 2.
"""
function ison_curve(E::EllCrv{T}, coords::Array{T, 1}) where T
  length(coords) != 2 && error("Array must be of length 2")

  x = coords[1]
  y = coords[2]

  if E.short == true
    if y^2 == x^3 + (E.coeff[1])*x + (E.coeff[2])
      return true
    else
      return false
    end
  else
    if (y^2 + (E.coeff[1])*x*y + (E.coeff[3])*y ==
            x^3 + (E.coeff[2])*x^2+(E.coeff[4])*x + (E.coeff[5]))
      return true
    else
      return false
    end
  end
end

################################################################################
#
#  Discriminant
#
################################################################################

@doc Markdown.doc"""
    disc(E::EllCrv{T}) -> T

Computes the discriminant of $E$.
"""
function disc(E::EllCrv{T}) where T
  if isdefined(E, :disc)
    return E.disc
  end

  if E.short == true
    # fall back to the formula for the long form
    # this should be done in a more clever way
    R = base_field(E)
    F = EllipticCurve([R(0), R(0), R(0), E.coeff[1], E.coeff[2]])
    d = disc(F)
    E.disc = d
    return d::T
  else
    a1 = E.coeff[1]
    a2 = E.coeff[2]
    a3 = E.coeff[3]
    a4 = E.coeff[4]
    a6 = E.coeff[5]

    (b2, b4, b6, b8) = b_invars(E)

    d = -b2^2*b8 - 8*b4^3 - 27*b6^2 + 9*b2*b4*b6
    E.disc = d
    return d::T
  end
end

################################################################################
#
#  j-invariant
#
################################################################################

# p. 46 Washington, p. 72 Cohen
@doc Markdown.doc"""
    j(E::EllCrv{T}) -> T
Computes the j-invariant of $E$.
"""
function j_invariant(E::EllCrv{T}) where T
  if isdefined(E, :j)
    return E.j
  end

  if E.short == true

    R = base_field(E)
    F = EllipticCurve([R(0), R(0), R(0), E.coeff[1], E.coeff[2]])
    j = j_invariant(F)
    E.j = j
    return j::T
  else
    a1 = E.coeff[1]
    a2 = E.coeff[2]
    a3 = E.coeff[3]
    a4 = E.coeff[4]
    a6 = E.coeff[5]

    (b2, b4, b6, b8) = b_invars(E)
    #b2 = a1^2 + 4*a2
    #b4 = a1*a3 + 2*a4
    #b6 = a3^2 + 4*a6
    #b8 = a1^2*a6 - a1*a3*a4 + 4*a2*a6 + a2*a3^2 - a4^2

    c4 = b2^2 - 24*b4

    j = divexact(c4^3, disc(E))
    E.j = j
    return j::T
  end
end

################################################################################
#
#  Addition of Points
#
################################################################################

# washington p. 14, cohen p. 270
@doc Markdown.doc"""
    +(P::EllCrvPt, Q::EllCrvPt) -> EllCrvPt
Adds two points on an elliptic curve.
does not work in characteristic 2
"""
function +(P::EllCrvPt{T}, Q::EllCrvPt{T}) where T
  parent(P) != parent(Q) && error("Points must live on the same curve")

  characteristic(base_field(parent(P))) == 2 &&
      error("Not yet implemented in characteristic 2")

  # Is P = infinity or Q = infinity?
  if P.isinfinite
      return Q
  elseif Q.isinfinite
      return P
  end

  E = P.parent

  # Distinguish between long and short form
  if E.short == true
    if P.coordx != Q.coordx
        m = divexact(Q.coordy - P.coordy, Q.coordx - P.coordx)
        x = m^2 - P.coordx - Q.coordx
        y = m * (P.coordx - x) - P.coordy
    elseif P.coordy != Q.coordy
        return infinity(E)
    elseif P.coordy != 0
        m = divexact(3*(P.coordx)^2 + (E.coeff[1]), 2*P.coordy)
        x = m^2 - 2*P.coordx
        y = m* (P.coordx - x) - P.coordy
    else
        return infinity(E)
    end

    Erg = E([x, y], false)

  else
    a1 = E.coeff[1]
    a2 = E.coeff[2]
    a3 = E.coeff[3]
    a4 = E.coeff[4]
    a6 = E.coeff[5]

    # Use [Cohen, p. 270]
    if P.coordx == Q.coordx
      if Q.coordy == -a1*P.coordx - a3 - P.coordy # then P = -Q
        return infinity(E)
      elseif P.coordy == Q.coordy # then P = Q
        m = divexact(3*((P.coordx)^2) + 2*a2*P.coordx + a4 - a1*P.coordy, 2*P.coordy + a1*P.coordx + a3)
        x = -P.coordx - Q.coordx - a2 + a1*m + m^2
        y = -P.coordy - m*(x - P.coordx) - a1*x - a3
      else # then P != +-Q
        m = divexact(Q.coordy - P.coordy, Q.coordx - P.coordx)
        x = -P.coordx - Q.coordx - a2 + a1*m + m^2
        y = -P.coordy - m*(x - P.coordx) - a1*x - a3
      end
    else # now P != +-Q
      m = divexact(Q.coordy - P.coordy, Q.coordx - P.coordx)
      x = -P.coordx - Q.coordx - a2 + a1*m + m^2
      y = -P.coordy - m*(x - P.coordx) - a1*x - a3
    end

    Erg = E([x, y], false)

  end
  return Erg
end

################################################################################
#
#  Inverse
#
################################################################################

@doc Markdown.doc"""
    -(P::EllCrvPt) -> EllCrvPt

Computes the inverse of the point $P$ on an elliptic curve.
"""
function -(P::EllCrvPt)
  E = P.parent

  if !isfinite(P)
    return infinity(E)
  end

  if E.short == true
    Q = E([P.coordx, -P.coordy], false)
  else
    Q = E([P.coordx, -E.coeff[1]*P.coordx - E.coeff[3] - P.coordy], false)
  end

  return Q
end

@doc Markdown.doc"""
    ==(P::EllCrvPt, Q::EllCrvPt) -> Bool

Returns true if $P$ and $Q$ are equal and live over the same elliptic curve
$E$.
"""
function ==(P::EllCrvPt{T}, Q::EllCrvPt{T}) where T
  # both are infinite
  if P.isinfinite && Q.isinfinite
    return true
  end

  # one of them is infinite
  if xor(P.isinfinite, Q.isinfinite)
    return false
  end

  # Otherwise, compare coordinates
  if P.coordx == Q.coordx && P.coordy == Q.coordy
    return true
  else
    return false
  end
end

################################################################################
#
#  Scalar multiplication
#
################################################################################

# algorithm 'integer times a point', [Washington, p. 18]
@doc Markdown.doc"""
    *(n::Int, P::EllCrvPt) -> EllCrvPt

Computes the point $nP$.
"""
function *(n::Int, P::EllCrvPt)
  B = infinity(P.parent)
  C = P

  if n >= 0
      a = n
  else
      a = -n
  end

  while a != 0
    if mod(a,2) == 0
      a = div(a,2)
      C = C + C
    else
      a = a - 1
      B = B + C
    end
  end

  if n < 0
    B = -B
  end

  return B
end

################################################################################
#
#  Division polynomials
#
################################################################################
# TODO:
# - Adjust to Sage/Magma
# - Implement for long form, see Mazur, Tate, "p-adic sigma function"


# computes the n-th division polynomial psi_n in ZZ[x,y] for a given elliptic curve E over ZZ
function division_polynomialE(E::EllCrv, n::Int, x = nothing, y = nothing)

  A = numerator(E.coeff[1])
  B = numerator(E.coeff[2])

  if x === nothing
    Zx, _x = PolynomialRing(FlintZZ, "x")
    Zxy, y = PolynomialRing(Zx, "y")
    x = Zxy(_x)
  else
    Zxy = parent(x)
  end

  if n == 1
    return one(Zxy)
  elseif n == 2
    return 2*y
  elseif n == 3
    return 3*x^4 + 6*(A)*x^2 + 12*(B)*x - (A)^2
  elseif n == 4
    return 4*y*(x^6 + 5*(A)*x^4 + 20*(B)*x^3 - 5*(A)^2*x^2 - 4*(A)*(B)*x - 8*(B)^2 - (A)^3)
  elseif mod(n,2) == 0
    m = div(n,2)
    return divexact( (division_polynomialE(E,m,x,y))*(division_polynomialE(E,m+2, x, y)*division_polynomialE(E,m-1,x, y)^2 - division_polynomialE(E,m-2,x, y)*division_polynomialE(E,m+1,x,y)^2), 2*y)
  else m = div(n-1,2)
    return division_polynomialE(E,m+2,x,y)*division_polynomialE(E,m,x,y)^3 - division_polynomialE(E,m-1,x,y)*division_polynomialE(E,m+1,x,y)^3
  end
end

function replace_all_squares(f, g)
    # assumes that f is in Z[x,y^2] and g in Z[x]. Replaces y^2 with g.
    # the result will be in Z[x]
    z = zero(parent(g)) # this is the zero in Z[x]
    d = div(degree(f), 2) # degree of f in y^2 should be even
    for i in 0:d
        z = z + coeff(f, 2*i)*g^i
    end
    return z
end

function replace_all_squares_modulo(f, g, F)
    # assumes that f is in Z[x,y^2] and g in Z[x]. Replaces y^2 with g.
    # the result will be in Z[x]
    z = zero(parent(g)) # this is the zero in Z[x]
    d = div(degree(f), 2) # degree of f in y^2 should be even
    for i in 0:d
        z = z + coeff(f, 2*i)*powmod(g, i, F)
    end
    return z
end

# here is an example: f = _Zxy(_x)*y^2 + _Zxy(_x + 1)*y^4; EC.replace_all_squares(f, x^3)
# this should give _x^7+_x^6+_x^4

# computes the n-th Psi-polynomial Psi_n in ZZ[_x]
function Psi_polynomial(E::EllCrv, n::Int)

    if n < 2
        error("Psi-polynomial not defined")
    end

    Zx, _x = PolynomialRing(FlintZZ, "x")
    Zxy, y = PolynomialRing(Zx, "y")
    x = Zxy(_x)

    # g = y^2
    g = _x^3 + (numerator(E.coeff[1]))*_x + numerator(E.coeff[2])

    h = division_polynomialE(E, n, x, y)
    # make h into an element of ZZ[x]

    # in the even case, first divide by 2y and then replace y^2
    if mod(n,2) == 0
        f = divexact(h,2*y)
        f = replace_all_squares(f,g)
    else
        f = replace_all_squares(h,g)
    end

    return f
end

# Division polynomials in general for an elliptic curve over an arbitrary field

# standard divison polynomial Psi (as needed in Schoof's algorithm)
function psi_poly_field(E::EllCrv, n::Int, x, y)

    R = base_field(E)
    A = E.coeff[1]
    B = E.coeff[2]

    if n == -1
        return -y^0
    elseif n == 0
        return zero(parent(y))
    elseif n == 1
        return y^0
    elseif n == 2
        return 2*y
    elseif n == 3
        return (3*x^4 + 6*(A)*x^2 + 12*(B)*x - (A)^2)*y^0
    elseif n == 4
        return 4*y*(x^6 + 5*(A)*x^4 + 20*(B)*x^3 - 5*(A)^2*x^2 - 4*(A)*(B)*x - 8*(B)^2 - (A)^3)
    elseif mod(n,2) == 0
        m = div(n,2)
        return divexact( (psi_poly_field(E,m,x,y))*(psi_poly_field(E,m+2,x,y)*psi_poly_field(E,m-1,x,y)^2 - psi_poly_field(E,m-2,x,y)*psi_poly_field(E,m+1,x,y)^2), 2*y)
    else m = div(n-1,2)
        return psi_poly_field(E,m+2,x,y)*psi_poly_field(E,m,x,y)^3 - psi_poly_field(E,m-1,x,y)*psi_poly_field(E,m+1,x,y)^3
    end
end
