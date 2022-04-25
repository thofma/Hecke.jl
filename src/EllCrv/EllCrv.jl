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
# (C) 2022 Jeroen Hanselman
#
################################################################################

export EllCrv, EllCrvPt

export base_field, division_polynomial, division_polynomial_univariate, EllipticCurve, infinity,
       isfinite, isinfinite, isweierstrassmodel, is_on_curve, j_invariant,
       short_weierstrass_model, +, *, a_invars, b_invars, c_invars, equation

################################################################################
#
#  Types
#
################################################################################

mutable struct EllCrv{T}
  base_field::Field
  short::Bool
  a_invars::Tuple{T, T, T, T, T}
  b_invars::Tuple{T, T, T, T}
  c_invars::Tuple{T,T}
  disc::T
  j::T

  torsion_points#::Vector{EllCrvPt}
  torsion_structure#Tuple{Vector{Int}, Vector{EllCrvPt}}

  function EllCrv{T}(coeffs::Vector{T}, check::Bool = true) where {T}
    if length(coeffs) == 2
      if check
        d = -16*(4*coeffs[1]^3 + 27*coeffs[2]^2)
        if d != 0
          E = new{T}()
          E.short = true
          # fixed on Nemo master
          K = parent(coeffs[1])
          E.base_field = K
          E.a_invars = (zero(K),zero(K),zero(K),coeffs[1],coeffs[2])
          
          E.disc = d
        else
          error("discriminant is zero")
        end
      else
        E = new{T}()
        E.short = true
        K = parent(coeffs[1])
        E.base_field = K
        E.a_invars = (zero(K),zero(K),zero(K),coeffs[1],coeffs[2])
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
          if a1==a2==a3==0
            E.short = true
          else
            E.short = false
          end
          E.a_invars = (a1, a2, a3, a4, a6)
          E.b_invars = (b2, b4, b6, b8)
          E.disc = d
          E.base_field = parent(coeffs[1])
        else
          error("Discriminant is zero")
        end
      else
        E = new{T}()
        a1 = coeffs[1]
        a2 = coeffs[2]
        a3 = coeffs[3]
        a4 = coeffs[4]
        a6 = coeffs[5]
        if a1==a2==a3==0
            E.short = true
          else
            E.short = false
          end
        E.a_invars = (a1, a2, a3, a4, a6)
        E.base_field = parent(coeffs[1])
      end
    else
      error("Length of coefficient array must be either 2 or 5")
    end
    return E
  end
end

mutable struct EllCrvPt{T}
  coordx::T
  coordy::T
  isinfinite::Bool
  parent::EllCrv{T}

  function EllCrvPt{T}(E::EllCrv{T}, coords::Vector{T}, check::Bool = true) where {T}
    if check
      if is_on_curve(E, coords)
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
#  Constructors for Elliptic Curve
#
################################################################################

function EllipticCurve(x::Vector{T}, check::Bool = true) where T <: FieldElem
  E = EllCrv{T}(x, check)
  return E
end

function EllipticCurve(K::Field, x::Vector{T}, check::Bool = true) where T 
  EllipticCurve([ K(z) for z in x], check)
end

#  Implicit promotion in characterstic 0
function EllipticCurve(x::Vector{Int}, check::Bool = true)
  return EllipticCurve(fmpq[ FlintQQ(z) for z in x], check)
end

function EllipticCurve(x::Vector{BigInt}, check::Bool = true)
  return EllipticCurve(fmpq[ FlintQQ(z) for z in x], check)
end

function EllipticCurve(x::Vector{fmpz}, check::Bool = true)
  return EllipticCurve(fmpq[ FlintQQ(z) for z in x], check)
end

function EllipticCurve(x::Vector{Rational{Int}}, check::Bool = true)
  return EllipticCurve(fmpq[ FlintQQ(z) for z in x], check)
end

################################################################################
#
#  Constructors for Point on Elliptic Curve
#
################################################################################

function (E::EllCrv{T})(coords::Vector{S}, check::Bool = true) where {S, T}
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
#  Equality of Models
#
################################################################################


@doc Markdown.doc"""
    ==(E::EllCrv, F::EllCrv) -> Bool

Return true if $E$ and $F$ are given by the same model over the same field.
"""
function ==(E::EllCrv, F::EllCrv) where T
  return a_invars(E) == a_invars(F) && base_field(E) == base_field(F)
end

################################################################################
#
#  Field access
#
################################################################################

@doc Markdown.doc"""
    base_field(E::EllCrv) -> Field

Return the base field over which E is defined. 
"""
function base_field(E::EllCrv{T}) where T
  return E.base_field::parent_type(T)
end

function Base.deepcopy_internal(E::EllCrv, dict::IdDict)
    return EllipticCurve(E.a_invars)
end

function parent(P::EllCrvPt)
  return P.parent
end

@doc Markdown.doc"""
    isfinite(E::EllCrvPt) -> Bool

Return true if P is not the point at infinity. 
"""
function isfinite(P::EllCrvPt)
  return !P.isinfinite
end

@doc Markdown.doc"""
    isinfinite(E::EllCrvPt) -> Bool

Return true if P is the point at infinity. 
"""
function isinfinite(P::EllCrvPt)
  return P.isinfinite
end

@doc Markdown.doc"""
    isweierstrassmodel(E::EllCrv) -> Bool

Return true if E is in short Weierstrass form. 
"""
function isweierstrassmodel(E::EllCrv)
  return E.short
end

@doc Markdown.doc"""
    a_invars(E::EllCrv{T}) -> Tuple{T, T, T, T, T}

Return the Weierstrass coefficients of E as a tuple (a1, a2, a3, a4, a6)
such that E is given by y^2 + a1xy + a3y = x^3 + a2x^2 + a4x + a6. 
"""
function a_invars(E::EllCrv)
  return E.a_invars
end

@doc Markdown.doc"""
    coefficients(E::EllCrv{T}) -> Tuple{T, T, T, T, T}

Return the Weierstrass coefficients of E as a tuple (a1, a2, a3, a4, a6)
such that E is given by y^2 + a1xy + a3y = x^3 + a2x^2 + a4x + a6. 
"""
coefficients(E::EllCrv) = a_invars(E)

@doc Markdown.doc"""
    b_invars(E::EllCrv{T}) -> Tuple{T, T, T, T}

Return the b-invariants of E as a tuple (b2, b4, b6, b8).
"""
function b_invars(E::EllCrv)
  if isdefined(E, :b_invars)
    # fixed on Nemo master
    return deepcopy(E.b_invars)
  else
    a1, a2, a3, a4, a6 = a_invars(E)

    b2 = a1^2 + 4*a2
    b4 = a1*a3 + 2*a4
    b6 = a3^2 + 4*a6
    b8 = a1^2*a6 - a1*a3*a4 + 4*a2*a6 + a2*a3^2 - a4^2

    E.b_invars = (b2, b4, b6, b8)
    return (b2, b4, b6, b8)
  end
end

@doc Markdown.doc"""
    c_invars(E::EllCrv{T}) -> Tuple{T, T, T, T}

Return the c-invariants of E as a tuple (c4, c6).
"""
function c_invars(E::EllCrv)
  if isdefined(E, :c_invars)
    # fixed on Nemo master
    return deepcopy(E.c_invars)
  else
    b2,b4,b6,b8 = b_invars(E)
    c4 = b2^2 - 24*b4
    c6 = -b2^3 + 36*b2*b4 - 216*b6
    return (c4,c6)
  end
end

################################################################################
#
# Changing the model
#
################################################################################

@doc Markdown.doc"""
    short_weierstrass_model(E::EllCrv{fmpq}) -> 
      (EE::EllCrv, function(EllCrvPt), function(EllCrvPt))

Transform a curve given in long Weierstrass form over QQ to short Weierstrass
form. Return short form and both transformations for points on the curve;
first transformation from E (long form) to EE (short form), 
second transformation the other way round
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

  a1, _, a3= a_invars(E)

  b2, b4, b6, b8 = b_invars(E)

  c4, c6 = c_invars(E)

  Anew = -divexact(c4, 48)
  Bnew = -divexact(c6, 864)

  EE = EllipticCurve([Anew, Bnew])::EllCrv{T}

  # we are hitting https://github.com/JuliaLang/julia/issues/15276

  _b2 = deepcopy(b2)
  _a1 = deepcopy(a1)
  _a3 = deepcopy(a3)

  # transforms a point on E (long form) to a point on EE (short form)
  trafo = function(P::EllCrvPt)

    if P.isinfinite
      return infinity(EE)
    end

    xnew = P.coordx + divexact(_b2, 12)
    ynew = P.coordy + divexact(_a1*P.coordx + _a3, 2)
    Q = EE([xnew, ynew])::EllCrvPt{T}
    return Q
  end

  # transforms a point on EE (short form) back to a point on E (long form)
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
#  Equation
#
################################################################################

@doc Markdown.doc"""
    equation(E::EllCrv) -> Poly

Return the equation defining the elliptic curve E. 
"""
function equation(E::EllCrv)
  K = base_field(E)
  Kx, x = PolynomialRing(K,"x")
  Kxy, y = PolynomialRing(Kx,"y")
  
  a1, a2, a3, a4, a6 = a_invars(E)
  
  return y^2 + a1*x*y + a3*y - (x^3 + a2*x^2 + a4*x + a6)
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, E::EllCrv)
  print(io, "Elliptic curve with equation\n")
  a1, a2, a3, a4, a6 = a_invars(E)
  sum = Expr(:call, :+)
  push!(sum.args, Expr(:call, :^, :y, 2))
  c = a1
  if !iszero(c)
    if isone(c)
      push!(sum.args, Expr(:call, :*, :x, :y))
    else
      push!(sum.args, Expr(:call, :*, AbstractAlgebra.expressify(c, context = io), :x, :y))
    end
  end
  c = a3
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

  c = a2
  if !iszero(c)
    if isone(c)
      push!(sum.args, Expr(:call, :*, Expr(:call, :^, :x, 2)))
    else
      push!(sum.args, Expr(:call, :*, AbstractAlgebra.expressify(c, context = io), Expr(:call, :^, :x, 2)))
    end
  end

  c = a4
  if !iszero(c)
    if isone(c)
      push!(sum.args, Expr(:call, :*, :x))
    else
      push!(sum.args, Expr(:call, :*, AbstractAlgebra.expressify(c, context = io), :x))
    end
  end

  c = a6
  if !iszero(c)
    push!(sum.args, AbstractAlgebra.expressify(c, context = io))
  end

  print(io, AbstractAlgebra.expr_to_string(AbstractAlgebra.canonicalize(sum)))
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

Return the point at infinity.
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
    is_on_curve(E::EllCrv{T}, coords::Vector{T}) -> Bool

Return true if `coords` defines a point on $E$ and false otherwise. The array
`coords` must have length 2.
"""
function is_on_curve(E::EllCrv{T}, coords::Vector{T}) where T
  length(coords) != 2 && error("Array must be of length 2")
  a1, a2, a3, a4, a6 = a_invars(E)
  x = coords[1]
  y = coords[2]

  if E.short == true
    if y^2 == x^3 + a4*x + a6
      return true
    else
      return false
    end
  else
    if (y^2 + a1*x*y + a3*y ==
            x^3 + a2*x^2+a4*x + a6)
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
    discriminant(E::EllCrv{T}) -> T

Compute the discriminant of $E$.
"""
function discriminant(E::EllCrv{T}) where T
  if isdefined(E, :disc)
    return E.disc
  end
  if E.short == true
    _, _, _, a4, a6 = a_invars(E)
    d = -16*(4*a4^3 + 27*a6^2)
    E.disc = d
    return d::T
  else
    b2, b4, b6, b8 = b_invars(E)
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

Compute the j-invariant of $E$.
"""
function j_invariant(E::EllCrv{T}) where T
  if isdefined(E, :j)
    return E.j
  end

  if E.short == true

    R = base_field(E)
    a1, a2, a3, a4, a6 = a_invars(E)
    j = divexact(-1728*(4*a4)^3,discriminant(E))
    E.j = j
    return j::T
  else

    c4, c6 = c_invars(E)

    j = divexact(c4^3, discriminant(E))
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

Add two points on an elliptic curve.
"""
function +(P::EllCrvPt{T}, Q::EllCrvPt{T}) where T
  parent(P) != parent(Q) && error("Points must live on the same curve")

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
        _, _, _, a4 = a_invars(E)
        m = divexact(3*(P.coordx)^2 + a4, 2*P.coordy)
        x = m^2 - 2*P.coordx
        y = m* (P.coordx - x) - P.coordy
    else
        return infinity(E)
    end

    Erg = E([x, y], false)

  else
  a1, a2, a3, a4, a6 = a_invars(E)

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

Compute the inverse of the point $P$ on an elliptic curve.
"""
function -(P::EllCrvPt)
  E = P.parent

  if !isfinite(P)
    return infinity(E)
  end

  if E.short == true
    Q = E([P.coordx, -P.coordy], false)
  else
    a1,_, a3 = a_invars(E)
    Q = E([P.coordx, -a1*P.coordx - a3 - P.coordy], false)
  end

  return Q
end

@doc Markdown.doc"""
    ==(P::EllCrvPt, Q::EllCrvPt) -> Bool

Return true if $P$ and $Q$ are equal and live over the same elliptic curve
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

Compute the point $nP$.
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
"""
    division_polynomial_univariate(E::EllCrv, n::Int, [x]) -> Poly

Compute the n-th univariate division polynomial of an elliptic curve defined 
over a field k following Mazur and Tate. By default the result is a univariate polynomial over the base ring of `E`.
When `x` is given, the output is evaluated using the given value for `x`.

A triple of objects is returned:
- The n-th division polynomial as a univariate polynomial with a mutiplicity
   of 2 at the non-zero two-torsion points.
- The n-th division polynomial as a univariate polynomial divided by the
  univariate 2-torsion polynomial when n is even.
- The complementary factor, i.e. the first output divided by the second output.
"""
function division_polynomial_univariate(E::EllCrv, n::Int, x = PolynomialRing(base_field(E),"x")[2])
  
  R = parent(x)
  if isweierstrassmodel(E)
    poly = divpol_g_short(E,n,x)
    if mod(n,2) == 0
      _, _, _, A, B = a_invars(E)
      twotorsfactor = 4*(x^3+A*x+B)
    else
      twotorsfactor = one(R)
    end
  else
    poly = divpol_g(E,n,x)
      if mod(n,2) == 0
        b2, b4, b6 = b_invars(E)
        twotorsfactor = 4*x^3+b2*x^2+2*b4*x+b6
      else
        twotorsfactor = one(R)
      end
  end
  return twotorsfactor*poly, poly, twotorsfactor 
end

"""
    division_polynomial(E::EllCrv, n::Int, x, y) -> Poly

Compute the n-th division polynomial of an elliptic curve defined over a field
k following Mazur and Tate. When x and or y are given the output is 
automatically evaluated using the given values.
"""
function division_polynomial(E::EllCrv, n::Int,x = PolynomialRing(base_field(E),"x")[2], y = PolynomialRing(parent(x),"y")[2])
  R = parent(y)
  if isweierstrassmodel(E)
     if mod(n,2) == 0
      return 2*y*divpol_g_short(E,n,x)
    else
      return R(divpol_g_short(E,n,x))
    end
  else
    a1, _, a3 = a_invars(E)
    if mod(n,2) == 0
      return (2*y + a1*x + a3)*divpol_g(E,n,x)
    else
      return R(divpol_g(E,n,x))
    end
  end
end


function divpol_g_short(E, n::Int, x = PolynomialRing(base_field(E),"x")[2])
  
  Kx = parent(x)
  _, _, _, A, B = a_invars(E)

  
  B6sqr = (4*x^3+4*A*x+4*B)^2

  if n == 1 || n == 2
    return one(parent(x))
  elseif n == 3
    return 3*x^4 + 6*(A)*x^2 + 12*(B)*x - (A)^2
  elseif n == 4
    return 2*(x^6 + 5*(A)*x^4 + 20*(B)*x^3 - 5*(A)^2*x^2 - 4*(A)*(B)*x - 8*(B)^2 - (A)^3)
  elseif mod(n,2) == 0
    m = div(n,2)
    return (divpol_g_short(E,m,x))*(divpol_g_short(E,m+2, x)*divpol_g_short(E,m-1,x)^2 - divpol_g_short(E,m-2,x)*divpol_g_short(E,m+1,x)^2)
  else m = div(n-1,2)
    m = div(n-1,2)
    part1 = divpol_g_short(E,m+2,x)  * divpol_g_short(E,m,x)^3
    part2 = divpol_g_short(E,m-1,x) * divpol_g_short(E,m+1,x)^3
    if mod(m,2) == 0
      return B6sqr * part1 - part2
    else
      return part1 - B6sqr * part2
    end
  end
end

function divpol_g(E, n::Int, x = PolynomialRing(base_field(E),"x")[2])
  
  Kx = parent(x)
  
  b2, b4, b6, b8 = E.b_invars
  B4 = 6*x^2+b2*x+b4
  B6sqr = (4*x^3+b2*x^2+2*b4*x+b6)^2
  B8 = 3*x^4 + b2*x^3 + 3*b4*x^2 + 3*b6*x + b8

  
  if n == 1 || n ==2
    return one(Kx)
  elseif n == 3
    return B8
  elseif n == 4
    return -B6sqr+B4*B8
  elseif mod(n,2) == 0
    m = div(n-2,2)
    return divpol_g(E,m+3,x)*divpol_g(E,m+1,x)*divpol_g(E,m,x)^2 - divpol_g(E,m+1,x)*divpol_g(E,m-1,x)*divpol_g(E,m+2,x)^2
  else
    m = div(n-1,2)
    part1 = divpol_g(E,m+2,x)  * divpol_g(E,m,x)^3
    part2 = divpol_g(E,m-1,x) * divpol_g(E,m+1,x)^3
    if mod(m,2) == 0
      return B6sqr * part1 - part2
    else
      return part1 - B6sqr * part2
    end
  end
end

function replace_all_squares_modulo(f, g, F)
    # assumes that f is in Z[x,y^2] and g in Z[x]. Replaces y^2 with g.
    # the result will be in Z[x]
    z = zero(parent(g)) # this is the zero in Z[x]
    d = div(degree(f), 2) # degree of f in y^2 should be even
    for i in 0:d
        z = z + coeff(f, 2*i)*powermod(g, i, F)
    end
    return z
end
