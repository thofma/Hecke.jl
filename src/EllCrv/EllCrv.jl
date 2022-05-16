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

export EllipticCurve, infinity, base_field, base_change, j_invariant, 
       elliptic_curve_from_j_invariant, is_finite, is_infinite, is_on_curve, +, *, 
       //, a_invars, b_invars, c_invars, equation, hyperelliptic_polynomials, 
       points_with_x, division_points

################################################################################
#
#  Types
#
################################################################################

mutable struct EllCrv{T}
  base_field::Ring
  short::Bool
  a_invars::Tuple{T, T, T, T, T}
  b_invars::Tuple{T, T, T, T}
  c_invars::Tuple{T,T}
  disc::T
  j::T
  coeff::Vector{T}

  torsion_points#::Vector{EllCrvPt}
  torsion_structure#Tuple{Vector{Int}, Vector{EllCrvPt}}

  function EllCrv{T}(coeffs::Vector{T}, check::Bool = true) where {T}
    if length(coeffs) == 2
      if check
        d = -16*(4*coeffs[1]^3 + 27*coeffs[2]^2)
        if !iszero(d)
          E = new{T}()
          E.short = true
          # fixed on Nemo master
          K = parent(coeffs[1])
          E.base_field = K
          E.a_invars = (zero(K), zero(K), zero(K), coeffs[1], coeffs[2])
          E.disc = d
        else
          error("Discriminant is zero")
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
          if iszero(a1) && iszero(a2) && iszero(a3)
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
        if iszero(a1) && iszero(a2) && iszero(a3)
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
    E.coeff = coeffs
    return E
  end
end

mutable struct EllCrvPt{T}
  coordx::T
  coordy::T
  is_infinite::Bool
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
    z.is_infinite = true
    return z
  end
end

################################################################################
#
#  Constructors for Elliptic Curve
#
################################################################################

function EllipticCurve(x::Vector{T}; check::Bool = true) where T <: RingElem
  E = EllCrv{T}(x, check)
  return E
end

function EllipticCurve(K::Field, x::Vector{T}; check::Bool = true) where T
  if T === elem_type(K)
    return EllipticCurve(x, check = check)
  else
    return EllipticCurve(elem_type(K)[K(z) for z in x], check = check)
  end
end

#  Implicit promotion in characterstic 0
function EllipticCurve(x::Vector{<: IntegerUnion}; check::Bool = true)
  return EllipticCurve(fmpq[QQ(z) for z in x], check = check)
end

function EllipticCurve(x::Vector{Rational{T}}; check::Bool = true) where {T <: IntegerUnion}
  return EllipticCurve(fmpq[QQ(z) for z in x], check = check)
end

@doc Markdown.doc"""
    EllipticCurve(f::PolyElem; check::Bool = true) -> EllCrv

Return the elliptic curve $y^2 = f(x)$. The polynomial $f$ must be monic of
degree 3.
"""
function EllipticCurve(f::PolyElem{<: FieldElem}; check::Bool = true)
  @req ismonic(f) "Polynomial must be monic"
  @req degree(f) == 3 "Polynomial must be of degree 3"
  R = base_ring(f)
  a1 = zero(R)
  a3 = zero(R)
  coeffs = coefficients(f)
  a2 = coeffs[2]
  a4 = coeffs[1]
  a6 = coeffs[0]
  return EllipticCurve([a1, a2, a3, a4, a6], check = check)
end

@doc Markdown.doc"""
    EllipticCurve(f::PolyElem; h::PolyElem, check::Bool = true) -> EllCrv

Return the elliptic curve $y^2 + h(x)y = f(x)$. The polynomial $f$ must be monic of
degree 3 and $h$ of degree at most 1.
"""
function EllipticCurve(f::PolyElem{T}, h::PolyElem{T}, check::Bool = true) where T
  @req ismonic(f) "First polynomial must be monic"
  @req degree(f) == 3 "First polynomial must be of degree 3"
  @req degree(h) <= 1 "Second polynomial must be of degree at most 1"
  R = base_ring(f)
  coeffsh = coefficients(h)
  a1 = coeffsh[1]
  a3 = coeffsh[0]
  coeffsf = coefficients(f)
  a2 = coeffsf[2]
  a4 = coeffsf[1]
  a6 = coeffsf[0]
  return EllipticCurve([a1, a2, a3, a4, a6], check = check)
end

function EllipticCurve(f::PolyElem{T}, g, check::Bool = true) where T
  return EllipticCurve(f, parent(f)(g))
end

@doc Markdown.doc"""
    elliptic_curve_from_j_invariant(j::FieldElem) -> EllCrv

Return an elliptic curve with the given j-invariant.
"""
function elliptic_curve_from_j_invariant(j::FieldElem)
  K = parent(j)
  char = characteristic(K)
 
  if j == zero(K) && char != 3
    return EllipticCurve(K, [0, 0, 1, 0, 0])
  end

  if j == K(1728)
    return EllipticCurve(K, [0, 0, 0, 1, 0])
  end

  return EllipticCurve(K, [1, 0, 0, divexact(-36, j - 1728), divexact(-1,j-1728)])
end

function elliptic_curve_from_j_invariant(j::IntegerUnion)
  return elliptic_curve_from_j_invariant(QQ(j))
end

################################################################################
#
#  Field access
#
################################################################################

@doc Markdown.doc"""
    base_field(E::EllCrv) -> Field

Return the base field over which `E` is defined.
"""
function base_field(E::EllCrv{T}) where T
  return E.base_field::parent_type(T)
end

################################################################################
#
#  Base Change
#
################################################################################

@doc Markdown.doc"""
    base_change(K::Field, E::EllCrv) -> EllCrv

Return the base change of the elliptic curve $E$ over K if coercion is
possible.
"""
function base_change(K::Field, E::EllCrv)
  a1, a2, a3, a4, a6 = a_invars(E)
  return EllipticCurve(K, map(K, [a1, a2, a3, a4, a6])::Vector{elem_type(K)})
end

function base_change(f, E::EllCrv)
  a1, a2, a3, a4, a6 = a_invars(E)
  return EllipticCurve(map(f, [a1, a2, a3, a4, a6]))
end

@doc Markdown.doc"""
    base_change(E::EllCrv{FinFieldElem}, n::Int) -> EllCrv{FinFieldElem}

Given an elliptic curve $E$ defined over the finite field $\mathbb{F}_q$.
Return the base change of the curve $E$ over the field $\mathbb{F}_{q^n}$.
"""
function base_change(E::EllCrv{T}, n::Int) where T<:FinFieldElem
  K = base_field(E)
  #char gets converted to an Int here as it is currently impossible to 
  #take a field extension of GF(p) when p is fmpz.
  char = Int(characteristic(K))
  d = degree(K)*n
  L = GF(char, d)
  return base_change(E, L)
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
#  Elementary invariants
#
################################################################################

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
    return E.b_invars
  else
    a1, a2, a3, a4, a6 = a_invars(E)

    b2 = a1^2 + 4*a2
    b4 = a1*a3 + 2*a4
    b6 = a3^2 + 4*a6
    b8 = a1^2*a6 - a1*a3*a4 + 4*a2*a6 + a2*a3^2 - a4^2
    E.b_invars = b2, b4, b6, b8
    return b2, b4, b6, b8
  end
end

@doc Markdown.doc"""
    c_invars(E::EllCrv{T}) -> Tuple{T, T, T, T}

Return the c-invariants of E as a tuple (c4, c6).
"""
function c_invars(E::EllCrv)
  if isdefined(E, :c_invars)
    return E.c_invars
  else
    b2,b4,b6,b8 = b_invars(E)
    c4 = b2^2 - 24*b4
    c6 = -b2^3 + 36*b2*b4 - 216*b6
    E.c_invars = c4, c6
    return  c4, c6
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
  if is_short_weierstrass_model(E)
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
    j_invariant(E::EllCrv{T}) -> T

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
#  Equations
#
################################################################################

@doc Markdown.doc"""
    equation(E::EllCrv) -> Poly

Return the equation defining the elliptic curve E. 
"""
function equation(E::EllCrv)
  K = base_field(E)
  Kxy,(x,y) = PolynomialRing(K, ["x","y"])
  
  a1, a2, a3, a4, a6 = a_invars(E)
  
  return y^2 + a1*x*y + a3*y - (x^3 + a2*x^2 + a4*x + a6)
end

@doc Markdown.doc"""
    hyperelliptic_polynomials(E::EllCrv) -> Poly, Poly

Return f, h such that E is given by y^2 + h*y = f
"""
function hyperelliptic_polynomials(E::EllCrv)

  K = base_field(E)
  Kx, x = PolynomialRing(K,"x")
  a1, a2, a3, a4, a6 = a_invars(E)
  
  return x^3 + a2*x^2 + a4*x + a6, a1*x + a3
end


################################################################################
#
#  Points on Elliptic Curves
#
################################################################################

function (E::EllCrv{T})(coords::Vector{S}; check::Bool = true) where {S, T}
  if length(coords) != 2
    error("Need two coordinates")
  end

  if S === T
    parent(coords[1]) != base_field(E) &&
        error("Objects must be defined over same field")
    return EllCrvPt{T}(E, coords, check)
  else
    return EllCrvPt{T}(E, map(base_field(E), coords)::Vector{T}, check)
  end
end

################################################################################
#
#  Parent
#
################################################################################

function parent(P::EllCrvPt)
  return P.parent
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

function points_with_x(E::EllCrv{T}, x) where T
  R = base_field(E)
  x = R(x)
  a1, a2, a3, a4, a6 = a_invars(E)
  Ry, y = PolynomialRing(R,"y")
  f = y^2 +a1*x*y + a3*y - x^3 - a2*x^2 - a4*x - a6
  ys = roots(f)
  pts = []
   for yi in ys 
     push!(pts, E([x, yi]))
   end
  return pts
end


@doc Markdown.doc"""
    is_finite(E::EllCrvPt) -> Bool

Return true if P is not the point at infinity. 
"""
function is_finite(P::EllCrvPt)
  return !P.is_infinite
end

@doc Markdown.doc"""
    is_infinite(E::EllCrvPt) -> Bool

Return true if P is the point at infinity. 
"""
function is_infinite(P::EllCrvPt)
  return P.is_infinite
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
#  ElemType
#
################################################################################

function elem_type(E::EllCrv{T}) where T
  return EllCrvPt{T}
end

function elem_type(::Type{EllCrv{T}}) where T
  return EllCrvPt{T}
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
    if P.is_infinite
        print(io, "Point at infinity of $(P.parent)")
    else
        print(io, "Point $(P.coordx),$(P.coordy) of $(P.parent)")
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
  if P.is_infinite
      return Q
  elseif Q.is_infinite
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

    Erg = E([x, y], check = false)

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

    Erg = E([x, y], check = false)
  end
  return Erg
end

@doc Markdown.doc"""
    -(P::EllCrvPt, Q::EllCrvPt) -> EllCrvPt

Subtract two points on an elliptic curve.
"""
function -(P::EllCrvPt{T}, Q::EllCrvPt{T}) where T

  return P+(-Q)

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

  if !is_finite(P)
    return infinity(E)
  end

  if E.short == true
    Q = E([P.coordx, -P.coordy], check = false)
  else
    a1,_, a3 = a_invars(E)
    Q = E([P.coordx, -a1*P.coordx - a3 - P.coordy], check = false)
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
  if P.is_infinite && Q.is_infinite
    return true
  end

  # one of them is infinite
  if xor(P.is_infinite, Q.is_infinite)
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
function *(n ::S, P::EllCrvPt) where S<:Union{Integer, fmpz}
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
#  Multiplication (as maps) and division by m 
#
################################################################################

#Returns the numerator of the multiplication by m map
function multiplication_by_m_numerator(E::EllCrv, m::S, x = PolynomialRing(base_field(E),"x")[2]) where S<:Union{Integer, fmpz}

  Kx = parent(x)
  
  b2, b4, b6, b8 = b_invars(E)
  B6= 4*x^3+b2*x^2+2*b4*x+b6
  
  psi_mmin = division_polynomial_univariate(E, m-1, x)[2]
  psi_m = division_polynomial_univariate(E, m, x)[2]
  psi_mplus = division_polynomial_univariate(E, m+1, x)[2]
  
   if mod(m,2) == 0
      return x * B6 * psi_m^2 - psi_mmin * psi_mplus
    else
      return x * psi_m^2-B6 * psi_mmin * psi_mplus
    end
end

#Returns the denominator of the multiplication by m map
function multiplication_by_m_denominator(E::EllCrv, m::S, x = PolynomialRing(base_field(E),"x")[2]) where S<:Union{Integer, fmpz}
  
  Kx = parent(x)
  
  b2, b4, b6, b8 = b_invars(E)
  B6= 4*x^3+b2*x^2+2*b4*x+b6
  
  psi_m = division_polynomial_univariate(E, m, x)[2]

   if mod(m,2) == 0
      return B6 * psi_m^2
    else
      return psi_m^2
    end
end

@doc Markdown.doc"""
    division_points(P::EllCrvPt, m::Int) -> EllCrvPt

Compute the set of points Q defined over the base field such that m*Q = P.
Returns the empty set if no such points exist.
"""
function division_points(P::EllCrvPt, m::S) where S<:Union{Integer, fmpz}
  
  if m==0
    return typeof(P)[]
  end
  
  if m==1
    return [P]
  end
  
  if m<0
    m = -m
    P = -P
  end
  
  divpoints = typeof(P)[]
  
  E = parent(P)
  nP = -P
  twotors = (P == nP)
  
  if is_infinite(P)
    push!(divpoints, P)
    g = division_polynomial_univariate(E, m)[1]
  else
    g = multiplication_by_m_numerator(E,m) - P.coordx*multiplication_by_m_denominator(E,m)
    
    if twotors
      if mod(m, 2) == 0
        g = sqrt(g)
      else
        x = gen(parent(g))
        g0 = x - P.coordx
        g = numerator(g//g0)
        g = sqrt(g)
        g = g0*g
      end
    end
  end
  for a in roots(g)   
    a1, a2, a3, a4, a6 = a_invars(E)
    R = base_field(E)
    Ry, y = PolynomialRing(R,"y")
    f = y^2 +a1*a*y + a3*y - a^3 - a2*a^2 - a4*a - a6
    ys = roots(f)
    if length(ys)!=0
      Q = E([a,ys[1]])
      nQ = -Q
      mQ = m*Q
      if twotors
        if mQ == P
          push!(divpoints,Q)
          if nQ != Q
            push!(divpoints, nQ)
          end
        end
      else
        if mQ == P
          push!(divpoints, Q)
        elseif mQ == nP
          push!(divpoints, nQ)
        end
      end
    end
  end
  return divpoints
end

@doc Markdown.doc"""
    //(P::EllCrvPt, n::Int) -> EllCrvPt

Return a point $Q$ such that $nQ = P$.
"""
function //(P::EllCrvPt, n ::S) where S<:Union{Integer, fmpz}
  L = division_points(P, n)
  if !isempty(L) 
    return L[1]
  else
    error("Point is not divisible by n")
  end
end

################################################################################
#
#  Misc
#
################################################################################

function log(a::fmpz, b::fmpz)
  log(b)/log(a)
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
