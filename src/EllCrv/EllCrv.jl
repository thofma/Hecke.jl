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

function Base.getindex(P::EllCrvPt, i::Int)
  @req 1 <= i <= 3 "Index must be 1, 2 or 3"
  
  K = base_field(parent(P))
  
  if is_infinite(P)
    if i == 1 
      return zero(K)
    elseif i == 2
      return one(K)
    elseif i == 3
      return zero(K)
    end
  end
  if i == 1
    return P.coordx
  elseif i == 2
    return P.coordy
  elseif i == 3
    return one(K)
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

#  Implicit promotion in characteristic 0
function EllipticCurve(x::Vector{<: IntegerUnion}; check::Bool = true)
  return EllipticCurve(QQFieldElem[QQ(z) for z in x], check = check)
end

function EllipticCurve(x::Vector{Rational{T}}; check::Bool = true) where {T <: IntegerUnion}
  return EllipticCurve(QQFieldElem[QQ(z) for z in x], check = check)
end

@doc raw"""
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

@doc raw"""
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

@doc raw"""
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

@doc raw"""
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

@doc raw"""
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

################################################################################
#
#  Equality of Models
#
################################################################################

@doc raw"""
    ==(E::EllCrv, F::EllCrv) -> Bool

Return true if $E$ and $F$ are given by the same model over the same field.
"""
function ==(E::EllCrv, F::EllCrv)
  return a_invars(E) == a_invars(F) && base_field(E) == base_field(F)
end

################################################################################
#
#  Elementary invariants
#
################################################################################

@doc raw"""
    a_invars(E::EllCrv{T}) -> Tuple{T, T, T, T, T}

Return the Weierstrass coefficients of E as a tuple (a1, a2, a3, a4, a6)
such that E is given by y^2 + a1xy + a3y = x^3 + a2x^2 + a4x + a6.
"""
function a_invars(E::EllCrv)
  return E.a_invars
end

@doc raw"""
    coefficients(E::EllCrv{T}) -> Tuple{T, T, T, T, T}

Return the Weierstrass coefficients of E as a tuple (a1, a2, a3, a4, a6)
such that E is given by y^2 + a1xy + a3y = x^3 + a2x^2 + a4x + a6.
"""
coefficients(E::EllCrv) = a_invars(E)

@doc raw"""
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

@doc raw"""
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

@doc raw"""
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
@doc raw"""
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

@doc raw"""
    equation(E::EllCrv) -> Poly

Return the equation defining the elliptic curve E.
"""
function equation(E::EllCrv)
  K = base_field(E)
  Kxy,(x,y) = polynomial_ring(K, ["x","y"])

  a1, a2, a3, a4, a6 = a_invars(E)

  return y^2 + a1*x*y + a3*y - (x^3 + a2*x^2 + a4*x + a6)
end

@doc raw"""
    hyperelliptic_polynomials(E::EllCrv) -> Poly, Poly

Return f, h such that E is given by y^2 + h*y = f
"""
function hyperelliptic_polynomials(E::EllCrv)

  K = base_field(E)
  Kx, x = polynomial_ring(K,"x")
  a1, a2, a3, a4, a6 = a_invars(E)

  return x^3 + a2*x^2 + a4*x + a6, a1*x + a3
end


################################################################################
#
#  Points on Elliptic Curves
#
################################################################################

function (E::EllCrv{T})(coords::Vector{S}; check::Bool = true) where {S, T}
  if !(2 <= length(coords) <= 3) 
    error("Points need to be given in either affine coordinates (x, y) or projective coordinates (x, y, z)")
  end
  
  if length(coords) == 3
    if coords[1] == 0 && coords[3] == 0
      if coords[2] != 0
        return infinity(E)
      else
        error("The triple [0: 0: 0] does not define a point in projective space.")
      end
    end
    coords = [coords[1]//coords[3], coords[2]//coords[3]] 
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

@doc raw"""
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
  Ry, y = polynomial_ring(R,"y")
  f = y^2 +a1*x*y + a3*y - x^3 - a2*x^2 - a4*x - a6
  ys = roots(f)
  pts = []
   for yi in ys
     push!(pts, E([x, yi]))
   end
  return pts
end


@doc raw"""
    is_finite(P::EllCrvPt) -> Bool

Return true if P is not the point at infinity.
"""
function is_finite(P::EllCrvPt)
  return !P.is_infinite
end

@doc raw"""
    is_infinite(P::EllCrvPt) -> Bool

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

@doc raw"""
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
    #if P.is_infinite
    #    print(io, "Point at infinity of $(P.parent)")
    #else
        print(io, "Point  ($(P[1]) : $(P[2]) : $(P[3]))  of $(P.parent)")
    #end
end


################################################################################
#
#  Addition of Points
#
################################################################################

# washington p. 14, cohen p. 270
@doc raw"""
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
    if P[1] != Q[1]
        m = divexact(Q[2] - P[2], Q[1] - P[1])
        x = m^2 - P[1] - Q[1]
        y = m * (P[1] - x) - P[2]
    elseif P[2] != Q[2]
        return infinity(E)
    elseif P[2] != 0
        _, _, _, a4 = a_invars(E)
        m = divexact(3*(P[1])^2 + a4, 2*P[2])
        x = m^2 - 2*P[1]
        y = m* (P[1] - x) - P[2]
    else
        return infinity(E)
    end

    Erg = E([x, y], check = false)

  else
  a1, a2, a3, a4, a6 = a_invars(E)

    # Use [Cohen, p. 270]
    if P[1] == Q[1]
      if Q[2] == -a1*P[1] - a3 - P[2] # then P = -Q
        return infinity(E)
      elseif P[2] == Q[2] # then P = Q
        m = divexact(3*((P[1])^2) + 2*a2*P[1] + a4 - a1*P[2], 2*P[2] + a1*P[1] + a3)
        x = -P[1] - Q[1] - a2 + a1*m + m^2
        y = -P[2] - m*(x - P[1]) - a1*x - a3
      else # then P != +-Q
        m = divexact(Q[2] - P[2], Q[1] - P[1])
        x = -P[1] - Q[1] - a2 + a1*m + m^2
        y = -P[2] - m*(x - P[1]) - a1*x - a3
      end
    else # now P != +-Q
      m = divexact(Q[2] - P[2], Q[1] - P[1])
      x = -P[1] - Q[1] - a2 + a1*m + m^2
      y = -P[2] - m*(x - P[1]) - a1*x - a3
    end

    Erg = E([x, y], check = false)
  end
  return Erg
end

@doc raw"""
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

@doc raw"""
    -(P::EllCrvPt) -> EllCrvPt

Compute the inverse of the point $P$ on an elliptic curve.
"""
function -(P::EllCrvPt)
  E = P.parent

  if !is_finite(P)
    return infinity(E)
  end

  if E.short == true
    Q = E([P[1], -P[2]], check = false)
  else
    a1,_, a3 = a_invars(E)
    Q = E([P[1], -a1*P[1] - a3 - P[2]], check = false)
  end

  return Q
end

@doc raw"""
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
  if P[1] == Q[1] && P[2] == Q[2]
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
@doc raw"""
    *(n::Int, P::EllCrvPt) -> EllCrvPt

Compute the point $nP$.
"""
function *(n ::S, P::EllCrvPt) where S<:Union{Integer, ZZRingElem}
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
function multiplication_by_m_numerator(E::EllCrv, m::S, x = polynomial_ring(base_field(E),"x")[2]) where S<:Union{Integer, ZZRingElem}

  p = characteristic(base_field(E))
  if p == 2
    #See Blake, Seroussi, Smart - Elliptic Curves in Cryptography III.4.2
    psi_mmin = division_polynomial(E, m-1, x)(1)
    psi_m = division_polynomial(E, m, x)(1)
    psi_mplus = division_polynomial(E, m+1, x)(1)
    return x*psi_m^2 + (psi_mmin*psi_mplus)
  end

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
function multiplication_by_m_denominator(E::EllCrv, m::S, x = polynomial_ring(base_field(E),"x")[2]) where S<:Union{Integer, ZZRingElem}
  p = characteristic(base_field(E))
  if p == 2
    #See Blake, Seroussi, Smart - Elliptic Curves in Cryptography III.4.2
    psi_m = division_polynomial(E, m, x)(1)
    return psi_m^2
  end

  b2, b4, b6, b8 = b_invars(E)
  B6= 4*x^3+b2*x^2+2*b4*x+b6
  psi_m = division_polynomial_univariate(E, m, x)[2]

   if mod(m,2) == 0
      return B6 * psi_m^2
    else
      return psi_m^2
    end
end

#Returns the y-coordinate of the multiplication by m map
#For characteristic 2 the curve needs to be in simplified form
#See Blake, Seroussi, Smart - Elliptic Curves in Cryptography III
function multiplication_by_m_y_coord(E::EllCrv, m::S, x = polynomial_ring(base_field(E),"x")[2], y = polynomial_ring(parent(x),"y")[2]) where S<:Union{Integer, ZZRingElem}

  Kxy = parent(y)


  a1, a2, a3, a4 = a_invars(E)
  p = characteristic(base_field(E))
  if p == 2
    # See N. Koblitz - Constructing Elliptic Curve Cryptosystems, page 63

    f_mmin2 = division_polynomial(E, m-2, x)
    f_mmin = division_polynomial(E, m-1, x)
    f_m = division_polynomial(E, m, x)
    f_mplus = division_polynomial(E, m+1, x)


    if j_invariant(E) == 0 #Curve is supersingular
      f2 = a3
      f2on = a3
      h4 = x^2 + a4
    else
      f2 = x
      f2on = x + f_mmin*f_mplus//f_m^2
      h4 = x^2 + y
    end

    return y + f2on + (f_mplus^2*f_mmin2//(f2*f_m^3) + h4*(f_mplus*f_mmin)//(f2*f_m^2))
  end

  b2, b4, b6, b8 = b_invars(E)
  B6= 4*x^3+b2*x^2+2*b4*x+b6
  x = Kxy(x)
  psi_mplus2 = division_polynomial(E, m+2, x, y)
  psi_mmin = division_polynomial(E, m-1, x, y)
  psi_m_univ = division_polynomial_univariate(E, m, x)[2]
  psi_mplus = division_polynomial(E, m+1, x, y)
  psi_mmin2 = division_polynomial(E, m-2, x, y)
  
  if p == 3 && j_invariant(E) != 0   
    if iseven(m) 
      num = (psi_mplus2*psi_mmin^2 - psi_mmin2*psi_mplus^2) - a1*(x* psi_m_univ^2*B6 -psi_mmin*psi_mplus)*psi_m_univ
       denom = 2*B6^2*psi_m_univ^3
    else
      num = (psi_mplus2*psi_mmin^2 - psi_mmin2*psi_mplus^2) - a1*(x* psi_m_univ^2 -psi_mmin*psi_mplus*B6)*psi_m_univ
      denom = 4*y*psi_m_univ^3 
    end
    return num//denom
  end
  

  num = (psi_mplus2*psi_mmin^2 - psi_mmin2*psi_mplus^2)

  if iseven(m)
    denom = 2*B6^2*psi_m_univ^3
  else
    denom = 4*y*psi_m_univ^3
  end

  return num//denom
  #return (psi_2m//(2*psi_m) - (a1*phi_m + a3*psi_m^2)*psi_m//2)//(psi_m^3)
  #return (psi_2m - (a1*phi_m + a3*psi_m)*psi_m)//(2*psi_m^2)
end

@doc raw"""
    division_points(P::EllCrvPt, m::Int) -> EllCrvPt

Compute the set of points Q defined over the base field such that m*Q = P.
Returns the empty set if no such points exist.
"""
function division_points(P::EllCrvPt, m::S) where S<:Union{Integer, ZZRingElem}

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
    g = multiplication_by_m_numerator(E,m) - P[1]*multiplication_by_m_denominator(E,m)
    if twotors
      if mod(m, 2) == 0
        g = sqrt(g)
      else
        x = gen(parent(g))
        g0 = x - P[1]
        g = numerator(g//g0)
        g = sqrt(g)
        g = g0*g
      end
    end
  end
  for a in roots(g)
    a1, a2, a3, a4, a6 = a_invars(E)
    R = base_field(E)
    Ry, y = polynomial_ring(R,"y")
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

@doc raw"""
    //(P::EllCrvPt, n::Int) -> EllCrvPt

Return a point $Q$ such that $nQ = P$.
"""
function //(P::EllCrvPt, n ::S) where S<:Union{Integer, ZZRingElem}
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

function log(a::ZZRingElem, b::ZZRingElem)
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
