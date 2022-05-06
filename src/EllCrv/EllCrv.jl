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
       isfinite, is_infinite, is_weierstrassmodel, is_on_curve, j_invariant,
       short_weierstrass_model, +, *, a_invars, b_invars, c_invars, equation

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

function EllipticCurve(x::Vector{T}, check::Bool = true) where T <: RingElem
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

function EllipticCurve(f::PolyElem{T}, check::Bool = true) where T
  @assert ismonic(f)
  @assert degree(f) == 3
  R = base_ring(f)
  a1 = zero(R)
  a3 = zero(R)
  coeffs = coefficients(f)
  a2 = coeffs[2]
  a4 = coeffs[1]
  a6 = coeffs[0]
  return EllipticCurve([a1, a2, a3, a4, a6], check)
end

function EllipticCurve(f::PolyElem{T}, h::PolyElem{T}, check::Bool = true) where T
  @assert ismonic(f)
  @assert degree(f) == 3
  @assert degree(h) <= 1
  R = base_ring(f)
  coeffsh = coefficients(h)
  a1 = coeffsh[1]
  a3 = coeffsh[0]
  coeffsf = coefficients(f)
  a2 = coeffsf[2]
  a4 = coeffsf[1]
  a6 = coeffsf[0]
  return EllipticCurve([a1, a2, a3, a4, a6], check)
end



################################################################################
#
#  Base Change
#
################################################################################

function base_change(E::EllCrv, K::Field)

  a1, a2, a3, a4, a6 = a_invars(E)
  return EllipticCurve(K, map(K, [a1, a2, a3, a4, a6]))

end

#Galois Field and FqFiniteField? int(char)) is dumb
function base_change(E::EllCrv{T}, n::Int) where T<:FinFieldElem

  K = base_field(E)
  char = Int(characteristic(K))
  d = degree(K)*n
  L = GF(char, d)
  return base_change(E, L)

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
  return !P.is_infinite
end

@doc Markdown.doc"""
    is_infinite(E::EllCrvPt) -> Bool

Return true if P is the point at infinity. 
"""
function is_infinite(P::EllCrvPt)
  return P.is_infinite
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
second transformation is the inverse of this map.
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

    if P.is_infinite
      return infinity(EE)
    end

    xnew = P.coordx + divexact(_b2, 12)
    ynew = P.coordy + divexact(_a1*P.coordx + _a3, 2)
    Q = EE([xnew, ynew])::EllCrvPt{T}
    return Q
  end

  # transforms a point on EE (short form) back to a point on E (long form)
  ruecktrafo = function(R::EllCrvPt)
    if R.is_infinite
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


@doc Markdown.doc"""
    isshort_weierstrass_model(E::EllCrv) -> Bool

Return true if E is in short Weierstrass form. 
"""
function isshort_weierstrass_model(E::EllCrv)
  return E.short
end


@doc Markdown.doc"""
    simplified_model(E::EllCrv) -> 
      (EE::EllCrv, function(EllCrvPt), function(EllCrvPt))

Transform an elliptic curve to simplified Weierstrass form as defined in Connell. 
Return simplified form and both transformations for points on the curve;
first transformation from E (original) to EE (simplified), 
second transformation is the inverse of this map.

Returns short Weierstrass form if $\char K \neq 2, 3$,
Returns equation of the form $y^2 + xy = x^3 + a2x^2 + a6$ 
if $\char K = 2$  and $j(E) \neq 0$,
Returns equation of the form $y^2 + a3y = x^3 + a4x + a6$ 
if $\char K = 2$ and $j(E) = 0$.
Returns equation of the form $y^2 = x^3 + a2x^2 + a6$ 
if $\char K = 3$ and $j(E) \neq 0$,
Returns equation of the form $y^2 = x^3 + a4x + a6$ 
if $\char K = 3$ and $j(E) = 0$.
"""
#Magma returns minimal model if base field is QQ. Not sure if we want the same.
function simplified_model(E::EllCrv) 
  K = base_field(E)
  a1, a2, a3, a4, a6 = a_invars(E)
  if characteristic(K)==2 
    if j_invariant(E) == 0
      return transform_rstu(E, [a2, 0, 0, 1])
    else
      return transform_rstu(E, [a3//a1, 0, a4//a1 + a3^2//a1^3, a1])
    end
  end
  
  if characteristic(K)==3
    if j_invariant(E) == 0
      return transform_rstu(E, [0, a1, a3, 1])
    else
      b2, b4 = b_invars(E)
      return transform_rstu(E, [-b4//b2, a1, a3 - a1*b4//b2, 1])
    end
  end
  
  b2, b4 = b_invars(E)
  
  F, phi1 = transform_rstu(E, [0, -a1//2, -a3//2, 1])
  G, phi2 = transform_rstu(F, [-b2//12, 0, 0, 1])
  phi = phi1 * phi2
  return G, phi, inv(phi)
end


@doc Markdown.doc"""
    issimplified_model(E::EllCrv) -> Bool

Return true if E is a simplified model. 
"""
function issimplified_model(E::EllCrv)

  if characteristic(K)==2 || characteristic(K)==3
    if j_invariant(E) == 0
      return (a1, a2) == (0, 0)
    else
      return return (a1, a3, a4) == (1, 0, 0)
    end
  end
  
  if characteristic(K)==3
    if j_invariant(E) == 0
      return (a1, a2, a3) == (0, 0, 0)
    else
      return return (a1, a3, a4) == (0, 0, 0)
    end
  end
  
  return isshort_weierstrass_model(E)
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
  Kx, x = PolynomialRing(K,"x")
  Kxy, y = PolynomialRing(Kx,"y")
  
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

@doc Markdown.doc"""
    elliptic_curve_from_j_invariant(j::T) -> EllCrv{T}

Return an elliptic curve with the given j-invariant.
"""
function elliptic_curve_from_j_invariant(j::T) where T <: FieldElem
  K = parent(j)
  char = characteristic(K)
  
  if j == zero(K) && char!=3
    return EllipticCurve(K, [0, 0, 1, 0, 0])
  end
  
  if j == K(1728)
    return EllipticCurve(K, [0, 0, 0, 1, 0])
  end

  return EllipticCurve(K, [1, 0, 0, -36//(j - 1728), -1//(j-1728)])
end

function elliptic_curve_from_j_invariant(j::T) where T <: Union{Integer, fmpz}
  return elliptic_curve_from_j_invariant(QQ(j))
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
#  Isomorphism
#
################################################################################

#Following Connell's Handbook for Elliptic Curves Chapter 4.4
function is_isomorphic(E1::EllCrv{T}, E2::EllCrv{T}) where T
  K = base_field(E1)
  char = characteristic(K)
  j1 = j_invariant(E1)
  j2 = j_invariant(E2)
 
  #First check the j-invariants
  if j1 != j2
    return false
  end
  
  if char == 2
    E1 = simplified_model(E1)
    E2 = simplified_model(E2)
    a1, a2, a3, a4, a6 = a_invars(E1)
    _a1, _a2, _a3, _a4, _a6 = a_invars(E2)
    Rx, x = PolynomialRing(K, "x")
    # j-invariant non-zero
    if j!=0
      f = x^2 + x + a2 + _a2
      return !isempty(roots(f)) 
    end
    # j-invariant is 0
    us = roots(x^3 - a3//_a3)
    for u in us
      g = x^4 + a_3x + a4 + u^4_a4
      ss = roots(g)
      for s in ss
        h = x^2 + a3*x + s^6 + a4*s^2 + a6 + u^6*_a6
        ts = roots(h)
        if !isempty(ts)
          return true
        end
      end
    end
  return false
  end
  
  if char == 3 && j1 == 0
    E1 = simplified_model(E1)
    E2 = simplified_model(E2)
    a1, a2, a3, a4, a6 = a_invars(E1)
    _a1, _a2, _a3, _a4, _a6 = a_invars(E2)
    Rx, x = PolynomialRing(K, "x")
    us = roots(x^4 - a4//_a4)
    for u in us
      g = x^3 + a4*x + a6 - u^6*_a6
      rs = roots(g)
      if !isempty(rs)
        return true
      end
    end
  return false
  end
  
  c4, c6 = c_invars(E1)
  _c4, _c6 = c_invars(E2)


  if j1!=0 && j1!=1728
    return issquare(c6//_c6)
  else
    Rx, x = PolynomialRing(K, "x")
    if j1 == 1728
      us = roots(x^4 - c4//_c4)
      if !isempty(us)
        return true
      end
      return false
    end
    if j1 == 0
      us = roots(x^4 - c6//_c6)
      if !isempty(us)
        return true
      end
    return false
    end    
  end 
end

function isomorphism(E1::EllCrv, E2::EllCrv)
K = base_field(E1)
  char = characteristic(K)
  j1 = j_invariant(E1)
  j2 = j_invariant(E2)
 
  #First check the j-invariants
  if j1 != j2
    return error("Curves are not isomorphic")
  end
  
   E1s, pre_iso = simplified_model(E1)
   E2s, _, post_iso = simplified_model(E2)
   a1, a2, a3, a4, a6 = a_invars(E1)
   _a1, _a2, _a3, _a4, _a6 = a_invars(E2)
  
  if char == 2
    Rx, x = PolynomialRing(K, "x")
    # j-invariant non-zero
    if j!=0
      f = x^2 + x + a2 + _a2
      ss = roots(f)
      if !isempty(ss)
        s = ss[1]
        phi = isomorphism(E1s, [0, s, 0, 1])
        F = codomain(phi)
        @assert F == E2s "There is a bug in isomorphism"
        return pre_iso*phi * post_iso
      else
        error("Curves are not isomorphic")
      end
    end
    # j-invariant is 0
    us = roots(x^3 - a3//_a3)
    for u in us
      g = x^4 + a_3*x + a4 + u^4_a4
      ss = roots(g)
      for s in ss
        h = x^2 + a3*x + s^6 + a4*s^2 + a6 + u^6*_a6
        ts = roots(h)
        if !isempty(ts)
          t = ts[1]
          phi = isomorphism(E1s, [s^2, s, t, u])
          F = codomain(phi)
          @assert F == E2s "There is a bug in isomorphism"
          return pre_iso * phi * post_iso
        else
          error("Curves are not isomorphic")
        end
      end
    end
  return false
  end
  
  if char == 3 && j1 == 0
    Rx, x = PolynomialRing(K, "x")
    us = roots(x^4 - a4//_a4)
    for u in us
      g = x^3 + a4*x + a6 - u^6*_a6
      rs = roots(g)
      if !isempty(rs)
        r = rs[1]
        phi = isomorphism(E1s, [r, 0, 0, u])
        F = codomain(phi)
        @assert F == E2s "There is a bug in isomorphism"
        return pre_iso * phi * post_iso
      else
        error("Curves are not isomorphic")
      end
    end
  return false
  end
  
  #Characteristic != 2, 3 and characteristic 3 with j!= 0
  c4, c6 = c_invars(E1)
  _c4, _c6 = c_invars(E2)
  usq = (c6//_c6)//(c4//_c4)
      
  if issquare(usq)
    u = sqrt(usq)
    phi = isomorphism(E1s, [0, 0, 0, u])
    F = codomain(phi)
    @assert F == E2s "There is a bug in isomorphism"
    return pre_iso * phi * post_iso
  else
    error("Curves are not isomorphic")
  end
end
#=
function isomorphism(E::EllCrv, E2::EllCrv)
  char = characteristic(base_field(E))
  if char!= 2 && char!= 3
    if is_isomorphic(E, E2)
      a1, a2, a3 = a_invars(E)
      _a1, _a2, _a3 = a_invars(E2)
      
      c4, c6 = c_invars(E)
      _c4, _c6 = c_invars(E2)
      usq = (c6//_c6)//(c4//_c4)
      
      u = sqrt(usq)
      s = (_a1*u-a1)//2
      r = (_a2*u^2-a2+s*a1+s^2)//3
      t = (_a3*u^3-a3-r*a1)//2
      return isomorphism(E,[r,s,t,u])
    else
      throw(DomainError(E, "Curves are not isomorphic over the base field"))
    end
  else
    throw(DomainError(E, "Isomorphism test only implemented for characteristic not equal to 2 or 3"))
  end
end 
=#

################################################################################
#
# T(r, s, t, u) transformation
#
################################################################################

# transformation T(r,s,t,u) as in cremona's book
function transform_rstu(E::EllCrv, T::Vector{S}) where S

  phi = isomorphism(E, T)

  return codomain(phi), phi, inv(phi)
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
function division_polynomial_univariate(E::EllCrv, n::S, x = PolynomialRing(base_field(E),"x")[2]) where S<:Union{Integer, fmpz}
  
  R = parent(x)
  if isshort_weierstrass_model(E)
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
function division_polynomial(E::EllCrv, n::S, x = PolynomialRing(base_field(E),"x")[2], y = PolynomialRing(parent(x),"y")[2]) where S<:Union{Integer, fmpz}
  R = parent(y)
  if isshort_weierstrass_model(E)
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


function divpol_g_short(E::EllCrv, n::S, x = PolynomialRing(base_field(E),"x")[2]) where S<:Union{Integer, fmpz}
  
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

function divpol_g(E::EllCrv, n::S, x = PolynomialRing(base_field(E),"x")[2]) where S<:Union{Integer, fmpz}
  
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


################################################################################
#
#  Multiplication (as maps) and division by m 
#
################################################################################

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


function division_points(P::EllCrvPt, m::S) where S<:Union{Integer, fmpz}
  
  if m==0
    return []
  end
  
  if m==1
    return [P]
  end
  
  divpoints = []
  
  E = parent(P)
  nP = -P
  twotors = (P == nP)
  
  if isinfinite(P)
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
          push!(divpoints, Q)
        end
      end
    end
  end
return divpoints
end


################################################################################
#
#  p^r-Torsion part
#
################################################################################

#Adapted from Sage: ell_generic.py

function pr_torsion_basis(E::EllCrv, p, r = typemax(Int))

  if !isprime(p)
    throw(DomainError(p, "p should be a prime number"))
  end
  
  p_torsion = division_points(infinity(E), p)
  p_rank = Int(log(fmpz(p), fmpz(length(p_torsion))))

  if p_rank == 0
    return []
  elseif p_rank == 1
    P = p_torsion[1]
    if isinfinite(P)
      P=p_torsion[2]
    end
    k = 1
    if r==1
      return [[P,k]]
    end
      
    pts = division_points(P, p)
      
    while length(pts) > 0
      k += 1
      P = pts[1]
      if r <= k
        return [[P,k]]
      end
      points = division_points(P, p)
    end        
    return [[P,k]]
  else
    P1 = popfirst!(p_torsion)
    while isinfinite(P1)
      P1 = popfirst!(p_torsion)
    end
    P2 = popfirst!(p_torsion)
    while linearly_dependant(P1,P2)
     P2 = popfirst!(p_torsion)
    end

    k = 1
    log_order = 2
    if r<= 2
      return [[P1,1],[P2,1]]
    end
    pts1 = division_points(P1, p)
    pts2 = division_points(P2, p)
    while length(pts1) > 0 && length(pts2) > 0
      k += 1
      P1 = pts1[1]
      P2 = pts2[1]
      log_order += 2
      if r<=log_order
        return [[P1,k],[P2,k]]
      end
      pts1 = division_points(P1, p)
      pts2 = division_points(P2, p)
    end
  # Now P1,P2 are a basis for the p^k torsion, which is
  # isomorphic to (Z/p^k)^2, and k is the maximal integer for
  # which this is the case.

  # We now determine whether a combination (P2 or P1+a*P2 for
  # some a) can be further divided for some a mod p; if so,
  # replace P1 by that combination, set pts to be the list of
  # solutions Q to p*Q=P1.  If no combination can be divided,
  # then the structure is (p^k,p^k) and we can stop.

    if length(pts1) > 0
      pts = pts1
    elseif length(pts2) > 0
      P1, P2 = P2, P1
      pts = pts2
    else
      for Q in [P1+a*P2: a in (1:p-1)]
          # Q runs through P1+a*P2 for a=1,2,...,p-1
        pts = division_points(Q, p)
        if len(pts) > 0
          P1 = Q
          break
        end
      end
    end
    if len(pts)==0
      return [[P1,k],[P2,k]]
    end
  # Now the structure is (p^n,p^k) for some n>k.  We need to
  # replace P1 by an element of maximal order p^n.  So far we
  # have pts = list of Q satisfying p*Q=P1, and all such Q have
  # order p^{k+1}.

  # We keep trying to divide P1 by p.  At each step, if we
  # succeed, replace P1 by any of the results and increment n.
  # If we fails try again with P1+a*P2 for a in [1..p-1]. If any
  # succeed, replace P1 by one of the resulting divided points.
  # If all fail, the structure is (p^n,p^k) and P1,P2 are
  # generators.

    n = k
    while true
      P1 = pts[1]
      n += 1
      log_order += 1
      if r <= log_order
        return [[P1,n],[P2,k]]
      end
      
      pts = division_points(P1, p)
      if len(pts) == 0
        for Q in [P1+a*P2: a in (1:p-1)]
        # Q runs through P1+a*P2 for a=1,2,...,p-1
          pts = division_points(Q, p)
          if len(pts) > 0
            break
          end
        end
        if len(pts) == 0
          return [[P1,n],[P2,k]]
        end
      end
    end
  end
end

function torsion_structure(E::EllCrv{nf_elem})
  
  T1 = T2 = infinity(E)
  k1 = k2 = 1
  bound = torsion_bound(E, 20)
  for (p,r) in factor(bound)
    ptor = pr_torsion_basis(E, p, r)
    if length(ptor) > 0
      T1 += ptor[1][1]
      k1 *= p^(ptor[1][2])
    end
    if length(ptor) > 1
      T2 += ptor[2][1]
      k2 *= p^(ptor[2][2])
    end
  end
  
  if k1 == 1
    structure = [fmpz(1)]
    gens = infinity(E)
  elseif k2 == 1
    structure = [fmpz(k1)]
    gens = [T1]
  else
    structure = [fmpz(k1), fmpz(k2)]
    gens = [T1, T2]
  end
  return [structure, gens]
end

################################################################################
#
#  Twists
#
################################################################################

function quadratic_twist(E::EllCrv{T}, d::T) where T<: FieldElem

  a1, a2, a3, a4, a6 = a_invars(E)
  K = base_field(E)
  if characteristic(K)!=2 
    return EllipticCurve(K, [a1, a3, a2*d + a1^2*(d-1)//4, a4*d^2 + a1*a3*(d^2-1)//2, a6*d^3 + a3^2*(d^3 -1)//4])
  end
  
  return EllipticCurve(K, [a1, a2+a1^2*d, a3, a4, a6 + a3^2])

end

function quadratic_twist(E::EllCrv{T}) where T<: FieldElem

  K = base_field(E)
  char = characteristic(K)
 
 if char == 2
   f, h = hyperelliptic_polynomials(E)
   if iseven(degree(K))
     u = normal_elem(GF(int(char)), K)
   else
     u = one(K)
   end
   
   return EllipticCurve(f + u*h^2, h)
 end 
  
  a = gen(K)
  return quadratic_twist(E, a)

end

#Test if we can't sometimes get two isomorphic curves
function quadratic_twists(E::EllCrv{T}) where T<: FinFieldElem

  return [E, quadratic_twist(E)]

end

function supersingular_twists2(E::EllCrv{T}) where T<: FinFieldElem
#Adapted from Magma code

  K = base_field(E)
  if isodd(degree(K))
    return [EllipticCurve(K, [0, 0, 1, 0, 0]), EllipticCurve(K, [0, 0, 1, 1, 0]), EllipticCurve(K, [0, 0, 1, 1, 1]) ]
  end
    
  u = gen(K);
  c = u
  while absolute_tr(c) == 0 
    c = rand(K) 
  end
  #First three curves
  part_1 = [EllipticCurve(K, [0, 0, 1, 0, 0]), EllipticCurve(K, [0, 0, 1, c, 0]), EllipticCurve(K, [0, 0, 1, 0, c]) ]
  #The other four
  part_2 = [EllipticCurve(K, [0, 0, a, 0, a^2*b]) for (a, b) in [[u, 0], [inv(u), 0], [u, c], [inv(u), c]]]
  return vcat(part_1, part_2)
end


function supersingular_twists3(E::EllCrv{T}) where T<: FinFieldElem
#Adapted from Magma code
    K = base_field(E)
    d = degree(K)

    if mod(d, 3) != 0
        c = one(K)
    else
      c = gen(K)
      while absolute_tr(c) == 0
        c = rand(K)
      end
    end

    if isodd(d)
      return [EllipticCurve(K, [1,0]), EllipticCurve(K, [-1, 0]), EllipticCurve(K, [-1, c]), EllipticCurve(K, [-1, -c]) ];
    end
    u = gen(K);
    #First four curves
    part_1 = [EllipticCurve(K, [-u^i,0]) for i in (0:3)]
    part_2 = [EllipticCurve(K, [-1,c]), EllipticCurve(K, [-u^2,(u^3)*c])]
    return vcat(part_1, part_2) 

end

function twists(E::EllCrv{T}) where T<: FinFieldElem
#Adapted from Magma code
   K = base_field(E);
   p = characteristic(K)
   j = j_invariant(E)
   if j != 0 && j != 1728
      return [E, quadratic_twist(E)]
   elseif p == 2
      return supersingular_twists2(E)
   elseif p == 3 then
      return supersingular_twists3(E)
   elseif j == 0
      a = gen(K)
      c4, c6 = c_invars(E)
      c = -c6//864
      n = gcd(6, order(K)-1)
      return [ EllipticCurve(K, [0,c*a^i]) for i in (0:n-1) ]
   elseif j == 1728 
      a = gen(K)
      c4, c6 = c_invars(E)
      c = -c4//48;
      n = gcd(4, order(K)-1)
      return [ EllipticCurve(K, [c*a^i,0]) : i in (0:n-1)]
   end
end


function istwist(E::EllCrv, F::EllCrv)

  return j_invariant(E) == j_invariant(F)
end


################################################################################
#
#  Misc
#
################################################################################

function log(a::fmpz, b::fmpz)
  log(b)/log(a)
end

function linearly_dependant(P1::EllCrvPt{T}, P2::EllCrvPt{T}) where T

#if !istorsion_point(P1)||!istorsion_point(P2)
#  throw(DomainError, "Points need to be torsion_points")
#end

A = P1
B = P2

while isfinite(A)
  while isfinite(B)
    if isinfinite(A+B)
      return true
    end
    B+=P2   
   end 
   A+=P1
   B+=P2
end
return false
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
