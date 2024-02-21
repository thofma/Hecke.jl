################################################################################
#
#          EllipticCurve/EllipticCurve.jl : Elliptic curves over general fields
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

################################################################################
#
#  Types
#
################################################################################

@attributes mutable struct EllipticCurve{T}
  base_field::Ring
  short::Bool
  a_invariants::Tuple{T, T, T, T, T}
  b_invariants::Tuple{T, T, T, T}
  c_invariants::Tuple{T,T}
  disc::T
  j::T
  coeff::Vector{T}

  torsion_points#::Vector{EllipticCurvePoint}
  torsion_structure#Tuple{Vector{Int}, Vector{EllipticCurvePoint}}

  function EllipticCurve{T}(coeffs::Vector{T}, check::Bool = true) where {T}
    if length(coeffs) == 2
      if check
        d = -16*(4*coeffs[1]^3 + 27*coeffs[2]^2)
        if !iszero(d)
          E = new{T}()
          E.short = true
          # fixed on Nemo master
          K = parent(coeffs[1])
          E.base_field = K
          E.a_invariants = (zero(K), zero(K), zero(K), coeffs[1], coeffs[2])
          E.disc = d
        else
          error("Discriminant is zero")
        end
      else
        E = new{T}()
        E.short = true
        K = parent(coeffs[1])
        E.base_field = K
        E.a_invariants = (zero(K),zero(K),zero(K),coeffs[1],coeffs[2])
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
          E.a_invariants = (a1, a2, a3, a4, a6)
          E.b_invariants = (b2, b4, b6, b8)
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
        E.a_invariants = (a1, a2, a3, a4, a6)
        E.base_field = parent(coeffs[1])
      end
    else
      error("Length of coefficient array must be either 2 or 5")
    end
    E.coeff = coeffs
    return E
  end
end

mutable struct EllipticCurvePoint{T}
  coordx::T
  coordy::T
  is_infinite::Bool
  parent::EllipticCurve{T}

  function EllipticCurvePoint{T}(E::EllipticCurve{T}, coords::Vector{T}, check::Bool = true) where {T}
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

  function EllipticCurvePoint{T}(E::EllipticCurve{T}) where {T}
    z = new{T}()
    z.parent = E
    z.is_infinite = true
    return z
  end
end

function Base.getindex(P::EllipticCurvePoint, i::Int)
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

@doc raw"""
    elliptic_curve([K::Field], x::Vector; check::Bool = true) -> EllipticCurve

Construct an elliptic curve with Weierstrass equation specified by
the coefficients in `x`, which must have either length 2 or 5.

Per default, it is checked whether the discriminant is non-zero. This can be
disabled by setting `check = false`.

# Examples

```jldoctest
julia> elliptic_curve(QQ, [1, 2, 3, 4, 5])
Elliptic curve with equation
y^2 + x*y + 3*y = x^3 + 2*x^2 + 4*x + 5

julia> elliptic_curve(GF(3), [1, 1])
Elliptic curve with equation
y^2 = x^3 + x + 1
```
"""
elliptic_curve

function elliptic_curve(x::Vector{T}; check::Bool = true) where T <: RingElem
  E = EllipticCurve{T}(x, check)
  return E
end

function elliptic_curve(K::Field, x::Vector{T}; check::Bool = true) where T
  if T === elem_type(K)
    return elliptic_curve(x, check = check)
  else
    return elliptic_curve(elem_type(K)[K(z) for z in x], check = check)
  end
end

# Implicit promotion in characteristic 0
function elliptic_curve(x::Vector{<: IntegerUnion}; check::Bool = true)
  return elliptic_curve(QQFieldElem[QQ(z) for z in x], check = check)
end

function elliptic_curve(x::Vector{Rational{T}}; check::Bool = true) where {T <: IntegerUnion}
  return elliptic_curve(QQFieldElem[QQ(z) for z in x], check = check)
end

# A constructor to create an elliptic curve from a bivariate polynomial.
# One can specify how to interpret the polynomial via the second and the
# third argument.
@doc raw"""
    elliptic_curve(f::MPolyRingElem, x::MPolyRingElem, y::MPolyRingElem) -> EllipticCurve

Construct an elliptic curve from a bivariate polynomial `f` in long Weierstrass form.
The second and third argument specify variables of the `parent` of `f` so that
``f = c ⋅ (-y² + x³ - a₁ ⋅ xy + a₂ ⋅ x² - a₃ ⋅ y + a₄ ⋅ x + a₆)``.
"""
function elliptic_curve(f::MPolyRingElem, x::MPolyRingElem, y::MPolyRingElem)
  R = parent(f)
  @assert ngens(R) == 2 "polynomial must be bivariate"
  @assert x in gens(R) && y in gens(R) "second and third argument must be ring variables"
  k = coefficient_ring(f)
  kf = k
  if !(k isa Field)
    kf = fraction_field(k)
  end
  # coeff returns a polynomial in parent(f); we pick out the constant coefficient.
  my_const = t->(iszero(t) ? zero(coefficient_ring(parent(t))) : first(coefficients(t)))
  c = my_const(coeff(f, [x, y], [3, 0])::MPolyRingElem)
  @assert parent(c)===k
  f = inv(c)*f
  @assert coeff(f, [x,y], [0,2]) == -1 "coefficient of y^2 must be -1"
  a6 = coeff(f, [x,y], [0,0])
  a4 = coeff(f, [x,y], [1,0])
  a2 = coeff(f, [x,y], [2,0])
  a3 = -coeff(f, [x,y], [0,1])
  a1 = -coeff(f, [x,y], [1,1])
  a_invariants = [my_const(i) for i in [a1,a2,a3,a4,a6]]
  (a1,a2,a3,a4,a6) = a_invariants
  @assert f == (-(y^2 + a1*x*y + a3*y) + (x^3 + a2*x^2 + a4*x + a6))
  E = elliptic_curve(kf, kf.([a1,a2,a3,a4,a6]))
  return E
end


@doc raw"""
    elliptic_curve(f::PolyRingElem, [h::PolyRingElem,] check::Bool = true) -> EllipticCurve

Return the elliptic curve $y^2 + h(x)y = f(x)$ respectively $y^2 + y = f(x)$,
if no $h$ is specified. The polynomial $f$ must be monic of degree 3 and $h$ of
degree at most 1.

Per default, it is checked whether the discriminant is non-zero. This can be
disabled by setting `check = false`.

# Examples

```jldoctest
julia> Qx, x = QQ["x"];

julia> elliptic_curve(x^3 + x + 1)
Elliptic curve with equation
y^2 = x^3 + x + 1

julia> elliptic_curve(x^3 + x + 1, x)
Elliptic curve with equation
y^2 + x*y = x^3 + x + 1
```
"""
function elliptic_curve(f::PolyRingElem{T}, h::PolyRingElem{T} = zero(parent(f)); check::Bool = true) where T
  @req is_monic(f) "First polynomial must be monic"
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
  return elliptic_curve([a1, a2, a3, a4, a6], check = check)
end

function elliptic_curve(f::PolyRingElem{T}, g; check::Bool = true) where T
  return elliptic_curve(f, parent(f)(g))
end

@doc raw"""
    elliptic_curve_from_j_invariant(j::FieldElem) -> EllipticCurve

Return an elliptic curve with the given $j$-invariant.

# Examples

```jldoctest
julia> K = GF(3)
Prime field of characteristic 3

julia> elliptic_curve_from_j_invariant(K(2))
Elliptic curve with equation
y^2 + x*y = x^3 + 1
```
"""
function elliptic_curve_from_j_invariant(j::FieldElem)
  K = parent(j)
  char = characteristic(K)

  if j == zero(K) && char != 3
    return elliptic_curve(K, [0, 0, 1, 0, 0])
  end

  if j == K(1728)
    return elliptic_curve(K, [0, 0, 0, 1, 0])
  end

  return elliptic_curve(K, [1, 0, 0, divexact(-36, j - 1728), divexact(-1,j-1728)])
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
    base_field(E::EllipticCurve) -> Field

Return the base field over which `E` is defined.
"""
function base_field(E::EllipticCurve{T}) where T
  return E.base_field::parent_type(T)
end

################################################################################
#
#  Base Change
#
################################################################################

@doc raw"""
    base_change(K::Field, E::EllipticCurve) -> EllipticCurve

Return the base change of the elliptic curve $E$ over $K$ if coercion is
possible.
"""
function base_change(K::Field, E::EllipticCurve)
  a1, a2, a3, a4, a6 = a_invariants(E)
  return elliptic_curve(K, map(K, [a1, a2, a3, a4, a6])::Vector{elem_type(K)})
end

@doc raw"""
    base_change(f, E::EllipticCurve) -> EllipticCurve

Return the base change of the elliptic curve $E$ using the map $f$.
"""
function base_change(f, E::EllipticCurve)
  a1, a2, a3, a4, a6 = a_invariants(E)
  return elliptic_curve(map(f, [a1, a2, a3, a4, a6]))
end

################################################################################
#
#  Equality of Models
#
################################################################################

@doc raw"""
    ==(E::EllipticCurve, F::EllipticCurve) -> Bool

Return true if $E$ and $F$ are given by the same model over the same field.
"""
function ==(E::EllipticCurve, F::EllipticCurve)
  return a_invariants(E) == a_invariants(F) && base_field(E) == base_field(F)
end

################################################################################
#
#  Elementary invariants
#
################################################################################

@doc raw"""
    a_invariants(E::EllipticCurve{T}) -> Tuple{T, T, T, T, T}

Return the Weierstrass coefficients of $E$ as a tuple $(a_1, a_2, a_3, a_4, a_6)$
such that $E$ is given by $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$.
"""
function a_invariants(E::EllipticCurve)
  return E.a_invariants
end

@doc raw"""
    coefficients(E::EllipticCurve{T}) -> Tuple{T, T, T, T, T}

Return the Weierstrass coefficients of $E$ as a tuple (a1, a2, a3, a4, a6)
such that $E$ is given by y^2 + a1xy + a3y = x^3 + a2x^2 + a4x + a6.
"""
coefficients(E::EllipticCurve) = a_invariants(E)

@doc raw"""
    b_invariants(E::EllipticCurve{T}) -> Tuple{T, T, T, T}

Return the b-invariants of $E$ as a tuple $(b_2, b_4, b_6, b_8)$.
"""
function b_invariants(E::EllipticCurve)
  if isdefined(E, :b_invariants)
    return E.b_invariants
  else
    a1, a2, a3, a4, a6 = a_invariants(E)

    b2 = a1^2 + 4*a2
    b4 = a1*a3 + 2*a4
    b6 = a3^2 + 4*a6
    b8 = a1^2*a6 - a1*a3*a4 + 4*a2*a6 + a2*a3^2 - a4^2
    E.b_invariants = b2, b4, b6, b8
    return b2, b4, b6, b8
  end
end

@doc raw"""
    c_invariants(E::EllipticCurve{T}) -> Tuple{T, T}

Return the c-invariants of $E as a tuple $(c_4, c_6)$.
"""
function c_invariants(E::EllipticCurve)
  if isdefined(E, :c_invariants)
    return E.c_invariants
  else
    b2,b4,b6,b8 = b_invariants(E)
    c4 = b2^2 - 24*b4
    c6 = -b2^3 + 36*b2*b4 - 216*b6
    E.c_invariants = c4, c6
    return  c4, c6
  end
end


################################################################################
#
#  Discriminant
#
################################################################################

@doc raw"""
    discriminant(E::EllipticCurve) -> FieldElem

Return the discriminant of $E$.
"""
function discriminant(E::EllipticCurve{T}) where T
  if isdefined(E, :disc)
    return E.disc
  end
  if is_short_weierstrass_model(E)
    _, _, _, a4, a6 = a_invariants(E)
    d = -16*(4*a4^3 + 27*a6^2)
    E.disc = d
    return d::T
  else
    b2, b4, b6, b8 = b_invariants(E)
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
    j_invariant(E::EllipticCurve) -> FieldElem

Compute the j-invariant of $E$.
"""
function j_invariant(E::EllipticCurve{T}) where T
  if isdefined(E, :j)
    return E.j
  end

  if E.short == true
    R = base_field(E)
    a1, a2, a3, a4, a6 = a_invariants(E)
    j = divexact(-1728*(4*a4)^3,discriminant(E))
    E.j = j
    return j::T
  else
    c4, c6 = c_invariants(E)
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
    equation([R::MPolyRing,] E::EllipticCurve) -> MPolyRingElem

Return the equation defining the elliptic curve $E$ as a bivariate polynomial.
If the polynomial ring $R$ is specified, it must by a bivariate polynomial
ring.

# Examples

```jldoctest
julia> E = elliptic_curve(QQ, [1, 2, 3, 4, 5]);

julia> equation(E)
-x^3 - 2*x^2 + x*y - 4*x + y^2 + 3*y - 5
```
"""
function equation(E::EllipticCurve)
  K = base_field(E)
  Kxy,(x,y) = polynomial_ring(K, ["x","y"])
  return equation(Kxy, E)
end

function equation(Kxy::MPolyRing, E::EllipticCurve)
  K = base_field(E)
  @req base_ring(Kxy) === K "Base field of elliptic curve and polynomial ring must coincide"
  x, y = gens(Kxy)
  a1, a2, a3, a4, a6 = a_invariants(E)
  return y^2 + a1*x*y + a3*y - (x^3 + a2*x^2 + a4*x + a6)
end

@doc raw"""
    hyperelliptic_polynomials([R::PolyRing,] E::EllipticCurve) -> PolyRingElem, PolyRingElem

Return univariate polynomials $f, h$ such that $E$ is given by $y^2 + h*y = f$.

# Examples

```jldoctest
julia> E = elliptic_curve(QQ, [1, 2, 3, 4, 5]);

julia> hyperelliptic_polynomials(E)
(x^3 + 2*x^2 + 4*x + 5, x + 3)
```
"""
function hyperelliptic_polynomials(E::EllipticCurve)
  K = base_field(E)
  Kx, x = polynomial_ring(K,"x")
  return hyperelliptic_polynomials(Kx, E)
end

function hyperelliptic_polynomials(Kx::PolyRing, E::EllipticCurve)
  x = gen(Kx)
  @req base_ring(Kx) === base_field(E) "Base field of elliptic curve and polynomial ring must coincide"
  a1, a2, a3, a4, a6 = a_invariants(E)
  return x^3 + a2*x^2 + a4*x + a6, a1*x + a3
end

################################################################################
#
#  Points on Elliptic Curves
#
################################################################################

@doc raw"""
    (E::EllipticCurve)(coords::Vector; check::Bool = true)

Return the point $P$ of $E$ with coordinates specified by `coords`, which can
be either affine coordinates (`length(coords) == 2`) or projective coordinates
(`length(coords) == 3`).

Per default, it is checked whether the point lies on $E$. This can be disabled
by setting `check = false`.

# Examples

```jldoctest
julia> E = elliptic_curve(QQ, [1, 2]);

julia> E([1, -2])
Point  (1 : -2 : 1)  of Elliptic curve with equation
y^2 = x^3 + x + 2

julia> E([2, -4, 2])
Point  (1 : -2 : 1)  of Elliptic curve with equation
y^2 = x^3 + x + 2
```
"""
function (E::EllipticCurve{T})(coords::Vector{S}; check::Bool = true) where {S, T}
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
    return EllipticCurvePoint{T}(E, coords, check)
  else
    return EllipticCurvePoint{T}(E, map(base_field(E), coords)::Vector{T}, check)
  end
end

################################################################################
#
#  Parent
#
################################################################################

@doc raw"""
    parent(P::EllipticCurvePoint) -> EllipticCurve

Return the elliptic curve on which $P$ lies.

# Examples

```jldoctest
julia> E = elliptic_curve(QQ, [1, 2]);

julia> P = E([1, -2]);

julia> E == parent(P)
true
```
"""
function parent(P::EllipticCurvePoint)
  return P.parent
end

################################################################################
#
#  Point at infinity
#
################################################################################

@doc raw"""
    infinity(E::EllipticCurve) -> EllipticCurvePoint

Return the point at infinity with project coordinates $[0 : 1 : 0]$.
"""
function infinity(E::EllipticCurve{T}) where T
  infi = EllipticCurvePoint{T}(E)
  return infi
end

function points_with_x_coordinate(E::EllipticCurve{T}, x) where T
  R = base_field(E)
  x = R(x)
  a1, a2, a3, a4, a6 = a_invariants(E)
  Ry, y = polynomial_ring(R,"y")
  f = y^2 +a1*x*y + a3*y - x^3 - a2*x^2 - a4*x - a6
  ys = roots(f)
  pts = elem_type(E)[]
   for yi in ys
     push!(pts, E([x, yi]))
   end
  return pts
end


@doc raw"""
    is_finite(P::EllipticCurvePoint) -> Bool

Return true if P is not the point at infinity.
"""
function is_finite(P::EllipticCurvePoint)
  return !P.is_infinite
end

@doc raw"""
    is_infinite(P::EllipticCurvePoint) -> Bool

Return true if P is the point at infinity.
"""
function is_infinite(P::EllipticCurvePoint)
  return P.is_infinite
end


################################################################################
#
#  Test for inclusion
#
################################################################################

@doc raw"""
    is_on_curve(E::EllipticCurve, coords::Vector) -> Bool

Return true if `coords` defines a point on $E$ and false otherwise. The array
`coords` must have length 2.

# Examples

```jldoctest
julia> E = elliptic_curve(QQ, [1, 2]);

julia> is_on_curve(E, [1, -2])
true

julia> is_on_curve(E, [1, -1])
false
```
"""
function is_on_curve(E::EllipticCurve, coords::Vector)
  length(coords) != 2 && error("Array must be of length 2")
  a1, a2, a3, a4, a6 = a_invariants(E)
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
#  Element type
#
################################################################################

function elem_type(::Type{EllipticCurve{T}}) where T
  return EllipticCurvePoint{T}
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, E::EllipticCurve)
  print(io, "Elliptic curve with equation\n")
  a1, a2, a3, a4, a6 = a_invariants(E)
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

function show(io::IO, P::EllipticCurvePoint)
  print(io, "Point  ($(P[1]) : $(P[2]) : $(P[3]))  of $(P.parent)")
end


################################################################################
#
#  Addition of Points
#
################################################################################

# washington p. 14, cohen p. 270
@doc raw"""
    +(P::EllipticCurvePoint, Q::EllipticCurvePoint) -> EllipticCurvePoint

Add two points on an elliptic curve.

# Examples

```jldoctest
julia> E = elliptic_curve(QQ, [1, 2]);

julia> P = E([1, -2]);

julia> P + P
Point  (-1 : 0 : 1)  of Elliptic curve with equation
y^2 = x^3 + x + 2
```
"""
function +(P::EllipticCurvePoint{T}, Q::EllipticCurvePoint{T}) where T
  parent(P) != parent(Q) && error("Points must live on the same curve")

  # Is P = infinity or Q = infinity?
  if P.is_infinite
      return Q
  elseif Q.is_infinite
      return P
  end

  E = P.parent

  # Distinguish between long and short form
  if E.short
    if P[1] != Q[1]
        m = divexact(Q[2] - P[2], Q[1] - P[1])
        x = m^2 - P[1] - Q[1]
        y = m * (P[1] - x) - P[2]
    elseif P[2] != Q[2]
        return infinity(E)
    elseif P[2] != 0
        _, _, _, a4 = a_invariants(E)
        m = divexact(3*(P[1])^2 + a4, 2*P[2])
        x = m^2 - 2*P[1]
        y = m* (P[1] - x) - P[2]
    else
        return infinity(E)
    end

    Erg = E([x, y], check = false)

  else
  a1, a2, a3, a4, a6 = a_invariants(E)

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

#@doc raw"""
#    -(P::EllipticCurvePoint, Q::EllipticCurvePoint) -> EllipticCurvePoint
#
#Subtract two points on an elliptic curve.
#"""
function -(P::EllipticCurvePoint{T}, Q::EllipticCurvePoint{T}) where T
  return P + (-Q)
end

################################################################################
#
#  Inverse
#
################################################################################

#@doc raw"""
#    -(P::EllipticCurvePoint) -> EllipticCurvePoint
#
#Compute the inverse of the point $P$ on an elliptic curve.
#"""
function -(P::EllipticCurvePoint)
  E = P.parent

  if !is_finite(P)
    return infinity(E)
  end

  if E.short == true
    Q = E([P[1], -P[2]], check = false)
  else
    a1,_, a3 = a_invariants(E)
    Q = E([P[1], -a1*P[1] - a3 - P[2]], check = false)
  end

  return Q
end

#@doc raw"""
#    ==(P::EllipticCurvePoint, Q::EllipticCurvePoint) -> Bool
#
#Return true if $P$ and $Q$ are equal and live over the same elliptic curve
#$E$.
#"""
function ==(P::EllipticCurvePoint{T}, Q::EllipticCurvePoint{T}) where T
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
    *(n::Int, P::EllipticCurvePoint) -> EllipticCurvePoint

Compute the point $nP$.
"""
function *(n::S, P::EllipticCurvePoint) where S<:Union{Integer, ZZRingElem}
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
function multiplication_by_m_numerator(E::EllipticCurve, m::S, x = polynomial_ring(base_field(E),"x", cached = false)[2]) where S<:Union{Integer, ZZRingElem}
  p = characteristic(base_field(E))
  if p == 2
    #See Blake, Seroussi, Smart - Elliptic Curves in Cryptography III.4.2
    psi_mmin = division_polynomial(E, m-1, x)(1)
    psi_m = division_polynomial(E, m, x)(1)
    psi_mplus = division_polynomial(E, m+1, x)(1)
    return x*psi_m^2 + (psi_mmin*psi_mplus)
  end

  b2, b4, b6, b8 = b_invariants(E)
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
function multiplication_by_m_denominator(E::EllipticCurve, m::S, x = polynomial_ring(base_field(E),"x")[2]) where S<:Union{Integer, ZZRingElem}
  p = characteristic(base_field(E))
  if p == 2
    #See Blake, Seroussi, Smart - Elliptic Curves in Cryptography III.4.2
    psi_m = division_polynomial(E, m, x)(1)
    return psi_m^2
  end

  b2, b4, b6, b8 = b_invariants(E)
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
function multiplication_by_m_y_coord(E::EllipticCurve, m::S, x = polynomial_ring(base_field(E),"x")[2], y = polynomial_ring(parent(x),"y")[2]) where S<:Union{Integer, ZZRingElem}

  Kxy = parent(y)


  a1, a2, a3, a4 = a_invariants(E)
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

  b2, b4, b6, b8 = b_invariants(E)
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
    division_points(P::EllipticCurvePoint, m::Int) -> EllipticCurvePoint

Compute the set of points $Q$ defined over the base field such that $mQ = P$.
Returns the empty list if no such points exist.

# Examples

```jldoctest
julia> E = elliptic_curve(QQ, [1, 2]);

julia> division_points(infinity(E), 2)
2-element Vector{EllipticCurvePoint{QQFieldElem}}:
 Point  (0 : 1 : 0)  of Elliptic curve with equation
y^2 = x^3 + x + 2
 Point  (-1 : 0 : 1)  of Elliptic curve with equation
y^2 = x^3 + x + 2
```
"""
function division_points(P::EllipticCurvePoint, m::S) where S<:Union{Integer, ZZRingElem}
  if m == 0
    return typeof(P)[]
  end

  if m == 1
    return [P]
  end

  if m < 0
    m = -m
    P = -P
  end

  divpoints = typeof(P)[]

  E = parent(P)
  nP = -P
  twotors = (P == nP)
  _, x = polynomial_ring(base_field(E), cached = false)

  if is_infinite(P)
    push!(divpoints, P)
    g = division_polynomial_univariate(E, m, x)[1]
  else
    g = multiplication_by_m_numerator(E, m, x) - P[1]*multiplication_by_m_denominator(E, m, x)
    if twotors
      if mod(m, 2) == 0
        g = sqrt(g)
      else
        g0 = x - P[1]
        g = numerator(g//g0)
        g = sqrt(g)
        g = g0*g
      end
    end
  end
  for a in roots(g)
    a1, a2, a3, a4, a6 = a_invariants(E)
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
    //(P::EllipticCurvePoint, n::Int) -> EllipticCurvePoint

Return a point $Q$ such that $nQ = P$.
"""
function //(P::EllipticCurvePoint, n ::S) where S<:Union{Integer, ZZRingElem}
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

################################################################################
#
#  Hash
#
################################################################################

function Base.hash(P::EllipticCurvePoint, h::UInt)
  if is_infinite(P)
    return xor(h, UInt(0x8e54c9525d4f3979))
  else
    return xor(hash(P.coordx, h), hash(P.coordy, h))
  end
end
