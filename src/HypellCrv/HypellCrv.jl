################################################################################
#
#          HypellCrv/HypellCrv.jl : Hyperelliptic curves over general fields
#
# (C) 2022 Jeroen Hanselman
#
################################################################################

################################################################################
#
#  Types
#
################################################################################

mutable struct HypellCrv{T}
  base_field::Ring
  f::PolyRingElem{T}
  h::PolyRingElem{T}
  f_hom::MPolyRingElem{T}
  h_hom::MPolyRingElem{T}
  g::Int
  disc::T

  function HypellCrv{T}(f::PolyRingElem, h::PolyRingElem, check::Bool = true) where {T}
    n = degree(f)
    m = degree(h)
    g = div(degree(f) - 1, 2)
    if g < 0
      error("Curve has to be of positive genus")
    end
    if m > g + 1
      error("h has to be of degree smaller than g + 2.")
    end
    R = base_ring(f)

    if characteristic(R) == 2
      check = false
    end

    d = 2^(4*g)*discriminant(f + divexact(h^2,4))

    if d != 0 && check
      C = new{T}()

      C.f = f
      C.h = h
      C.g = g
      C.disc = d
      C.base_field = R

      coeff_f = coefficients(f)
      coeff_h = coefficients(h)

      Rxz, (x, z) = polynomial_ring(R, ["x", "z"])
      f_hom = sum([coeff_f[i]*x^i*z^(2*g + 2 - i) for i in (0:n)];init = zero(Rxz))
      h_hom = sum([coeff_h[i]*x^i*z^(g + 1 - i) for i in (0:m)];init = zero(Rxz))
      C.f_hom = f_hom
      C.h_hom = h_hom

    else
      error("Discriminant is zero")
    end
    return C
  end
end

mutable struct HypellCrvPt{T}
  coordx::T
  coordy::T
  coordz::T
  is_infinite::Bool
  parent::HypellCrv{T}

  function HypellCrvPt{T}(C::HypellCrv{T}, coords::Vector{T}, check::Bool = true) where {T}
    g = genus(C)
    K = base_field(C)
    P = new{T}()
    if check
      if !is_on_curve(C, coords)
        error("Point is not on the curve")
      end
    end

    P.parent = C
    if coords[3] == 0
      P.coordx = coords[1]
      P.coordy = coords[2]
      P.coordz = coords[3]
      P.is_infinite = true
    else
      P.is_infinite = false

      #Don't have numerators, denominators and gcd over finite fields
      if T <: FinFieldElem

        scalar = inv(coords[3])

        P.coordx = coords[1]*scalar
        P.coordy = coords[2]*scalar^(g+1)
        P.coordz = coords[3]*scalar
      else

        #Eliminate denominators
        x = numerator(coords[1]) * denominator(coords[3])
        y = coords[2] * (denominator(coords[3]) * denominator(coords[1]))^(g + 1)
        z = numerator(coords[3]) * denominator(coords[1])

        c = gcd(x, z)

        #Eliminate gcd
        if c!= 1
          x = divexact(x, c)
          y = divexact(y, c^(g+1))
          z = divexact(z, c)
        end

        P.coordx = K(x)
        P.coordy = K(y)
        P.coordz = K(z)
      end
    end
    return P
  end
end

function Base.getindex(P::HypellCrvPt, i::Int)
  @req 1 <= i <= 3 "Index must be 1, 2 or 3"

  if i == 1
    return P.coordx
  elseif i == 2
    return P.coordy
  elseif i == 3
    return P.coordz
  end
end

################################################################################
#
#  Constructors for Hyperelliptic Curve
#
################################################################################

@doc raw"""
    HyperellipticCurve(f::PolyRingElem, g::PolyRingElem; check::Bool = true) -> HypellCrv

Return the hyperelliptic curve $y^2 + h(x)y = f(x)$. The polynomial $f$
must be monic of degree 2g + 1 > 3 or of degree 2g + 2 > 4 and the
polynomial h must be of degree < g + 2. Here g will be the genus of the curve.
"""
function HyperellipticCurve(f::PolyRingElem{T}, h::PolyRingElem{T}; check::Bool = true) where T <: FieldElem
  @req is_monic(f) "Polynomial must be monic"
  @req degree(f) >= 3 "Polynomial must be of degree 3"

  return HypellCrv{T}(f, h, check)
end

@doc raw"""
    HyperellipticCurve(f::PolyRingElem; check::Bool = true) -> HypellCrv

Return the hyperelliptic curve $y^2 = f(x)$. The polynomial $f$ must be monic of
degree larger than 3.
"""
function HyperellipticCurve(f::PolyRingElem{T}; check::Bool = true) where T <: FieldElem
  @req is_monic(f) "Polynomial must be monic"
  @req degree(f) >= 3 "Polynomial must be of degree 3"
  R = parent(f)
  return HypellCrv{T}(f, zero(R), check)
end


################################################################################
#
#  Field access
#
################################################################################

@doc raw"""
    base_field(C::HypellCrv) -> Field

Return the base field over which `C` is defined.
"""
function base_field(C::HypellCrv{T}) where T
  return C.base_field::parent_type(T)
end

################################################################################
#
#  Base Change
#
################################################################################

@doc raw"""
    base_change(K::Field, C::HypellCrv) -> EllipticCurve

Return the base change of the hyperelliptic curve $C$ over K if coercion is
possible.
"""
function base_change(K::Field, C::HypellCrv)
  f, h = hyperelliptic_polynomials(C)
  fnew = change_coefficient_ring(K, f)
  hnew = change_coefficient_ring(K, h)
  return HyperellipticCurve(fnew, hnew)
end


################################################################################
#
#  Equality of Models
#
################################################################################

@doc raw"""
    ==(C::HypellCrv, D::HypellCrv) -> Bool

Return true if $C$ and $D$ are given by the same model over the same field.
"""
function ==(C::HypellCrv{T}, D::HypellCrv{T}) where T
  return hyperelliptic_polynomials(C) == hyperelliptic_polynomials(D) && base_field(C) == base_field(D)
end


################################################################################
#
#  Genus
#
################################################################################

@doc raw"""
    genus(C::HypellCrv{T}) -> T

Return the of $C$.
"""
function genus(C::HypellCrv{T}) where T
  return C.g
end



################################################################################
#
#  Discriminant
#
################################################################################

@doc raw"""
    discriminant(C::HypellCrv{T}) -> T

Compute the discriminant of $C$.
"""
function discriminant(C::HypellCrv{T}) where T
  if isdefined(C, :disc)
    return C.disc
  end
  K = base_field(C)
  if characteristic(K) != 2
    f, h = hyperelliptic_polynomials(C)
    d = 2^(4*g)*discriminant(f(x) + 1//4*h(x)^2)
    C.disc = d
    return d::T
  else
    #Need to use Witt vectors for this
    error("Cannot compute discriminant of hyperelliptic curve in characteristic 2.")
  end
end


################################################################################
#
#  Equations
#
################################################################################

@doc raw"""
    equation(C::HypellCrv) -> Poly

Return the equation defining the hyperelliptic curve C.
"""
function equation(C::HypellCrv)
  K = base_field(C)
  Kxy,(x,y) = polynomial_ring(K, ["x","y"])

  f, h = hyperelliptic_polynomials(C)

  return y^2 + h(x)*y - f(x)
end

@doc raw"""
    homogeneous_equation(C::HypellCrv) -> Poly

Return the homogeneous equation defining the hyperelliptic curve C.
"""
function homogeneous_equation(C::HypellCrv)
  K = base_field(C)
  Kxyz, (x, y, z) = polynomial_ring(K, ["x", "y", "z"])

  f = C.f_hom
  h = C.h_hom

  return y^2 + h(x, z)*y - f(x, z)
end



@doc raw"""
    hyperelliptic_polynomials(C::HypellCrv) -> Poly, Poly

Return f, h such that C is given by y^2 + h*y = f
"""
function hyperelliptic_polynomials(C::HypellCrv{T}) where T
  return (C.f, C.h)::Tuple{dense_poly_type(T), dense_poly_type(T)}
end


################################################################################
#
#  Points on Hyperelliptic Curves
#
################################################################################

function (C::HypellCrv{T})(coords::Vector{S}; check::Bool = true) where {S, T}
  if !(2 <= length(coords) <= 3)
    error("Points need to be given in either affine coordinates (x, y) or projective coordinates (x, y, z)")
  end

  if length(coords) == 2
    push!(coords, 1)
  end
  if S === T
    parent(coords[1]) != base_field(C) &&
        error("Objects must be defined over same field")
    return HypellCrvPt{T}(C, coords, check)
  else
    return HypellCrvPt{T}(C, map(base_field(C), coords)::Vector{T}, check)
  end
end

################################################################################
#
#  Parent
#
################################################################################

function parent(P::HypellCrvPt)
  return P.parent
end

################################################################################
#
#  Point at infinity
#
################################################################################

@doc raw"""
    points_at_infinity(C::HypellCrv) -> HypellCrvPt

Return the points at infinity.
"""
function points_at_infinity(C::HypellCrv{T}) where T
  K = base_field(C)
  equ = homogeneous_equation(C)

  infi = HypellCrvPt{T}[]

  if equ(one(K),zero(K), zero(K)) == 0
    push!(infi, C([one(K),zero(K), zero(K)]))
  end

  if equ(one(K),one(K), zero(K)) == 0
    push!(infi, C([one(K),one(K), zero(K)]))
    if characteristic(K)!= 2
      push!(infi, C([one(K),- one(K), zero(K)]))
    end
  end

  return infi
end

function points_with_x_coordinate(C::HypellCrv{T}, x) where T<: FinFieldElem
  R = base_field(C)
  Ry, y = polynomial_ring(R,"y")
  equ = homogeneous_equation(C)
  f = equ(R(x), y, one(R))
  ys = roots(f)
  pts = []
   for yi in ys
     push!(pts, C([x, yi, one(R)]))
   end
  return pts
end

function points_with_x_coordinate(C::HypellCrv{T}, x) where T
  R = base_field(C)
  Ry, y = polynomial_ring(R,"y")
  equ = homogeneous_equation(C)
  f = equ(numerator(x), y, denominator(x))
  ys = roots(f)
  pts = []
   for yi in ys
     push!(pts, C([numerator(x), yi, denominator(x)]))
   end
  return pts
end


@doc raw"""
    is_finite(P::HypellCrvPt) -> Bool

Return true if P is not the point at infinity.
"""
function is_finite(P::HypellCrvPt)
  return !P.is_infinite
end

@doc raw"""
    is_infinite(P::HypellCrvPt) -> Bool

Return true if P is the point at infinity.
"""
function is_infinite(P::HypellCrvPt)
  return P.is_infinite
end


################################################################################
#
#  Test for inclusion
#
################################################################################

@doc raw"""
    is_on_curve(C::HypellCrv{T}, coords::Vector{T}) -> Bool

Return true if `coords` defines a point on $C$ and false otherwise. The array
`coords` must have length 2.
"""
function is_on_curve(C::HypellCrv{T}, coords::Vector{T}) where T
  length(coords) != 3 && error("Array must be of length 3")
  coords
  x = coords[1]
  y = coords[2]
  z = coords[3]

  equ = homogeneous_equation(C)
  equ(x, y, z)
  if equ(x, y, z) == 0
    return true
  else
    return false
  end
end

################################################################################
#
#  ElemType
#
################################################################################

function elem_type(::Type{HypellCrv{T}}) where T
  return HypellCrvPt{T}
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, C::HypellCrv)
  f, h = hyperelliptic_polynomials(C)
  #Swapped order of x and y to get nicer printing
  g = genus(C)
  if !is_zero(h)
    print(io, "Hyperelliptic curve of genus $(g) with equation\n y^2 + ($(h))*y = $(f)")
  else
    print(io, "Hyperelliptic curve of genus $(g) with equation\n y^2 = $(f)")
  end
end

function show(io::IO, P::HypellCrvPt)
   print(io, "Point  ($(P[1]) : $(P[2]) : $(P[3]))  of $(P.parent)")
end

@doc raw"""
    ==(P::EllipticCurvePoint, Q::EllipticCurvePoint) -> Bool

Return true if $P$ and $Q$ are equal and live over the same elliptic curve
$E$.
"""
function ==(P::HypellCrvPt{T}, Q::HypellCrvPt{T}) where T
 # Compare coordinates
  if P[1] == Q[1] && P[2] == Q[2] && P[3] == Q[3]
    return true
  else
    return false
  end
end
