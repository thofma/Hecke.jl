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

  function HypellCrv{T}(f::PolyRingElem{T}, h::PolyRingElem{T}, check::Bool = true) where {T}
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
      #TODO: Check what d is
      d = zero(R)
    else
      d = 2^(4*g)*discriminant(f + divexact(h^2,4))
    end
    if d != 0 || check == false

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
    hyperelliptic_curve(f::PolyRingElem, g::PolyRingElem; check::Bool = true) -> HypellCrv

Return the hyperelliptic curve $y^2 + h(x)y = f(x)$. The polynomial $f$
must be monic of degree 2g + 1 > 3 or of degree 2g + 2 > 4 and the
polynomial h must be of degree < g + 2. Here g will be the genus of the curve.
"""
function hyperelliptic_curve(f::PolyRingElem{T}, h::PolyRingElem{T}; check::Bool = true) where T <: FieldElem
  @req is_monic(f) "Polynomial must be monic"
  @req degree(f) >= 3 "Polynomial must be of degree bigger than 3"

  return HypellCrv{T}(f, h, check)
end

@doc raw"""
    hyperelliptic_curve(f::PolyRingElem; check::Bool = true) -> HypellCrv

Return the hyperelliptic curve $y^2 = f(x)$. The polynomial $f$ must be monic of
degree larger than 3.
"""
function hyperelliptic_curve(f::PolyRingElem{T}; check::Bool = true) where T <: FieldElem
  @req is_monic(f) "Polynomial must be monic"
  @req degree(f) >= 3 "Polynomial must be of degree greater or equal to 3"
  R = parent(f)
  return HypellCrv{T}(f, zero(R), check)
end

@doc raw"""
    hyperelliptic_curve(L::Vector{FieldElem}; check::Bool = true) -> HypellCrv

Return the hyperelliptic curve $y^2 = f(x)$ where f = a0*x^n + ... + an
where L = [a0,...,an]
"""
function hyperelliptic_curve(L::Vector{T}; check::Bool = true) where T <: FieldElem
  @req L[1] == 1 "Polynomial must be monic"
  @req length(L) >= 4 "Polynomial must be of degree greater or equal to 3"
  K = parent(L[1])
  Kx, x = polynomial_ring(K)

  return HypellCrv{T}(Kx(reverse(L)), check)
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
  return hyperelliptic_curve(fnew, hnew)
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

function Base.hash(C::HypellCrv, h::UInt)
  h = hash(base_field(C), h)
  h = hash(hyperelliptic_polynomials(C), h)
  return h
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
  return (C.f, C.h)::Tuple{poly_type(T), poly_type(T)}
end

@doc raw"""
    is_integral_model(C::HyperellCrv{T}) -> Bool where T<:Union{QQFieldElem, AbsSimpleNumFieldElem}

Given a hyperelliptic curve $C$ over QQ or a number field $K$, return
true if $C$ is an integral model of $C$.
"""
function is_integral_model(C::HypellCrv{T}) where T<:Union{QQFieldElem, AbsSimpleNumFieldElem}
  f, h = hyperelliptic_polynomials(C)
  coeffs = vcat(collect(coefficients(f)), collect(coefficients(h)))
  coeffs = map(denominator, coeffs)
  mu = lcm(coeffs)
  if mu == 1
    return true
  end

  return false
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
  x = coords[1]
  y = coords[2]
  z = coords[3]

  K = parent(x)

  if all(i -> i == zero(K), [x,y,z])
    error("(0 : 0 : 0) is not a point in projective space.")
  end
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

Return true if $P$ and $Q$ are equal and live over the same hyperelliptic curve
$E$.
"""
function ==(P::HypellCrvPt{T}, Q::HypellCrvPt{T}) where T
  if parent(P) != parent(Q)
    return false
  end
  # Compare coordinates
  if P[1] == Q[1] && P[2] == Q[2] && P[3] == Q[3]
    return true
  else
    return false
  end
end

function Base.hash(P::HypellCrvPt, h::UInt)
  h = hash(parent(P), h)
  h = hash(P[1], h)
  h = hash(P[2], h)
  h = hash(P[3], h)
  return h
end

@doc raw"""
    reduce_binary_form(f::PolyRingElem) -> PolyRingElem

Given a binary form over QQ, compute the binary form with
minimal Julia covariant.
"""
#Following the preprint "Efficient reduction of binary forms"
# by Michael Stoll.
function reduce_binary_form(f::PolyRingElem)
  R = base_ring(f)
  Rx = parent(f)
  coeff_f = coefficients(f)
  Rxz, (x, z) = polynomial_ring(R, ["x", "z"])
  n = degree(f)
  g = div(degree(f) - 1, 2)
  f_hom = sum([coeff_f[i]*x^i*z^(2*g + 2 - i) for i in (0:n)];init = zero(Rxz))
  f, gamma = reduce_binary_form(f_hom)
  return evaluate(f, [gen(Rx), one(Rx)])
end

@doc raw"""
    reduce_binary_form(f::MPolyRingElem) -> MPolyRingElem

Given a binary form over QQ that is stable (i.e. f is not divisible by a
linear form of degree m with 2m >= deg(f)), compute the binary form with
minimal Julia covariant.
"""
function reduce_binary_form(f::MPolyRingElem{T}) where T
  #Check stability
  n = total_degree(f)
  ms = values(factor(f).fac)
  for m in ms
    if 2*m >= n
      error("Binary form is not stable.")
    end
  end

  gamma = identity_matrix(ZZ,2)
  CC = AcbField(200)
  Rxz = parent(f)
  x, z = gens(Rxz)
  Cs, s = polynomial_ring(CC, "s")
  Qt, t = polynomial_ring(QQ, "t")
  while true
    f_fin = evaluate(f, [s, Cs(1)])
    f_inf = evaluate(f, [Qt(1), t])
    S2 = roots(f_fin;initial_prec = 200)
    S_inf = valuation(f_inf, t)

    # repos(map(x-> x - a, S2), S_inf) returns whether Re(zF) >= a
    # The goal is to get -1/2 <= Re(z(F)) <= 1/2
    # We first find u and l such that l- 1/2 <= Re(z(F)) <= u - 1/2.
    S_new = map(x-> CC(x - 1/2), S2)
    if repos(S_new, S_inf)
      k = 0
      l = 1
      u = 2
      # Note that in Stoll's preprint u + 1/2 is written, but to test
      # when the value is no longer >= u - 1/2, we need u - 1/2 instead.
      while test_u(u, S2, S_inf)
        k += 1
        l = u
        u = u + 2^k
      end
    else
      if repos(map(x-> x + CC(1/2), S2), S_inf)
        return f, gamma
      end
      k = 0
      u = 0
      l = -1
      # Note that in Stoll's preprint l + 1/2 is written, but to test
      # when the value is >= l - 1/2, we need l - 1/2 instead.
      while !test_u(l, S2, S_inf)
        k += 1
        u = l
        l = l - 2^k
      end
    end

    while u - l > 1
      m = floor(Int, (l+u)//2)
      # Note that in Stoll's preprint m + 1/2 is written, but to test
      # when the value is >= m - 1/2, we need m - 1/2 instead.
      if repos(map(x-> x - CC(m - 1/2), S2), S_inf)
        l = m
      else
        u = m
      end
    end

    f = Rxz(evaluate(f, [x + l*z, z]))
    gamma = gamma * matrix(ZZ, [[1,l],[0,1]])
    f_fin = evaluate(f, [s, Cs(1)])
    S2 = roots(f_fin;initial_prec = 200)

    # Instead of mapping all roots to (a+1)/(a-1) by doing
    # repos(map(x-> (x+1)/(x-1), S2), S_inf) we compute f(x+z, x-z)
    # to also deal with the case where a = 1 (which gets mapped to infinity).

    g = evaluate(f, [x + z, x - z])
    g_fin = evaluate(g, [s, Cs(1)])
    g_inf = evaluate(g, [Qt(1), t])

    S2_flipped = roots(g_fin;initial_prec = 200)
    S_inf_flipped = valuation(g_inf, t)

    #Check |z(F)|> 1
    if repos(S2_flipped, S_inf_flipped)
      return f, gamma
    end
    f = Rxz(evaluate(f, [-z,x]))
    gamma = gamma * matrix(ZZ, [[0,-1],[1,0]])
  end
end


function test_u(u, S2, S_inf)
  CC = parent(S2[1])
  S_new = map(x-> x - CC(u - 1/2), S2)
  return repos(S_new, S_inf)
end

function repos(S2::Vector{AcbFieldElem}, S_inf::Int)
  CC = parent(S2[1])
  RR = ArbField(precision(CC))
  #Precision equality 0?
  n = length(S2) + S_inf
  m = n - length(S2)
  S = S2 |> filter(x -> x != 0)
  m = m - (length(S2) - length(S))


  S_abs = map(x-> RR(abs(x)), S)

  u = log(minimum(S_abs)^2)/2
  v = log(maximum(S_abs)^2)/2

  function h(eta::ArbFieldElem)
    result = CC(0)
    for a in S_abs
      result += log(a*exp(-eta) + exp(eta)/a)
    end
    result -= m*eta
    return result
  end

  function dh(eta::ArbFieldElem)
    result = RR(0)
    for a in S_abs
      result += (exp(2*eta) - a^2)/(exp(2*eta) + a^2)
    end
    result -= m
    return result
  end

  function ddh(eta::ArbFieldElem)
    result = RR(0)
    for a in S_abs
      result += 1/(cosh(eta) - log(a))^2
    end
    return result
  end

  #Newton iteration with bisection as fallback
  eta0 = (u+v)/2
  I = RR(0)
  add_error!(I, RR(10^-20))
  while (!contains(I, dh(eta0)))

    if dh(eta0) > 0
      v = eta0
    else
      u = eta0
    end

    etatest = eta0 - dh(eta0)/ddh(eta0)

    #Decide whether to use Newton iteration or bisection.
    #Not sure what the optimal way to balance this is.
    if abs(dh(etatest)) / abs(dh(eta0)) < RR(0.5)
      eta0 = etatest
    else
      if dh(eta0) > 0
        eta0 = (eta0+u)/2
      else
        eta0 = (eta0+v)/2
      end
    end
  end
  delta = sum(map(x -> real(x)/(abs(x)^2 + exp(2*eta0)), S))
  if delta >= 0
    return true
  else
    return false
  end
end
