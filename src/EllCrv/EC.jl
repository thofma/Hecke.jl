include("header.jl")

export EllipticCurve, is_on_curve, j, +, *, infinity, disc, inverse, compare_points, 
       ZXYAB, X, Y, A, B, division_polynomial, phi_polynomial, 
       Zx, Zxy, x, y, division_polynomialE, Psi_polynomial, psi_poly_field,
       torsion_points, torsion_divi, torsion_structure,
       get_short, get_short_finite_field, makeintegral, 
       order_via_legendre, elem_order_bsgs, order_via_bsgs, hasse_interval, random, t_mod_prime, order_via_schoof, order_best,
       laska_kraus_connell, mod_red, check_weak_bsd, 
       transform, minimal_residue, tates_algorithm_local, tates_algorithm_global, tidy_model,
       local_height_finite2, local_height_infinite, canonical_height, is_independent, real_period, 
       naive_height, points_with_bounded_height, torsion_points_via_height, independent_points_up_to



# Set up the data structures: 
# EllCrv, Elliptic Curve, EllCrvPt
type EllCrv{T}
  base_field::Ring
  short::Bool
  coeff::Array{T, 1}
  long_b::Array{T, 1}
  disc::T
  j::T

  torsion_points#::Array{EllCrvPt, 1}
  torsion_structure#Tuple{Array{Int, 1}, Array{EllCrvPt, 1}}

  function EllCrv(coeffs::Array{T, 1}, check::Bool = true)
    if length(coeffs) == 2
      if check
        d = 4*coeffs[1]^3 + 27*coeffs[2]^2
        if d != 0 
          E.new()
          E.short = true
          E.coeff = deepcopy(coeffs)
          #E.disc = d
        else 
          error("discriminant is zero")
        end
      else 
        E.new()
        E.short = true
        E.coeff = deepcopy(coeffs)
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
          E = new()
          E.coeff = deepcopy(coeffs)
          E.short = false
          E.long_b = [ b2, b4, b6, b8]
          E.disc = E
        else 
          error("discriminant is zero")
        end
      else
        E = new()
        E.short = false
        E.coeff = deepcopy(coeffs)
      end
    else
      error("Length of coefficient array must be 2 or 5")
    end
    return E
  end
end

type EllCrvPt{T}
  coordx::T
  coordy::T
  isinfinite::Bool
  parent::EllCrv{T}

  function EllCrvPt(E::EllCrv{T}, coords::Array{T, 1}, check::Bool = true)
    if length(coords) != 2
      error("Need two coordinates")
    end
    if check
      if is_on_curve(E, coords)
        P = new{T}(coords[1], coords[2], false, E)
        return P
      else
        error("Point is not on the curve")
      end
    else
      P = new{T}(coords[1], coords[2], false ,E)
      return P
    end
  end
end

function call{T}(E::EllCrv{T}, coords::Array{T, 1}, check::Bool = true)
  return EllCrvPt{T}(E, coords, check)
end

################################################################################
#
#  Implicit conversion in characterstic 0
#
################################################################################

function EllipticCurve{T}(x::Array{T, 1}, check::Bool = true)
  E = EllCrv{T}(x, check)
  return E
end

function EllipticCurve(x::Array{Int, 1}, check::Bool = true)
  return EllipticCurve(fmpq[ FlintQQ(z) for z in x], check)
end

function EllipticCurve(x::Array{fmpz, 1}, check::Bool = true)
  return EllipticCurve(fmpq[ FlintQQ(z) for z in x], check)
end

################################################################################
#
#  Field access
#
################################################################################

function base_field{T}(E::EllCrv{T})
  return E.base_field::parent_type(T)
end

function deepcopy(E::EllCrv)
    return EllipticCurve(E.coeff)
end

function get_bs{T}(E::EllCrv)
  return (long_b[1], long_b[2], long_b[3], long_b[4])
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, E::EllCrv)
  if E.short
    print(io, "Elliptic curve with equation y^2 = x^3 + $(E.coeff[1])*x + $(E.coeff[2])\n")
  else
    print(io, "Elliptic curve with equation y^2")
    if !iszero(E.coeff[1])
      print(io, " + $(E.coeff[1])*xy")
    end
    if !iszero(E.coeff[3])
      print(io, " + $(E.coeff[3])*y")
    end
    print(io, " = x^3")
    if !iszero(E.coeff[2])
      print(io, " + $(E.coeff[2])*x^2")
    end
    if !iszero(E.coeff[4])
      print(io, " + $(E.coeff[4])*x")
    end
    if !iszero(E.coeff[5])
      print(io, " + $(E.coeff[5])")
    end
    print(io, "\n")
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

doc"""
***
    infinity(E::EllCrv) -> EllCrvPt

> Creates the point at infinity.
"""
function infinity{T}(E::EllCrv{T})
  infi = EllCrvPt{T}(zero(base_field(E)), zero(base_field(E)), true, E)
  return infi
end


################################################################################
#
#  Test for inclusion
#
################################################################################

doc"""
***
    is_on_curve(E::EllCrv{T}, coords::Array{T, 1}) -> Bool

> Returns true if P = (coords[1], coords[2]) is on E and false otherwise
"""
function is_on_curve{T}(E::EllCrv{T}, coords::Array{T, 1})
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

doc"""
***
    disc(E::EllCrv{T}) -> T

> Computes the discriminant of $E$.
"""
function disc(E::EllCrv)
  if isdefined(E, :disc)
    return E.disc
  end
    
  if E.short == true
    # fall back to the formula for the long form    
    # this should be then in a more clever way
    R = base_field(E)
    F = EllipticCurve([R(0), R(0), R(0), E.coeff[1], E.coeff[2]])
    d = disc(F)
    E.disc = d
    return d
  else 
    a1 = E.coeff[1]
    a2 = E.coeff[2]
    a3 = E.coeff[3]
    a4 = E.coeff[4]
    a6 = E.coeff[5]
    
    (b2, b4, b6, b8) = get_b(E)
    
    d = -b2^2*b8 - 8*b4^3 - 27*b6^2 + 9*b2*b4*b6
    E.disc = d
    return d
  end
end

################################################################################
#
#  j-invariant
#
################################################################################

doc"""
***
    j(E::EllCrv{T}) -> T 
> Computes the j-invariant of $E$.
"""
# p. 46 Washington, p. 72 Cohen
function j(E::EllCrv)
  if isdefined(E, :j)
    return E.j
  end

  if E.short == true
    
    R = base_field(E)
    F = EllipticCurve([R(0), R(0), R(0), E.coeff[1], E.coeff[2]])
    j = j(F)
    E.j = j
    return j
  else
    a1 = E.coeff[1]
    a2 = E.coeff[2]
    a3 = E.coeff[3]
    a4 = E.coeff[4]
    a6 = E.coeff[5]

    (b2, b4, b6, b8) = get_b(E)
    #b2 = a1^2 + 4*a2
    #b4 = a1*a3 + 2*a4
    #b6 = a3^2 + 4*a6
    #b8 = a1^2*a6 - a1*a3*a4 + 4*a2*a6 + a2*a3^2 - a4^2

    c4 = b2^2 - 24*b4
    
    j = divexact(c4^3, disc(E))
    E.j = j
    return j
  end
end

################################################################################
#
#  Addition of Points
#
################################################################################

doc"""
***
    +(P::EllCrvPt, Q::EllCrvPt) -> EllCrvPt
> Adds two points on an elliptic curve.
> does not work in characteristic 2
"""
# washington p. 14, cohen p. 270
function +{T}(P::EllCrvPt{T}, Q::EllCrvPt{T})
  parent(P) != parent(Q) && error("Points must live on the same curve")

  char(base_Field(parent(P))) == 2 &&
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

    Erg = EllCrvPt{T}(x, y, false, E)
      
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
      
    Erg = EllCrvPt{T}(x, y, false, E)

  end
  return Erg
end

################################################################################
#
#  Inverse
#
################################################################################

doc"""
***
    inverse(P::EllCrvPt) -> EllCrvPt

> Computes the inverse of a point $P$ on an elliptic curve.
"""
function inverse(P::EllCrvPt)
  E = P.parent
  
  if E.short == true
    Q = EllCrvPt(P.coordx, -P.coordy, P.isinfinite, P.parent)
  else
    Q = EllCrvPt(P.coordx, -E.coeff[1]*P.coordx - E.coeff[3] - P.coordy,
                 P.isinfinite, P.parent)
  end
  
  return Q
end

doc"""
***
    ==(P::EllCrvPt, Q::EllCrvPt) -> Bool

> Returns true if $P$ and $Q$ are equal and live over the same elliptic curve
> $E$.
"""
function ==(P::EllCrvPt, Q::EllCrvPt)
  # Is one of the points the point at infinity?
  if P.isinfinite
    if Q.isinfinite
      return true
    else
      return false
    end
  end

  # Otherwise, compare coordinates
  if P.coordx != Q.coordx
    return false 
  elseif P.coordy != Q.coordy
    return false
  else 
    return true 
  end
end

################################################################################
#
#  Scalar multiplication
#
################################################################################

doc"""
****
    *(n::Int, P::EllCrvPt) -> EllCrvPt
> Computes the point $nP$.
"""
# algorithm 'integer times a point', [Washington, p. 18]
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
    B = inverse(B)
  end
    
  return B
end


###### DIVISION POLYNOMIALS ######
# division_polynomial, phi_polynomial
# division_polynomialE, replace_all_squares, replace_all_squares_modulo, Psi_polynomial
# psi_poly_field

# polynomial ring ZZ[X,Y,A,B]
global ZXYAB = PolynomialRing(PolynomialRing(PolynomialRing(PolynomialRing(ZZ, "X")[1], "Y")[1], "A")[1], "B")[1];

global B = gen(ZXYAB)
global A = ZXYAB(gen(parent(coeff(B, 0))))
global Y = ZXYAB(gen(parent(coeff(gen(parent(coeff(B, 0))), 0))))
global X = ZXYAB(gen(parent(coeff(gen(parent(coeff(gen(parent(coeff(B, 0))), 0))), 0))))

# computes the n-th division polynomial psi_n in ZZ[X,Y,A,B], p. 81
function division_polynomial(n::Int)

    if n == 0
        return zero(ZXYAB)
    elseif n == 1
        return one(ZXYAB)
    elseif n == 2
        return 2*Y     
    elseif n == 3
        return 3*X^4 + 6*A*X^2 + 12*B*X - A^2
    elseif n == 4
        return 4*Y*(X^6 + 5*A*X^4 + 20*B*X^3 - 5*A^2*X^2 - 4*A*B*X - 8*B^2 - A^3)
    elseif mod(n,2) == 0
        m = div(n,2)
        return divexact( (division_polynomial(m))*(division_polynomial(m+2)*division_polynomial(m-1)^2 - division_polynomial(m-2)*division_polynomial(m+1)^2), 2*Y)
    else m = div(n-1,2)
        return division_polynomial(m+2)*division_polynomial(m)^3 - division_polynomial(m-1)*division_polynomial(m+1)^3 
    end
end

# computes the n-th phi-polynomial phi_n, p. 81
function phi_polynomial(n::Int)
    return X*division_polynomial(n)^2 - division_polynomial(n+1)*division_polynomial(n-1)
end

# polynomial rings Zx = ZZ[x] and Zxy = ZZ[x,y]
global Zx = PolynomialRing(ZZ, "x")[1]
global Zxy = PolynomialRing(Zx, "y")[1]
global x = gen(Zx)
global y = gen(Zxy)

# computes the n-th division polynomial psi_n in ZZ[x,y] for a given elliptic curve E over ZZ
function division_polynomialE(E::EllCrv, n::Int)
    
    A = num(E.coeff[1])
    B = num(E.coeff[2])
    
    if n == 1
        return one(Zxy)
    elseif n == 2
        return 2*Zxy(y)
    elseif n == 3
        return 3*Zxy(x)^4 + 6*(A)*Zxy(x)^2 + 12*(B)*Zxy(x) - (A)^2
    elseif n == 4
        return 4*Zxy(y)*(Zxy(x)^6 + 5*(A)*Zxy(x)^4 + 20*(B)*Zxy(x)^3 - 5*(A)^2*Zxy(x)^2 - 4*(A)*(B)*Zxy(x) - 8*(B)^2 - (A)^3)
    elseif mod(n,2) == 0
        m = div(n,2)
        return divexact( (division_polynomialE(E,m))*(division_polynomialE(E,m+2)*division_polynomialE(E,m-1)^2 - division_polynomialE(E,m-2)*division_polynomialE(E,m+1)^2), 2*Zxy(y))
    else m = div(n-1,2)
        return division_polynomialE(E,m+2)*division_polynomialE(E,m)^3 - division_polynomialE(E,m-1)*division_polynomialE(E,m+1)^3 
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

# here is an example: f = Zxy(x)*y^2 + Zxy(x + 1)*y^4; EC.replace_all_squares(f, x^3)
# this should give x^7+x^6+x^4

# computes the n-th Psi-polynomial Psi_n in ZZ[x]
function Psi_polynomial(E::EllCrv, n::Int)

    if n < 2 
        error("Psi-polynomial not defined")
    end
    
    # g = y^2
    g = Zx(x)^3 + (num(E.coeff[1]))*Zx(x) + num(E.coeff[2])
    
    h = division_polynomialE(E, n)
    # make h into an element of ZZ[x]
    
    # in the even case, first divide by 2y and then replace y^2
    if mod(n,2) == 0
        f = divexact(h,2*Zxy(y))
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

###### DIVISORS AND INTEGER SOLUTIONS OF POLYNOMIAL EQUATIONS ######
# divisors, squaredivisors
# integersolutions, integer_zeros

################################################################################
#
#  Computing all divisors
#
################################################################################

doc"""
***
    Divisors(n::fmpz) -> Array{fmpz, 1}

> Computes the divisors of a given number $n$. It is assumed that $n$ is not
> zero.
"""
function divisors(n)
  n == 0 && error("The number must be nonzero")
  # special cases
  if (n == 1) || (n == -1)
    return fmpz[1,-1]
  end
  if (n == 0)
    return fmpz[]
  end
  
  if n < 0
    n = -n
  end

  d = isqrtrem(n) # d = (s,r) where s is sqrt(n) rounded down and r = n - s^2
  divi = Nemo.fmpz[]

  i = d[1]+1
  while i <= n
    if mod(n,i) == 0
      # add i and n/i to list of divisors (and their negative)
      push!(divi,i)
      push!(divi,-i)
      push!(divi, div(n,i))
      push!(divi, -div(n,i))
    end
    i = i + 1
  end
  
  # case where n is a square. then d[1] = sqrt(n) is a divisor
  if d[2] == 0 
    push!(divi,d[1])
    push!(divi,-d[1])
  end
  return divi
end

doc"""
*
    squaredivisors(n::fmpz) -> Array{fmpz, 1}
> Computes the numbers whose square divides a given number $n$. It is assumed
> that $n$ is not zero.
"""
function squaredivisors(n)
  n == 0 && error("The number must be nonzero")  
  divi = Nemo.fmpz[]
  for i in 1:length(divisors(n))
    if mod(n, divisors(n)[i]^2) == 0
      push!(divi, divisors(n)[i])
    end
  end
        
  return divi
end

doc"""
***
  zeros(f::fmpz_poly) -> Array{fmpz, 1}

> Computes the integer zeros of a given polynomial $f$.
"""
function zeros(f::fmpz_poly)

  fac = factor(f)
  zeros = Nemo.fmpz[]
    
    # check if there are monic linear factors <-> zeros
  for i in fac
    if degree(i[1]) == 1 && lead(i[1]) == 1
      push!(zeros, -coeff(i[1],0))
    end
  end
    
  return zeros
end


###### TORSION POINTS ######
# E elliptic curve defined over Q. We are interested in tor(E) = {P in E(Q) | P has finite order}
# torsion_points, torsion_divi
# torsion_structure


doc"""
***
    torsion_points_lutz_nagell(E::EllCrv{fmpq}) -> Array{EllCrvPt, 1}

> Computes the torsion points of an elliptic curve using the Lutz-Nagell theorem.
> It is assumed that $E$ is given in short Weierstrass form with integral coefficients.
"""
function torsion_points_lutz_nagell(E::EllCrv{fmpq}) # makes sure that the curve is defined over QQ
  !E.short && error("Elliptic curve must be given by short form")
  if (den(E.coeff[1]) != 1) || (den(E.coeff[2]) != 1)
    error("Need integer coefficients")
  end
    
  res = [infinity(E)]
  d = disc(E)
    
  # Lutz-Nagell: necessary: y = 0 or y^2 divides d

  ycand = squaredivisors(num(d)) # candidates for y-coordinate

  push!(ycand,0)

  pcand = [] # candidates for torsion points
    
  # Lutz-Nagell: coordinates of torsion points need to be in ZZ
  for i = 1:length(ycand)
    # are there corresponding integer x-values?
    xcand = zeros(Zx(x)^3 + (num(E.coeff[1]))*Zx(x) + (num(E.coeff[2])) - ycand[i]^2)
      if length(xcand) != 0 
        for j = 1: length(xcand)
          push!(pcand, (xcand[j], ycand[i])) # add to candidates
        end
      end
    end
    
    # check if candidates are torsion points
    if length(pcand) != 0
      for i = 1:length(pcand)
        P = E([pcand[i][1],pcand[i][2]])
            
        # Mazur: Order of torsion point is at most 12
        for j = 1:12 
          if (j*P).isinfinite == true 
            push!(res,P)
            break
          end
        end
      end
    end
    return res
end

doc"""
***
    torsion_points_division_poly(E::EllCrv{fmpq}) -> Array{EllCrvPt}

> Computes the torsion points of an rational elliptic $E$ curve using division
> polynomials.
"""
function torsion_divi(F::EllCrv{fmpq})
    
  if isdefined(F, :torsion_points)
    return F.torsion_points
  end
    
  # if necessary, transform curve into short form
  if F.short == false
    (G, trafo, ruecktrafo) = get_short(F)
  else 
    G = F
  end

  # transform the curve to an equivalent one with integer coefficients, if necessary
    (E, trafo_int, trafo_rat) = makeintegral(G)
    
  # check whether we already know the torsion points or not
  if isdefined(E, :torsion_points)
    if F.short == false 
      F.torsion_points = []
      for i = 1:length(E.torsion_points)
        push!(F.torsion_points, ruecktrafo(trafo_rat(E.torsion_points[i])))
      end
    else
      F.torsion_points = []
      for i = 1:length(E.torsion_points)
        push!(F.torsion_points, trafo_rat(E.torsion_points[i]))
      end
    end
    return F.torsion_points 
  end
    
  # curve has integer coefficients
  A = num(E.coeff[1])
  B = num(E.coeff[2])
      
  torsionpoints = [infinity(E)]
    
  # points of order 2 (point has order 2 iff y-coordinate is zero) 
  # (note: these points are not detected by the division polynomials)
  s = zeros(Zx(x)^3 + A*Zx(x) + B) # solutions of x^3 + Ax + B = 0
  if length(s) != 0 
    for i = 1:length(s) 
      P = E([s[i], 0])
      push!(torsionpoints, P)
    end
  end
    
  # Mazur: order of torsion point is at most 12
  for n = 7 : 12 # points of smaller order will also be found
    Psi = Psi_polynomial(E,n)
    z = zeros(Psi)
                
    if length(z) == 0
      continue
    end
        
    # z contains candidates for x-coordinates of torsion points
    for i = 1:length(z)
            
      # are there corresponding integer-square y-coordinates?
      ysquarecand = z[i]^3 + A*z[i] + B
         
      if ysquarecand < 0
        continue
      end
            
      a = isqrtrem(ysquarecand)
            
      if a[1] == 0 # then ysquarecand = 0, so have found torsion point
        P = E([z[i], ysquarecand])
                
        # if not already contained in torsionpoints, add P
        if !(P in torsionpoints) 
          push!(torsionpoints, P)
        end
                
        continue
      end
            
      # now ysquarecand > 0 
      if a[2] == 0 # then y is a square of an integer
        P = E([z[i], a[1]])
        Q = E([z[i], -a[1]])
                
        # if not already contained in torsionpoints, add P and Q
        if !(P in torsionpoints)
          push!(torsionpoints, P)
          push!(torsionpoints, Q)
        end
      end
    end

    end
    
    if F.short == false 
         for i = 1:length(torsionpoints)
            torsionpoints[i]= ruecktrafo(trafo_rat(torsionpoints[i]))
         end
    else
        for i = 1:length(torsionpoints)
            torsionpoints[i] = trafo_rat(torsionpoints[i])
        end
    end
    
    F.torsion_points = torsionpoints
    
    return F.torsion_points
end

doc"""
torsion_structure(E::EllCrv{fmpq}) -> (A::Array(Nemo.fmpz), B::Array(Nemo.fmpz))
> computes the structure of the torsion group tor(E) of an elliptic curve E
> tor(E) is isomorphic to Z/nZ x Z/mZ with (n,m) = (2,2), (2,4), (2,6), (2,8) or to Z/nZ for n in 1:10 or n = 12
> returns a tuple (A,B), where
> A is an array with A = [n] resp. A = [n,m]
> B is an array of points with B = [P] and P has order n resp. B = [P, Q] and P has order n, Q has order m
"""
function torsion_structure(E::EllCrv{fmpq})
    T = torsion_divi(E)
    grouporder = length(T)
    orders = []
        
    for i in 1:grouporder
        push!(orders, 0)
    end
    
    # determine orders of group elements
    for i in 1:grouporder
        j = 1
        while (j < 13) && (orders[i] == 0)
            if (j*T[i]).isinfinite == true
                orders[i] = j
            end
            j = j + 1
        end
    end
    
    # find generators 
    if in(grouporder, orders) == true # is the group cyclic?
        k = findfirst(orders, grouporder)
        return ([grouporder], [T[k]])
    else # group not cyclic
        m = div(grouporder, 2)
        k1 = findfirst(orders, 2)
        k2 = findlast(orders, m) # findlast to get different points if m = 2
        points = [T[k1], T[k2]]
        return ([2, m], points)
    end

end


###### TRANSFORMATIONS ######
# get_short, get_short_finite_field, makeintegral

doc"""
get_short(E::EllCrv{fmpq}) -> (EE::EllCrv, function(EllCrvPt), function(EllCrvPt))
> transforms a curve given in long Weierstrass form over QQ to short Weierstrass form
> returns short form and both transformations for points on the curve; first transformation from E (long form) to EE (short form), second transformation the other way round
"""
function get_short(E::EllCrv{fmpq})
    
    a1 = E.coeff[1]
    a2 = E.coeff[2]
    a3 = E.coeff[3]
    a4 = E.coeff[4]
    a6 = E.coeff[5]
    
    b2 = a1^2 + 4*a2
    b4 = a1*a3 + 2*a4
    b6 = a3^2 + 4*a6
    
    c4 = b2^2 - 24*b4
    c6 = -b2^3 + 36* b2*b4 - 216* b6
    
    Anew = -divexact(c4, 48)
    Bnew = -divexact(c6, 864)
    
    EE = EllipticCurve([Anew, Bnew])
    
    trafo = function(P) # transformes a point on E (long form) to a point on EE (short form)
        if P.isinfinite
            return infinity(EE)
        end
        
        xnew = P.coordx + divexact(b2, 12)
        ynew = P.coordy + divexact(a1*P.coordx + a3, 2)
        Q = EE([xnew, ynew])
        return Q
    end
    
    ruecktrafo = function(R) # transformes a point on EE (short form) back to a point on E (long form)
        if R.isinfinite
            return infinity(E)
        end
          
        xnew = R.coordx - divexact(b2, 12)
        ynew = R.coordy - divexact(a1*xnew + a3, 2)
        S = E([xnew, ynew])
        return S
    end
        
    return EE, trafo, ruecktrafo
end

doc"""
get_short_finite_field(E::EllCrv) -> (EE::EllCrv, function(EllCrvPt), function(EllCrvPt))
> transforms a curve given in long Weierstrass form over a finite field to short Weierstrass form
> returns short form and both transformations for points on the curve; first transformation from E (long form) to EE (short form), second transformation the other way round
> does not work in characteristic 2 and 3
"""
function get_short_finite_field(E::EllCrv)
    
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
    
    b2 = a1^2 + 4*a2
    b4 = a1*a3 + 2*a4
    b6 = a3^2 + 4*a6
    
    c4 = b2^2 - 24*b4
    c6 = -b2^3 + 36* b2*b4 - 216* b6
    
    Anew = -divexact(c4, R(48))
    Bnew = -divexact(c6, R(864))
    
    EE = EllipticCurve([Anew, Bnew])
    
    trafo = function(P) # transformes a point on E (long form) to a point on EE (short form)
        if P.isinfinite
            return infinity(EE)
        end
        
        xnew = P.coordx + divexact(b2, R(12))
        ynew = P.coordy + divexact(a1*P.coordx + a3, R(2))
        Q = EE([xnew, ynew])
        return Q
    end
    
    ruecktrafo = function(X) # transformes a point on EE (short form) back to a point on E (long form)
        if X.isinfinite
            return infinity(E)
        end
          
        xnew = X.coordx - divexact(b2, R(12))
        ynew = X.coordy - divexact(a1*xnew + a3, R(2))
        S = E([xnew, ynew])
        return S
    end
        
    return EE, trafo, ruecktrafo
end

doc"""
makeintegral(E::EllCrv{fmpq}) -> (E_int::EllCrv{fmpz}, function(EllCrvPt), function(EllCrvPt))
> transforms a curve given in short form over QQ into an equivalent curve in short form over ZZ
> returns new curve and both transformations for points on the curve; first transformation from E (over QQ) to E_int (over ZZ), second transformation the other way round
"""
function makeintegral(E::EllCrv{fmpq})
    A = E.coeff[1]
    B = E.coeff[2]
    
    if (den(A) == 1) && (den(B) == 1) # curve already has integer coefficients
        
        trafo_int = function(P)
            return P
        end
            
        trafo_rat = function(R)
            return R
        end
        
        return copy(E), trafo_int, trafo_rat
                
    else # need to do a transformation (that does not change the j-invariant) 
        mue = lcm(den(A), den(B))
        Anew = mue^4 * A
        Bnew = mue^6 * B 
        E_int = EllipticCurve([Anew, Bnew])

        trafo_int = function(P) # transformes a point on E into a point on E_int
            if P.isinfinite
                return infinity(E_int)
            end
            
            xnew = mue^2 * P.coordx
            ynew = mue^3 * P.coordy
            Q = E_int([xnew, ynew])
            return Q
        end
                    
        trafo_rat = function(R) # transformes a point on E_int back into a point on E
            if R.isinfinite
                return infinity(E)
            end
            
            xnew = divexact(R.coordx, mue^2)
            ynew = divexact(R.coordy, mue^3)
            S = E([xnew, ynew])
            return S
        end
        
    end
    
    return E_int, trafo_int, trafo_rat
end


###### FINITE FIELDS ######
# order, characteristic
# order_via_legendre, hasse_interval
# elem_order_bsgs, order_via_bsgs
# next_prime, is_square, rand_finitefield, random
# order_via_schoof, prime_set, t_mod_prime

## Order of points and point counting

doc"""
order(R::ResRing{fmpz}) -> Nemo.fmpz
> returns the order of a finite field R
""" 
function order(R::ResRing{fmpz})
    return abs(modulus(R))
end


doc"""
characteristic(R::ResRing{fmpz}) -> Nemo.fmpz
> returns the characteristic of R
"""
function characteristic(R::ResRing{fmpz})
    return abs(modulus(R))
end

function characteristic(R::FlintRationalField)
    return fmpz(0)
end

doc"""
order_via_legendre(E::EllCrv) -> Nemo.fmpz
> calculates the number of points on an elliptic curve E given over a finite field F_p, p prime, using the Legendre symbol
"""
# Th. 4.14
function order_via_legendre(E)
    R = base_field(E)
    p = characteristic(R)
    q = order(R)
    grouporder = 0
    
    if p != q
        error("cannot deal with a finite field of degree > 1")
    end
    
    if E.short == false
        E = get_short_finite_field(E)[1]
    end
    
    if isprime(q)
    
        x = 0
        while x < p
            C = x^3 + (E.coeff[1])*x + (E.coeff[2])
            Cnew = C.data # convert to fmpz
            a = jacobi(Cnew, p) # can be used to compute (C/F_p) since p prime
            grouporder = grouporder + a
            x = x + 1
        end

        grouporder = grouporder + p + 1
        return grouporder
        
    else ### need list of elements of F_q
        
        legendre = []
        for i = 1:q
            push!(legendre, -1)
        end
        
        a = gen(R)
        n = degree(R)
        
        elements = []
        for i = 0:(n-1)
            for k = 1:(i*p) 
                for j = 0:(p-1)
                    push!(elements, j*(a^i))
                end
            end
        end
    end
end

doc"""
hasse_interval(E::EllCrv) -> Array{Nemo.fmpz}
> input: E elliptic curve given over a finite field F_q
> output: interval [l, b] with l <= #E(F_q) <= b (Hasse's theorem)
"""
function hasse_interval(E::EllCrv)
    R = base_field(E)
    q = order(R)
    s = isqrtrem(q)[1] # sqrt(q) rounded down
    
    l = q + 1 - 2*(s + 1)
    b = q + 1 + 2*(s + 1)
    
    return [l, b]
end
    
doc"""
elem_order_bsgs(P::EllCrvPt) -> Nemo.fmpz
> calculates the order of a point P on an elliptic curve given over F_q using the 'baby step, giant step'- method 
"""
# section 4.3.4
function elem_order_bsgs(P)
    R = base_field(P.parent)
    p = characteristic(R)
    q = order(R) # R = F_q
    
    # step 1
    Q = Int(q + 1) * P
    
    # step 2
    m = Int( ceil(Int(q)^(1//4)) )

    list_points = []
    for j = 0:m
        S = j*P
        push!(list_points, S)
    end
    
    # step 3
    k = -m
    H = (2*m)*P
    M = ZZ(0) # initialize M, so that it is known after the while loop
    
    while k < m + 1
        Snew = Q + (k*H)
        
        i = 1
        while i < m + 2 # is there a match?
            if Snew == list_points[i] 
                M = q + 1 + (2*m*k) - (i-1) 
                
                if M != 0        
                    i = m + 2 # leave both while loops
                    k = m + 1
                else
                    i = i + 1 # search on if M == 0
                end
                
            elseif Snew == inverse(list_points[i])
                M = q + 1 + (2*m*k) + (i-1) # step 4
                
                if M != 0 
                    i = m + 2 # leave both while loops
                    k = m + 1
                else
                    i = i + 1 # search on if M == 0
                end
            else 
                i = i + 1
            end
        end
        
        k = k + 1
    end
    
    # step 5
    gotostep5 = true
    while gotostep5
        fac = factor(M)
        primefactors = []
        for i in fac
            push!(primefactors, i[1])
        end
        r = length(primefactors)

        # step 6
        i = 1
        while i < (r + 1)
            T = Int(divexact(M, primefactors[i]))*P 
            if T.isinfinite == true
                M = divexact(M, primefactors[i])
                i = r + 2  # leave while-loop
            else
                i = i + 1
            end
        end
        
        if i == r + 1  # then (M/p_i)P != oo for all i
            gotostep5 = false
        end
    end
        
    return M
end

doc"""
order_via_bsgs(E::EllCrv) -> Array{Nemo.fmpz}
> calculates the number of points on an elliptic curve E given over a finite field F_q, using the baby step, giant step method
> may only return an array of candidates for #E(F_q). if q prime, q > 229, then the order is determined uniquely by this algorithm
> does not work in characteristic 2
"""
function order_via_bsgs(E)
    R = base_field(E)
    p = characteristic(R)
    q = order(R)
    
    if (p == 2) 
        error("Characteristic must not be 2")
    end
    
    if E.short == false
        E = get_short_finite_field(E)[1]
    end
    
    Nposs = ZZ(1)
    h = hasse_interval(E)
    l = h[1]
    b = h[2]
    
    counter = 0
    runwhile = true
   
    # if Nposs is greater than interval length, there is only one multiple of Nposs in the interval, so stop
    # also, if lcm does not change in 10(?) consecutive loops, leave while loop
    while (Nposs <= (b-l)) && (runwhile == true)
    
        P = random(E)
        ord = elem_order_bsgs(P)
        
        if lcm(ord, Nposs) == Nposs
            counter = counter + 1
        else
            Nposs = lcm(ord, Nposs)
            counter = 0
        end
        
        if counter > 10 # maybe take another criterion 
            runwhile = false
        end

    end
    
    if runwhile == false # could not determine group order uniquely
        candidates = []
        Ncand = divrem(l, Nposs)[1]*Nposs
        if Ncand != 0
            push!(candidates, Ncand)
        end
        
        Ncand = Ncand + Nposs
        
        while Ncand < b # compute all possible group orders using Hasse's theorem
            push!(candidates, Ncand)
            Ncand = Ncand + Nposs
        end
        
        output = candidates
        
    else # group order is determined
        N = (divrem(l+1, Nposs)[1] + 1) * Nposs
        output = [N]
    end
    
    if (p == q) && (p > 229) && (length(output) != 1)
    # group order is uniquely determined, but by quadratic twist
        
        d = R(0)
        boolie = true
        while boolie # get a quadratic non-residue mod p
            d = rand_finitefield(R)
            if is_square(d)[1] == false
                boolie = false
            end
        end
        
        Eprime = EllipticCurve([E.coeff[1]*d^2, E.coeff[2]*d^3]) # quadratic twist
        b = order_via_bsgs(Eprime)[1]
        output = [2*p + 2 - b]
    end
    
    return output
end


doc"""
next_prime(z::Int) -> Int
> returns the next prime, starting from z
"""
function next_prime{T <: Integer}(z::T)
  z < 0 && error("Argument must be positive") 

  Tone = one(z)
  Tzero = zero(z)
  Ttwo = one(z) + one(z)

  if z == Tone || z == Tzero
    return Ttwo
  end

  if iseven(z)
    z += Tone
  else z += Ttwo
  end

  while !isprime(z)
    z += Ttwo
  end

  return z
end


doc"""
is_square(x::ResElem{fmpz}) -> (Bool, ResElem)
> checks if an element x of a ResidueRing of ZZ is a square, say of y
> returns (true, y) in that case and (false, 0) otherwise 
"""
function is_square(x::ResElem{fmpz})
    R = parent(x)
    p = characteristic(R)
    xnew = x.data
    
    j = jacobi(xnew, p)
    if j == 0
        return true, zero(R)
    elseif j == 1
        root = sqrtmod(xnew, p)
        return true, R(root)
    else
        return false, zero(R)
    end
end


doc"""
is_square(x) -> (Bool, ResElem)
> checks if an element x of F_q is a square, say of y
> returns (true, y) in that case and (false, 0) otherwise 
"""
function is_square(x)
    R = parent(x)
    S, t = PolynomialRing(R, "t")
    
    # check if x is a square by considering the polynomial f = t^2 - x
    # x is a square in F_q iff f has a root in F_q
    f = t^2 - x
    fac = factor(f)

    p = first(keys(fac))
    
    if fac[p] == 2 # f has a double zero
        root = -coeff(p, 0)
        return true, R(root)
    elseif length(fac) == 2 # f splits into two different linear factors
        root = -coeff(p, 0)
        return true, R(root)
    else # f does not have a root
        return false, zero(R)
    end
    
end


doc"""
rand_finitefield(R::Nemo.FqNmodFiniteField) -> Nemo.fqn_mod
> returns a random element of the finite field R
"""
function rand_finitefield(R)
    q = order(R)
    p = characteristic(R)
    
    if p == q
        e = rand(0:Int(q-1))
        return R(e)
        
    else
        a = gen(R)
        n = degree(R) # q = p^n 
            
        lambda = rand(0:Int(p-1), n)
        e = zero(R)
        
        for i = 1:n
            e = e + R(lambda[i])*a^(i-1)
        end
        
        return e
        
    end
end


doc"""
random(E::EllCrv) -> EllCrvPt
> returns a random point on the elliptic curve E defined over F_q (E in short form!)
"""
# only works for short form
function random(E::EllCrv)
    R = base_field(E)
    
    if E.short == false
        error("does not work for long form")
    end
    
    while true
        # choose random x-coordinate and check if it is a square in F_q
        # if not, choose new x-coordinate
        x = rand_finitefield(R)
        square = x^3 + E.coeff[1]*x + E.coeff[2]
        
        a = is_square(square)
        if a[1] == true # square is a square in F_q, so have found point on the curve
            y = a[2]
            P = E([x, y])
            return P
        end
    end

end


### Schoof's algorithm ###
include("Schoof.jl")


doc"""
order_via_schoof(E::EllCrv) -> Nemo.fmpz
> E elliptic curve given over F_q. uses Schoof's algorithm to determine #E(F_q)
> does not work in characteristic 2 and 3
"""
function order_via_schoof(E::EllCrv) 
    R = base_field(E)
    q = order(R)
    p = characteristic(R)
    
    if (p == 2) || (p == 3)
        error("Characteristic must not be 2 or 3")
    end
    
    if E.short == false
        E = get_short_finite_field(E)[1]
    end
    
    # step 1: get suitable set S of prime numbers
    sqrt_q = isqrtrem(q)[1] 
    S = prime_set(4*(sqrt_q + 1), p)
    
    L = length(S)
    product = 1
    
    # step 2: compute t (mod l) for every l in S
    t_mod_l = []
    for i = 1:L
        a = S[i]
        push!(t_mod_l, t_mod_prime(S[i], E))
        product = product * S[i]
    end
    
    # step 3: use chinese remainder theorem to get value of t
    t = 0
    for i = 1:L
        n_i = div(product, S[i])
        B = ResidueRing(ZZ, S[i])
        M_i = inv(B(n_i))
        M_i = M_i.data
        t = t + (M_i * n_i * t_mod_l[i])
    end
    
    t = mod(t, product)
    if t > product//2
        t = t - product
    end
    
    return q + 1 - t
    
end


doc"""
prime_set(M::Nemo.fmpz, char::Nemo.fmpz) -> Array{Nemo.fmpz}
>  returns a set S of primes with:
 1) char not contained in S
 2) product of elements in S is greater than M
"""
function prime_set(M, char)
    S = Nemo.fmpz[]
    
    p = 1
    product = 1
    
    while product < M
        p = next_prime(p)
        
        if p != char
            push!(S,p)
            product = product * p 
        end
    end
    
    return S
end
    

doc"""
t_mod_prime(l::Nemo.fmpz, E::EllCrv) -> Nemo.fmpz
> determines the value of t modulo some prime l (used in Schoof's algorithm)
"""
function t_mod_prime(l, E)
    R = base_field(E)
    q = order(R)
    q_int = Int(q)
    l = Int(l)
    
    S, x = PolynomialRing(R, "x")
    T, y = PolynomialRing(S, "y")
    Z = ResidueRing(ZZ, l)
    
    f = x^3 + E.coeff[1]*x + E.coeff[2]
    fl = fn_from_schoof(E, l, x)
    U = ResidueRing(S, fl)
    
    PsiPoly = [] # list of psi-polynomials
    for i = -1:(l + 1)
        push!(PsiPoly, psi_poly_field(E,i,x,y)) # Psi[n] is now found in PsiPoly[n+2]
    end
    
    Fnschoof = [] # list of the fn- functions # Psi[n] is now found in PsiPoly[n+2]
    for i = -1:(l + 1)
        push!(Fnschoof, fn_from_schoof(E,i,x))
    end
    
    
    # case where l == 2. value of t mod l determined by some gcd, see p. 124
    if l == 2
        x_q = powmod(x, q_int, f)
        ggt = gcd(f, x_q - x)
        if ggt == 1
            t = ZZ(1)
        else
            t = ZZ(0)
        end
        
        return t
    end
    
    # case where l != 2
    k = mod(q, l) # reduce q mod l
    k_mod = Z(k)
    
    fk = Fnschoof[k+2]
    fkme = Fnschoof[k+1]
    fkpe = Fnschoof[k+3]
    fkpz = Fnschoof[k+4]
    
    
    
    #fk = fn_from_schoof(E, k, x)
    #fkme = fn_from_schoof(E, k-1, x)
    #fkpe = fn_from_schoof(E, k+1, x)
    #fkpz = fn_from_schoof(E, k+2, x)
    
    # is there a nonzero P = (x,y) in E[l] with phi^2(P) == +-kP ?
    if mod(k,2) == 0 
        g = U( (powmod(x, q_int^2, fl) - x) * fk^2 * f + fkme * fkpe).data
        ggT = gcd(g, fl)
    else
        g = U( (powmod(x, q_int^2, fl) - x) * fk^2 + fkme * fkpe * f).data
        ggT = gcd(g, fl)
    end
    
    if ggT != 1 # case 1
       if jacobi(ZZ(k), ZZ(l)) == -1 
            return ZZ(0) 
       else 
            # need square root of q (mod l)
            w = is_square(k_mod)[2]
            if w.data < 0
                w = w + l
            end
            w_int = Int(w.data)
            
            
            fw = Fnschoof[w_int+2]
            fwme = Fnschoof[w_int+1]
            fwpe = Fnschoof[w_int+3]
            
            #fw = fn_from_schoof(E, w_int, x)
            #fwme = fn_from_schoof(E, w_int - 1, x)
            #fwpe = fn_from_schoof(E, w_int + 1, x)
            
            if mod(w_int, 2) == 0 
                g = U((powmod(x,q_int,fl) - x) * fw^2*f + fwme*fwpe).data # reduce mod fl
                ggT = gcd(g, fl)
            else
                g = U((powmod(x,q_int,fl) - x) * fw^2 + fwme*fwpe*f).data
                ggT = gcd(g, fl)
            end
            
            if ggT == 1
                return ZZ(0)
            else
                fwmz = Fnschoof[w_int]
                fwpz = Fnschoof[w_int+4]
                
                #fwmz = fn_from_schoof(E, w_int - 2, x)
                #fwpz = fn_from_schoof(E, w_int + 2, x)
                
                if mod(w_int, 2) == 0
                    g = U(4 * powmod(f,div(q_int + 3, 2),fl)*fw^3 - (fwpz * fwme^2) + (fwmz*fwpe^2)).data
                    ggT2 = gcd(g, fl)
                else
                    g = U(4 * powmod(f,div(q_int - 1, 2),fl)*fw^3 - (fwpz * fwme^2) + (fwmz*fwpe^2)).data
                    ggT2 = gcd(g, fl)
                end
                
                if ggT2 == 1
                    return -2*(w.data)
                else
                    return 2*(w.data)
                end
            end
            
       end
       

    else # case 2
        
        #println("Mammiiiiii")
        
        
        Fkmz = PsiPoly[k]
        Fkme = PsiPoly[k+1]
        Fk = PsiPoly[k+2]
        Fkpe = PsiPoly[k+3]
        Fkpz = PsiPoly[k+4]
        
        
        #Fkmz = psi_poly_field(E, k - 2, x, y)
        #Fkme = psi_poly_field(E, k - 1, x, y)
        #Fk = psi_poly_field(E, k, x, y)
        #Fkpe = psi_poly_field(E, k + 1, x, y)
        #Fkpz = psi_poly_field(E, k + 2, x, y)
        
        alpha = Fkpz*psi_power_mod_poly(k-1,E,x,y,2,fl) - Fkmz*psi_power_mod_poly(k+1,E,x,y,2,fl) - 4*powmod(f,div(q_int^2+1,2),fl)*psi_power_mod_poly(k,E,x,y,3,fl)
        beta = ((x - powmod(x, (q_int^2), fl))*psi_power_mod_poly(k,E,x,y,2,fl)- Fkme*Fkpe)*4*y*Fk
        
        tau = 1
        while tau < l
            
            ftaumz = PsiPoly[tau]
            ftaume = PsiPoly[tau+1]
            ftau = PsiPoly[tau+2]
            ftaupe = PsiPoly[tau+3]
            ftaupz = PsiPoly[tau+4]
            
            fntaumz = Fnschoof[tau]
            fntaume = Fnschoof[tau+1]
            fntaupe = Fnschoof[tau+3]
            fntaupz = Fnschoof[tau+4]
            
            #ftaumz = psi_poly_field(E, tau - 2, x, y)
            #ftaume = psi_poly_field(E, tau - 1, x,y)
            #ftau = psi_poly_field(E, tau, x,y)
            #ftaupe = psi_poly_field(E, tau + 1, x,y)
            #ftaupz = psi_poly_field(E, tau + 2, x,y)
            
            #fntaumz = fn_from_schoof(E, tau - 2, x)
            #fntaume = fn_from_schoof(E, tau - 1, x)
            #fntaupe = fn_from_schoof(E, tau +1, x)
            #fntaupz = fn_from_schoof(E, tau + 2, x)
           
            gammahelp = powmod(fntaupz*fntaume^2- fntaumz * fntaupe^2,q_int,fl)
            
            
            if mod(tau, 2) == 0 
                gamma = y * powmod(f,div(q_int-1,2),fl) * gammahelp
            else gamma = powmod(f,q_int,fl) * gammahelp
            end
            
            monster1 = ((Fkme*Fkpe - psi_power_mod_poly(k,E,x,y,2,fl)*(powmod(x, q_int^2, fl) + powmod(x, q_int, fl) + x)) * beta^2 + psi_power_mod_poly(k,E,x,y,2,fl)*alpha^2) * psi_power_mod_poly(tau,E,x,y,2*q_int,fl) + psi_power_mod_poly(tau-1, E, x,y,q_int,fl)*psi_power_mod_poly(tau+1, E, x,y,q_int, fl)*beta^2*psi_power_mod_poly(k,E,x,y,2,fl)
            
            if divrem(degree(monster1), 2)[2] == 1
                monster1 = divexact(monster1, y)
            end
            
            monster1_1 = replace_all_squares_modulo(monster1, f, fl)
            monster1_2 = U(monster1_1).data # monster1_1 reduced
         
            if monster1_2 != 0
                tau = tau + 1
            else
                monster2 = 4*y*powmod(f,div(q_int-1,2),fl)*psi_power_mod_poly(tau,E,x,y,3*q_int,fl) * (alpha * (((2*powmod(x, q_int^2, fl) + x) * psi_power_mod_poly(k,E,x,y,2,fl) - Fkme*Fkpe )*beta^2 - alpha^2*psi_power_mod_poly(k,E,x,y,2,fl)) - y*powmod(f,div(q_int^2-1,2),fl)*beta^3 * Fk^2) - beta^3*psi_power_mod_poly(k,E,x,y,2,fl)*gamma
                
                if divrem(degree(monster2), 2)[2] == 1
                    monster2 = divexact(monster2, y)
                end

                monster2_1 = replace_all_squares_modulo(monster2, f,fl)
                monster2_2 = U(monster2_1).data # monster2_1 mod fl
                
                if monster2_2 != 0
                    tau = tau + 1
                else
                    return tau
                end
                
            end
            
        end
            
    end
    
end

# computes psi_n^power mod g
function psi_power_mod_poly(n, E, x, y, power, g)
    
    fn = fn_from_schoof(E, n, x)
    f = x^3 + E.coeff[1]*x + E.coeff[2]
    p = powmod(fn,power,g)
    
    if mod(n, 2) == 0
        if mod(power, 2) == 0
            p1 = powmod(f, div(power, 2), g)
        else
            p1 = powmod(f, div(power - 1, 2), g) * y
        end
    else p1 = 1
    end
    
    return p * p1
end

doc"""
special_order2(E::EllCrv{NemoResidue}) -> Nemo.fmpz
> counts points on an elliptic curve E given over F_2
"""
function special_order2(E)
    R = base_field(E) # should be Z/2Z
    ord = ZZ(1)
    
    for i = 0:1
        for j = 0:1
            if is_on_curve(E, [R(i), R(j)])
                ord = ord + 1
            end
        end
    end
    
    return ord
end


doc"""
special_order3(E::EllCrv{NemoResidue}) -> Nemo.fmpz
> counts points on an elliptic curve E given over F_3 
"""
function special_order3(E)
    R = base_field(E) # should be Z/3Z
    ord = ZZ(1)
    
    for i = 0:2
        for j = 0:2
            if is_on_curve(E, [R(i), R(j)])
                ord = ord + 1
            end
        end
    end
    
    return ord
end


doc"""
order_best(E::EllCrv{NemoResidue}) -> Nemo.fmpz
> E elliptic curve given over F_q. computes #E(F_q) by selecting the best method for the given F_q
"""
function order_best(E)
    R = base_field(E)
    p = characteristic(R)
    q = order(R)
    
    # char 2
    if p == 2
        if q > 2
            error("Don't have algorithm for char = 2 and not F_2") # legendre is the only algorithm that can deal with char = 2, but q must be equal to p
        else 
            return special_order2(E)
        end
    end
    
    # char 3
    if p == 3 
        if q > 3
            error("Don't have algorithm for char = 3 and not F_3")
        else
            return special_order3(E)
        end
    end
    
    if q == p
        if p <= 229
            return order_via_legendre(E)
        else
            return order_via_bsgs(E)[1] # now no candidates as output, faster than schoof
        end
    else # now legendre does not work
        return order_via_schoof(E) # bsgs may only return candidate list
    end
    
end


###### MINIMAL MODELS AND BSD-CONJECTURE ######
# laska_kraus_connell
# mod_red, check_weak_bsd
# transform, quadroots, nrootscubic, ord_p, minimal_residue
# tates_algorithm_local, tates_algorithm_global, tidy_model

doc"""
laska_kraus_connell(E::EllCrv{fmpz}) -> Array{Nemo.fmpz}
> input: E elliptic curve given in long form over ZZ
> output: integral coefficients of an isomorphic(?) elliptic curve such that the discriminant is minimized
"""
# algorithm of Laska-Kraus-Connell
function laska_kraus_connell(E)
    
    a1 = num(E.coeff[1])
    a2 = num(E.coeff[2])
    a3 = num(E.coeff[3])
    a4 = num(E.coeff[4])
    a6 = num(E.coeff[5])
    
    b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)
    
    delta = divexact(c4^3 - c6^2, 1728)
    
    u = 1
    g = gcd(c6^2, delta)
    
    fac = factor(g)
    p_list = [i[1] for i in fac]
    exp_list = [i[2] for i  in fac]
    
    for i in 1:length(p_list)
        p = p_list[i]
        ord = exp_list[i]
        d = div(ord, 12)
        
        if p == 2
            a = divexact(c4, 2^(4*d))
            a = mod(a, ZZ(16))
            if a > 8
                a = a - 16
            end
            
            b = divexact(c6, 2^(6*d))
            b = mod(b, ZZ(32))
            if b > 16
                b = b - 32
            end
            
            if (mod(b, 4) != 3) && ((a != 0) || ((b != 0) && (b != 8)) )
                d = d - 1
            end
            
        elseif p == 3
            ord1 = remove(c6, ZZ(3))[1]
            
            if (ord1 == 6*d + 2)
                d = d - 1
            end
        end
        
        u = u * p^d
    end
    
    c4 = divexact(c4, u^4)
    c6 = divexact(c6, u^6) 
    b2 = mod(-c6, ZZ(12))
    
    if b2 > 6
        b2 = b2 - 12
    end
    
    b4 = divexact(b2^2 - c4, ZZ(24))
    b6 = divexact(-b2^3 + 36*b2*b4 - c6, ZZ(216))
    
    a1 = mod(b2, ZZ(2))
    a3 = mod(b6, ZZ(2))
    a2 = divexact(b2 - a1, ZZ(4))
    a4 = divexact(b4 - a1*a3, 2)
    a6 = divexact(b6 - a3, ZZ(4))

    return [a1, a2, a3, a4, a6]
end

doc"""
mod_red(E::EllCrv, B::Int) -> (P::Array{Int}, N::Array{Nemo.fmpz})
> input: E elliptic curve given in long form over ZZ
> output: arrays P, N, where
  P contains all primes smaller than B (for which E/F_p is non-singular)
  N[i] = #E(F_P[i])
"""
function mod_red(E, B)
    minmodel = EllipticCurve(laska_kraus_connell(E)) # global minimal model for E
    P = primes(B) # primes smaller than B
    N = Nemo.fmpz[]
    
    for i in 1:length(P)
        p = P[i]
        R = ResidueRing(ZZ, p)
        Ep = EllipticCurve([R(num(minmodel.coeff[1])), R(num(minmodel.coeff[2])), R(num(minmodel.coeff[3])), R(num(minmodel.coeff[4])), R(num(minmodel.coeff[5]))],  false) # reduction of E mod p 
        
        if  disc(Ep) != 0 # can only determine group order if curve is non-singular
            ord = order_best(Ep)
            push!(N, ord)
        else 
            P[i] = 0
        end
    end
    
    P = deleteat!(P, findin(P, 0)) # delete all zeros from P
    
    return P, N  
end

doc"""
check_weak_bsd(E::EllCrv, B::Int) -> (a::Float64, b::Float64)
> checks weak bsd-conjecture for elliptic curve E given in long form over ZZ, positive integer B
> returns linear regression values for log(log(B)) and sum of log(N_p/p) for p <= B
"""
function check_weak_bsd(E, B)
    
    (P, N) = mod_red(E, B)
    a = length(P)
    logprod = Float64[]
    loglogB = Float64[]
    
    # initial value
    push!(logprod, log(Int(N[1]) / P[1]) ) # N is nemo.fmpz, P is Int64
    push!(loglogB, log(log( P[1] + 1 )) )
    
    for i in 2:(a - 1)
        push!(logprod, log(Int(N[i]) / P[i]) + logprod[i-1] )
        push!(loglogB, log(log( float(P[i] + 1 ))) )
    end
    
    # last value
    push!(logprod, log(Int(N[a]) / P[a]) + logprod[a-1] )
    push!(loglogB, log(log(B)) )
  
    a, b = linreg(loglogB, logprod)
    plot(loglogB, logprod, "o")
    plot(loglogB, [a + b*i for i in loglogB])
        
    return a, b 
end

# transformation T(r,s,t,u) as in cremona's book
function transform(E, T)
    r = T[1]
    s = T[2]
    t = T[3]
    u = T[4]
    
    a1 = E.coeff[1]
    a2 = E.coeff[2]
    a3 = E.coeff[3]
    a4 = E.coeff[4]
    a6 = E.coeff[5] 
    
    a1neu = divexact(a1 + 2*s, u)
    a2neu = divexact(a2 - s*a1 + 3*r - s^2, u^2)
    a3neu = divexact(a3 + r*a1 + 2*t, u^3)
    a4neu = divexact(a4 - s*a3 + 2*r*a2 - (t + r*s)*a1 + 3*r^2 - 2*s*t, u^4)
    a6neu = divexact(a6 + r*a4 + r^2*a2 + r^3 - t*a3 - t^2 - r*t*a1, u^6)
    
    F = EllipticCurve([a1neu, a2neu, a3neu, a4neu, a6neu])
    
    trafo1 = function(P) # transformes a point on E into a point on F
        if P.isinfinite
            return infinity(F)
        end
            
        xnew = divexact(1, u^2)*(P.coordx - r)
        ynew = divexact(1, u^3)*(P.coordy - s*u^2*xnew - t)
        Q = F([xnew, ynew])
        return Q
    end
    
    trafo2 = function(P) # transformes a point on F into a point on E
        if P.isinfinite
            return infinity(E)
        end
            
        xnew = u^2*P.coordx + r
        ynew = u^3*P.coordy + s*u^2*P.coordx + t
        Q = E([xnew, ynew])
        return Q
    end
    
    return F, trafo1, trafo2
end

doc"""
quadroots(a::Nemo.fmpz, b::Nemo.fmpz, c::Nemo.fmpz, p::Nemo.fmpz) -> Bool
> returns true if the quadratic congruence ax^2 + bx + c = 0 (mod p) has a solution and false otherwise.
"""
function quadroots(a, b, c, p)
    F_p = ResidueRing(ZZ, p)
    R, x = PolynomialRing(F_p, "x")
    f = F_p(a)*x^2 + F_p(b)*x + F_p(c)
    
    if degree(f) == -1
        return true
    elseif degree(f) == 0
        return false
    elseif degree(f) == 1
        return true
    else
        fac = factor(f)
        p = first(keys(fac))
    
        if fac[p] == 2 # f has a double zero
            return true
        elseif length(fac) == 2 # f splits into two different linear factors
            return true
        else # f does not have a root
            return false
        end
    end
    
end

doc"""
nrootscubic(b::Nemo.fmpz, c::Nemo.fmpz, d::Nemo.fmpz, p::Nemo.fmpz) -> Nemo.fmpz
> returns the number of roots of the cubic congruence x^3 + bx^2 + cx + d = 0 (mod p).
"""
function nrootscubic(b, c, d, p)
    F_p = ResidueRing(ZZ, p)
    R, x = PolynomialRing(F_p, "x")
    f = x^3 + F_p(b)*x^2 + F_p(c)*x + F_p(d)
    
    fac = factor(f)
    
    if length(fac) == 1
        if fac[first(keys(fac))] == 3
            return ZZ(3)
        else
            return ZZ(0)
        end
    elseif length(fac) == 2
        if fac[first(keys(fac))]== 1 && fac[first(keys(fac))] == 1 # one linear and one irreducible quadratic factor
            return ZZ(1)
        else 
            return ZZ(3) #one double and one single root
        end
    else 
        return ZZ(3)
    end  
end

doc"""
ord_p(p::Nemo.fmpz, n::Nemo.fmpq) -> Nemo.fmpz
> returns the power of the prime p which divides the rational number n 
"""
function ord_p(p, n)
    
    if n == 0 
        error("order of p dividing 0 not defined")
    end
    
    counternum = 0 
    counterden = 0
    a = num(n)
    b = den(n)
    
    while mod(a,p) == 0 
        counternum = counternum +1 
        a = divexact(a,p)
    end
        
    while mod(b,p) == 0 
        counterden = counterden +1 
        b = divexact(b,p)
    end
    
    # subtract
    return counternum - counterden 
end


doc"""
minimal_residue(a::Nemo.fmpz, p::Nemo.fmpz) -> Nemo.fmpz
> returns the minimal residue of a mod p (i.e. an integer b with -(1/2)p < b <= (1/2)p and a = b (mod p)).
"""
function minimal_residue(a, p)
    rest = mod(a, p) 
    
    if rest > p//2
        rest = rest - p 
    end
    
    return rest
end


doc"""
tates_algorithm_local(E::EllCrv{fmpz}, p::Int) -> Array{Nemo.fmpz}
> returns a local minimal model mod p for E
"""
# tate's algorithm, see Cremona, p. 66
function tates_algorithm_local(E, p)
    
    p = ZZ(p)
    
    a1 = num(E.coeff[1])
    a2 = num(E.coeff[2])
    a3 = num(E.coeff[3])
    a4 = num(E.coeff[4])
    a6 = num(E.coeff[5])
    
    b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)
    
    delta = disc(E)
    delta = num(delta)
    
    n = ord_p(p, delta)
    
    # test for type I0
    if n == 0        
        return E, "I0", ZZ(0), ZZ(1)
    end
    
    # change coordinates so that p | a3, a4, a6
    if p == 2       
        if mod(b2, p) == 0 
            r = minimal_residue(a4, p)
            t = minimal_residue(r*(1 + a2 + a4) + a6, p)
        else
            r = minimal_residue(a3, p)
            t = minimal_residue(r + a4, p)
        end 
        
    elseif p == 3
        if mod(b2, p) == 0
            r = minimal_residue(-b6, p)
        else
            r = minimal_residue(-b2*b4, p)
        end 
        
        t = minimal_residue(a1*r + a3, p)       
    else
        if mod(c4, p) == 0 
            r = - invmod(ZZ(12), p)*b2
        else 
            r = - invmod(ZZ(12)*c4, p)*(c6 + b2*c4)
        end
        t = - invmod(ZZ(2), p)* (a1*r + a3) 
        r = minimal_residue(r, p)
        t = minimal_residue(t, p)
    end
    
    trans = transform(E, [r, 0, t, 1])
    E = trans[1]
    
    a1 = num(E.coeff[1])
    a2 = num(E.coeff[2])
    a3 = num(E.coeff[3])
    a4 = num(E.coeff[4])
    a6 = num(E.coeff[5])
    
    b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)
    
    # test for types In, II, III, IV
    if mod(c4, p) != 0 
        if quadroots(1, a1, -a2, p) 
            cp = ZZ(n)
        elseif mod(n, 2) == 0 
            cp = ZZ(2)
        else 
            cp = ZZ(1)
        end
        
        Kp = "I$(n)"
        fp = ZZ(1)
        
        return E, Kp, fp, cp
    end
    
    if mod(a6, p^2) != 0 
        Kp = "II"
        fp = ZZ(n) 
        cp = ZZ(1)
        return E, Kp, fp, cp
    end
        
    if mod(b8, p^3) != 0 
        Kp = "III"
        fp = ZZ(n-1) 
        cp = ZZ(2) 
        return E, Kp, fp, cp
    end
    
    if mod(b6, p^3) != 0 
        if quadroots(1, divexact(a3, p), divexact(-a6, p^2), p) 
            cp = ZZ(3) 
        else 
            cp = ZZ(1) 
        end 
        Kp = "IV"
        fp = n - 2
        return E, Kp, fp, cp 
    end
    
    # change coordinates so that p | a1, a2; p^2 | a3, a4; p^3 | a6
    if p == 2
        s = minimal_residue(a2, 2)
        t = 2 * minimal_residue(divexact(a6, 4), 2)
    else
        s = -a1 * invmod(ZZ(2), p)
        t = -a3 * invmod(ZZ(2), p)
    end
    
    trans = transform(E, [0, s, t, 1])
    E = trans[1]
        
    a1 = num(E.coeff[1])
    a2 = num(E.coeff[2])
    a3 = num(E.coeff[3])
    a4 = num(E.coeff[4])
    a6 = num(E.coeff[5])
    
    b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)
    
    # set up auxililary cubic T^3 + bT^2 + cT + d
    b = divexact(a2, p)
    c = divexact(a4, p^2)
    d = divexact(a6, p^3)
    w = 27*d^2 - b^2*c^2 + 4*b^3*d - 18*b*c*d + 4*c^3
    x = 3*c - b^2
    
    # test for distinct roots: type I0*
    if mod(w, p) != 0
        Kp = "I0*"
        fp = ZZ(n - 4)
        cp = 1 + nrootscubic(b, c, d, p)
        return E, Kp, fp, cp
        
    # test for double root: type Im*
    elseif mod(x, p) != 0
        
        # change coordinates so that the double root is T = 0
        if p == 2
            r = c
        elseif p == 3
            r = b*c
        else 
            r = (b*c - 9*d) * invmod(ZZ(2)*x, p)
        end
        
        r = p * minimal_residue(r, p)
        
        trans = transform(E, [r, 0, 0, 1])
        E = trans[1]
        
        a1 = num(E.coeff[1])
        a2 = num(E.coeff[2])
        a3 = num(E.coeff[3])
        a4 = num(E.coeff[4])
        a6 = num(E.coeff[5])
        
        b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)
        
        # make a3, a4, a6 repeatedly more divisible by p
        m = 1
        mx = p^2
        my = p^2
        cp = ZZ(0)
        
        while cp == 0
            xa2 = divexact(a2, p)
            xa3 = divexact(a3, my)
            xa4 = divexact(a4, p*mx)
            xa6 = divexact(a6, mx*my)
            
            if mod(xa3^2 + 4*xa6, p) !=  0
                if quadroots(1, xa3, -xa6, p)
                    cp = ZZ(4)
                else 
                    cp = ZZ(2)
                end
                
            else
                if p == 2
                    t = my * xa6
                else
                    t = my * minimal_residue(-xa3*invmod(ZZ(2), p), p) 
                end
                
                trans = transform(E, [0, 0, t, 1])
                E = trans[1]
                
                a1 = num(E.coeff[1])
                a2 = num(E.coeff[2])
                a3 = num(E.coeff[3])
                a4 = num(E.coeff[4])
                a6 = num(E.coeff[5])
                
                b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)
                
                my = my*p
                m = m + 1
                xa2 = divexact(a2, p) 
                xa3 = divexact(a3, my) 
                xa4 = divexact(a4, p*mx) 
                xa6 = divexact(a6, mx*my) 
                
                if mod(xa4^2 - 4*xa2*xa6, p) != 0
                    if quadroots(xa2, xa4, xa6, p) 
                        cp = 4
                    else 
                        cp = 2
                    end
                 
                else 
                    if p == 2
                        r = mx * minimal_residue(xa6*xa2, 2) 
                    else 
                        r = mx * minimal_residue(-xa4 * invmod(2*xa2, p), p)
                    end
                    
                    trans = transform(E, [r, 0, 0, 1])
                    E = trans[1]
                    
                    a1 = num(E.coeff[1])
                    a2 = num(E.coeff[2])
                    a3 = num(E.coeff[3])
                    a4 = num(E.coeff[4])
                    a6 = num(E.coeff[5])
                    
                    b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)
                    
                    mx = mx*p 
                    m = m + 1
                end
            end
        end
        
        fp = n - m - 4
        Kp = "I$(m)*"
        
        return E, Kp, fp, cp
    
    else
        # Triple root case: types II*, III*, IV* or non-minimal
        # change coordinates so that the triple root is T = 0
        if p == 3
            rp = -d
        else 
            rp = -b * invmod(ZZ(3), p) 
        end
        
        r = p * minimal_residue(rp, p) 
        
        trans = transform(E, [r, 0, 0, 1])
        E = trans[1]
        
        a1 = num(E.coeff[1])
        a2 = num(E.coeff[2])
        a3 = num(E.coeff[3])
        a4 = num(E.coeff[4])
        a6 = num(E.coeff[5])
    
        b2, b4, b6, b8, c4, c6 = get_b_c_integral(E) 
        
        x3 = divexact(a3, p^2) 
        x6 = divexact(a6, p^4) 
        
        # Test for type IV*       
        if mod(x3^2 + 4* x6, p) != 0
            if quadroots(1, x3, -x6, p) 
                cp = 3
            else 
                cp = 1
            end
            Kp = "IV*"
            fp = ZZ(n - 6)
            
            return E, Kp, fp, cp 
            
        else
            if p == 2
                t = x6 
            else 
                t = x3 * invmod(ZZ(2), p) 
            end 
            
            t = -p^2 * minimal_residue(t, p) 
            
            trans = transform(E, [0, 0, t, 1])
            E = trans[1]
            
            a1 = num(E.coeff[1])
            a2 = num(E.coeff[2])
            a3 = num(E.coeff[3])
            a4 = num(E.coeff[4])
            a6 = num(E.coeff[5])
            
            b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)
            
            # Test for types III*, II*            
            if mod(a4, p^4) != 0 
                Kp = "III*"
                fp = ZZ(n - 7) 
                cp = ZZ(2)
                
                return E, Kp, fp, cp
            
            elseif mod(a6, p^6) != 0 
                Kp = "II*"
                fp = ZZ(n - 8) 
                cp = ZZ(1) 
                
                return E, Kp, fp, cp
            else
                E = transform(E, [0, 0, 0, p])[1]
                return tates_algorithm_local(E, p)
            end
        end
    end
 
end

doc"""
tates_algorithm_global(E::EllCrv{fmpz}) -> E::EllCrv{fmpz}
> returns a global minimal model for E using Tate's algorithm
"""
function tates_algorithm_global(E)
    delta = abs(num(disc(E)))
    fac = factor(delta)
    
    p_list = [i[1] for i in fac]
    p_list = sort(p_list)
    
    output = []
    
    # apply tates algorithm successively for all primes dividing the discriminant
    for p in p_list
        E = tates_algorithm_local(E, p)[1]
    end
    
    # reduce coefficients (see tidy_model)
    E = tidy_model(E)
    
    return E        
end

doc"""
tidy_model(E::EllCrv{fmpz}) -> E::EllCrv{fmpz}
> input: (minimal model of an) elliptic curve E with integer coefficients
> output: model of E with reduced coefficients such that a1, a3 in {0, 1} and a2 in {-1, 0, 1}
"""
function tidy_model(E)
    
    a1 = num(E.coeff[1])
    a2 = num(E.coeff[2])
    a3 = num(E.coeff[3])
    a4 = num(E.coeff[4])
    a6 = num(E.coeff[5])
    
    if mod(a1, 2) == 0
        s = -divexact(a1, 2)
    else
        s = -divexact(a1 - 1, 2)
    end
    
    if mod(-a2 + s*a1 + s^2, 3) == 0
        r = divexact(-a2 + s*a1 + s^2, 3)
    elseif mod(-a2 + s*a1 + s^2, 3) == 1
        r = divexact(-1 - a2 + s*a1 + s^2, 3)
    else
        r = divexact(1 - a2 + s*a1 + s^2, 3)
    end
    
    if mod(-a3 - r*a1, 2) == 0
        t = divexact(-a3 - r*a1, 2)
    else
        t = divexact(1 - a3 - r*a1, 2)
    end
    
    E = transform(E, [r, s, t, 1])[1]
    
    return E 
end


###### HEIGHTS ######
# local_height_finite, local_height_finite2, local_height_infinite, canonical_height
# is_independent
# agm, real_period
# get_b_integral, get_b_c_integral
# height, naive_height, points_with_bounded_height, torsion_points_via_height, independent_points_up_to

# computes the local height of a point P at a prime p, where the curve E is given by a minimal model, see book of cremona, p. 73
# does not really work for torsion points -> use local_height_finite2
function local_height_finite(P, p)
    
    # point at infinity has height 0
    if P.isinfinite
        return Float64(0)
    end
    
    E = P.parent
    x = P.coordx
    y = P.coordy
    
    a1 = num(E.coeff[1])
    a2 = num(E.coeff[2])
    a3 = num(E.coeff[3])
    a4 = num(E.coeff[4])
    a6 = num(E.coeff[5])
    
    b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)   
    delta = disc(E)
    
    N = ord_p(p, delta)
    A = ord_p(p, 3*x^2 + 2*a2*x + a4 - a1*y) 
    B = ord_p(p, 2*y + a1*x + a3)
    C = ord_p(p, 3*x^4 + b2*x^3 + 3*b4*x^2 + 3*b6*x + b8)
    M = min(B, N//2) 
    
    if (A <= 0) || (B <= 0) 
        L = max(0, -ord_p(p, x))
    elseif ord_p(p, c4) == 0
        L = M*(M - N)//N
    elseif C >= 3*B
        L = -2*B//3
    else 
        L = -C//4
    end
    
    return Float64(num(L))/Float64(den(L)) * log(Float64(p))
end

doc"""
local_height_finite2(P::EllCrvPt{fmpq}, p::Int) -> Float64
> Computes the local height of $P$ modulo the prime p.
"""
function local_height_finite2(P, p)
    
    # point at infinity has height 0
    if P.isinfinite
        return Float64(0)
    end
    
    E = P.parent
    x = P.coordx
    y = P.coordy
    
    a1 = num(E.coeff[1])
    a2 = num(E.coeff[2])
    a3 = num(E.coeff[3])
    a4 = num(E.coeff[4])
    a6 = num(E.coeff[5])
    
    b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)   
    
    delta = disc(E)

    A = 3*x^2 + 2*a2*x + a4 - a1*y
    B = 2*y + a1*x + a3 # = psi2(P)
    C = 3*x^4 + b2 * x^3 + 3*b4*x^2 + 3*b6*x + b8 # = psi3(P)

    L = 0

    if (A != 0 && ord_p(p, A) <= 0) || (B != 0 && ord_p(p, B) <= 0)
      if x != 0
        L = max(0, -ord_p(p, x))
      else
        L = 0
      end
    elseif (c4 != 0 && ord_p(p, c4) == 0)
        N = ord_p(p, delta)
        if B == 0
          M = N//2
          L = M*(M - N)//N
        else
          M = min(ord_p(p, B), N//2)
          L = M*(M - N)//N
        end
    elseif ( C == 0 || ( C != 0 && B != 0 && ord_p(p, C) >= 3*ord_p(p, B)))
          L = -2*ord_p(p, B)//3
    else
          L = -ord_p(p, C)//4
    end
    
    return Float64(num(L))/Float64(den(L)) * log(Float64(p))
end

doc"""
    local_height_infinite(P::EllCrvPt, d :: Int) -> Float64
> Computes the real local height of a point P on an elliptic curve E given by a minimal model.
> Parameter d: number of decimal places required; default setting: d = 20.
"""
# p. 74 in cremona's book
function local_height_infinite(P, d = 20)
    E = P.parent
    x = P.coordx
    
    a1 = num(E.coeff[1])
    a2 = num(E.coeff[2])
    a3 = num(E.coeff[3])
    a4 = num(E.coeff[4])
    a6 = num(E.coeff[5])
    
    b2, b4, b6, b8 = get_b_integral(E)   
    
    H = max(4, abs(b2), 2*abs(b4), 2*abs(b6), abs(b8))
    b2prime = b2 - ZZ(12)
    b4prime = b4 - b2 + ZZ(6)
    b6prime = b6 - 2*b4 + b2 - 4
    b8prime = b8 - 3*b6 + 3*b4 - b2 + 3
    
    N = ceil( (5/3)*Float64(d) + (1/2) + (3/4)*log(7 + (4/3)*log(Float64(H))) )
    
    if abs(Float64(num(x))/Float64(den(x))) < 0.5
        t = 1/((Float64(num(x))/Float64(den(x))) + 1)
        beta = 0
    else
        t = 1/((Float64(num(x))/Float64(den(x))))
        beta = 1
    end
    
    mu = -log(abs(t))
    f = 1
    
    for n in 0:N
        f = f/4
        
        if beta == 1
            w = Float64(b6)*t^4 + 2*Float64(b4)*t^3 + Float64(b2)*t^2 + 4*t
            z = 1 - Float64(b4)*t^2 - 2*Float64(b6)*t^3 - Float64(b8)*t^4
            zw = z + w
        else
            w = Float64(b6prime)*t^4 + 2*Float64(b4prime)*t^3 + Float64(b2prime)*t^2 + 4*t
            z = 1 - Float64(b4prime)*t^2 - 2*Float64(b6prime)*t^3 - Float64(b8prime)*t^4
            zw = z - w
        end
                
        if abs(w) <= 2*abs(z)
            mu = mu + f*log(abs(z))
            t = w/z
        else
            mu = mu + f*log(abs(zw))
            t = w/zw
            beta = 1 - beta
        end
    end
    
    return mu              
end

doc"""
    canonical_height(P::EllCrvPt) -> Float64
> Computes the canonical height of a point $P$. 
"""
# see Cremona, p. 75
function canonical_height(P)
    
    if P.isinfinite == true
        return Float64(0)
    end
    
    E = P.parent
    x = P.coordx
    delta = disc(E)
    d = den(x)
    
    h = local_height_infinite(P) + log(Float64(d))
    
    fac = factor(num(delta))
    p_list = [i[1] for i in fac]
    
    for p in p_list
        if mod(d, p) != 0
            h = h + local_height_finite2(P, p)
        end 
    end
    
    return h
end

doc"""
    is_independent(P::Array{EllCrvPt}) -> Bool
>   Tests whether a given set of points P is linearly independent.
>   Returns true if it is independent, otherwise false.
"""
# see Robledo, p. 47
function is_independent(P)
    epsilon = 10.0^(-8)
    r = length(P)
    M = Matrix{Float64}(r,r)
    
    for i in 1:r
        for j in 1:r
            M[i,j] = canonical_height(P[i] + P[j]) - canonical_height(P[i]) - canonical_height(P[j])
        end
    end
    
    determinante = det(M) 
    
    if abs(determinante) < epsilon 
        return false
    else 
        return true
    end
end

doc"""
    agm(x::Float64, y::Float64, e::Int) -> Float64
>   Returns the arithmetic-geometric mean of x and y.
"""
function agm{T,U<:Integer}(x::T, y::T, e::U=5)
    0 < y && 0 < y && 0 < e || throw(DomainError())
    err = e*eps(x)
    (g, a) = extrema([x, y])
    while err < (a - g)
        ap = a
        a = 0.5*(a + g)
        g = sqrt(ap*g)
    end
    return a
end


doc"""
    real_period(E::EllCrv{fmpz}) -> Float64
>   Returns the real period of an elliptic curve E with integer coefficients.
"""
# see Cohen
function real_period(E)
    a1 = num(E.coeff[1])
    a2 = num(E.coeff[2])
    a3 = num(E.coeff[3])
    a4 = num(E.coeff[4])
    a6 = num(E.coeff[5])
    
    b2, b4, b6, b8 = get_b_integral(E)
    
    delta = disc(E)
    f(x) = x^3 + (Float64(b2)/4)*x^2 + (Float64(b4)/2)*x + (Float64(b6)/4)
    root = fzeros(f)

    if delta < 0 # only one real root 
        e1 = root[1]
        a = 3*e1 + (Float64(b2)/4)
        b = sqrt(3*e1^2 + (Float64(b2)/2)*e1 + (Float64(b4)/2))
        lambda = 2*pi / agm(2*sqrt(b), sqrt(2*b + a)) 
    else
        root = sort(root)
        e1 = root[1]
        e2 = root[2]
        e3 = root[3]
        w1 = pi / agm(sqrt(e3-e1), sqrt(e3-e2))
        lambda = 2*w1
    end
    
    return lambda
end


doc"""
    get_b_integral(E::EllCrv{fmpz}) -> Nemo.fmpz
> Computes the invariants b2, b4, b6, b8 of an elliptic curve E with integer coefficients.
"""
function get_b_integral(E)
    a1 = num(E.coeff[1])
    a2 = num(E.coeff[2])
    a3 = num(E.coeff[3])
    a4 = num(E.coeff[4])
    a6 = num(E.coeff[5])
    
    b2 = a1^2 + 4*a2
    b4 = a1*a3 + 2*a4
    b6 = a3^2 + 4*a6
    b8 = a1^2*a6 - a1*a3*a4 + 4*a2*a6 + a2*a3^2 - a4^2
    
    return b2,b4,b6,b8
end


doc"""
    get_b_c_integral(E::EllCrv{fmpz}) -> Nemo.fmpz
> Computes the invariants b2, b4, b6, b8, c4, c6 of an elliptic curve E with integer coefficients.
"""
function get_b_c_integral(E)
    a1 = num(E.coeff[1])
    a2 = num(E.coeff[2])
    a3 = num(E.coeff[3])
    a4 = num(E.coeff[4])
    a6 = num(E.coeff[5])
    
    b2 = a1^2 + 4*a2
    b4 = a1*a3 + 2*a4
    b6 = a3^2 + 4*a6
    b8 = a1^2*a6 - a1*a3*a4 + 4*a2*a6 + a2*a3^2 - a4^2
    
    c4 = b2^2 - 24*b4
    c6 = -b2^3 + 36*b2*b4 - 216*b6
    
    return b2,b4,b6,b8,c4,c6
end

doc"""
    height(x::fmpq) -> Float64
> Computes the height of a rational number x.
"""
function height(x::fmpq) 
    a = Float64(num(x))
    b = Float64(den(x)) 
    return log(max(abs(a),abs(b))) 
end

# every rational point is given by P = (a/c^2, b/c^3), gcd(a,c) = gcd(b,c) = 1. then h(P) = max(|a|, c^2)

doc"""
    naive_height(P::EllCrvPt{fmpq}) -> Float64
> Computes the naive height of a point $P$.

## Example

E = EllipticCurve([1,2,3,4,0])
P = E([])
naive_height(P)
"""
function naive_height(P)
    x = P.coordx
    a = Float64(num(x))
    c2 = Float64(den(x))
    
    h = log(max(abs(a), abs(c2)))
    return h
end

doc"""
    points_with_bounded_height(E:EllCrv, B::Int) -> Array{EllCrvPt}
> Computes all rational points on a curve E with integer coefficients which have naive height <= B.
"""
# p.75 Cremona
function points_with_bounded_height(E, B)
    a1 = num(E.coeff[1])
    a2 = num(E.coeff[2])
    a3 = num(E.coeff[3])
    a4 = num(E.coeff[4])
    a6 = num(E.coeff[5])
    
    # 2-torsion
    f(x) = x^3 + Float64(a2)*x^2 + Float64(a4)*x + Float64(a6)
    torsiontwo = sort(fzeros(f))
    x0 = torsiontwo[1]
    
    R, z = PolynomialRing(ZZ, "z")
    
    points = []
    
    # iterate over possible values for c and a
    k = Int(floor(exp(Float64(B)/2)))
    for c in 1:k
        for a in Int(floor(max(c^2*x0, -exp(Float64(B))))):Int(floor(exp(Float64(B))))
            if gcd(a, c) == 1
                # look for possible values for b; they are the zeros of g
                g = z^2 + (a1*c*a + a3*c^3)*z - (a^3 + a2*c^2*a^2 + a4*c^4*a + a6*c^6)
                zeros = zeros(g)
                
                if length(zeros) != 0
                    for b in zeros
                        P = E([QQ(a,c^2), QQ(b, c^3)])
                        push!(points, P)
                    end
                end
                
            end
        end
    end
   
    return points
end

doc"""
torsion_points_via_height(E::EllCrv{fmpz}) ->  Array{EllCrvPt}
> Returns the rational torsion points of a curve E with integer coefficients. 
"""
function torsion_points_via_height(E)
    
    if E.short == true
        E = EllipticCurve([0, 0, 0, E.coeff[1], E.coeff[2]])
    end
    
    jay = j(E)
    hj = height(jay) # height of the j-invariant
    jfloat = Float64(num(jay))/Float64(den(jay))
    
    delta = num(disc(E))
    b2, b4, b6, b8 = get_b_integral(E)
    twostar = 2
    if b2 == 0
        twostar = 1
    end
    
    # mu(E)
    mu = (1/6)*( log(abs(Float64(delta))) + log(max(1, abs(jfloat))) ) + log(max(1, abs(Float64(b2)/12))) + log(twostar)
    
    B = (1/12)*hj + mu + 1.922
    
    # all torsion points have naive height <= B, see Cremona, p. 77
    torsion_candidates = points_with_bounded_height(E, B)
    torsion_points = [infinity(E)]
    
    # check which points of the candidates are torsion points (order of a torsion point is <= 12)
    for P in torsion_candidates
        istorsion = false
        k = 7
        while (istorsion == false) && (k <= 12)
            if (k*P).isinfinite == true
                istorsion = true
            end
            k = k + 1
        end
        
        if istorsion == true
            push!(torsion_points, P)
        end
    end
    
    return torsion_points
end

doc"""
independent_points_up_to(E::EllCrv{fmpq}, B::Int) -> Array{EllCrvPt}
> Returns a maximal set of independent points with naive height <= B
"""
function independent_points_up_to(E,B)
    
    if E.short == true
        E = EllipticCurve([0, 0, 0, E.coeff[1], E.coeff[2]])
    end
    
    points = points_with_bounded_height(E,B)
    counter = 1
    M_ind = Matrix{Float64}(0,0) 
    M_cand = Matrix{Float64}(1,1)
    points_ind = []
    
    for p in points
        istorsion = false
        i = 7
        while (i < 13) && (istorsion == false)
            if (i*p).isinfinite == true
                istorsion = true
            end
            i = i + 1
        end
        
        if istorsion == true
            continue
        end
        
        push!(points_ind, p)
        for i = 1:length(points_ind)
            M_cand[i, counter] = canonical_height(points_ind[i] + points_ind[counter]) - canonical_height(points_ind[i]) - canonical_height(points_ind[counter])
            M_cand[counter, i] = M_cand[i, counter]
        end
                
        if abs(det(M_cand)) < 10.0^(-8)
            pop!(points_ind)
        else
            counter = counter + 1
            M_ind = M_cand 
            M_cand = Matrix{Float64}(size(M_cand)[1] + 1, size(M_cand)[1] + 1)
            
            for i = 1:size(M_cand)[1] - 1
                for j = 1:size(M_cand)[1] - 1
                    M_cand[i, j] = M_ind[i, j]
                end
            end
        end
        
    end
    
    return points_ind                
end

