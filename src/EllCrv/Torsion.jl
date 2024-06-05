################################################################################
#
#          EllipticCurve/Torsion.jl : Computing torsion points on elliptic curves
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
#  Order of a point
#
################################################################################

@doc raw"""
    order(P::EllipticCurvePoint{AbsSimpleNumFieldElem}) -> ZZRingElem

Returns the order of the point $P$ or $0$ if the order is infinite.
"""
function order(P::EllipticCurvePoint{T}) where T<:Union{AbsSimpleNumFieldElem, QQFieldElem}
  if T==QQFieldElem
    N = 12
  else
    E = parent(P)
    N = torsion_bound(E, 20)
  end

  Q = P
  for i in 1:N
    if !is_finite(Q)
      return ZZRingElem(i)
    end
    Q = Q + P
  end

  return ZZRingElem(0)
end

################################################################################
#
#  Test if point is torsion point
#
################################################################################

@doc raw"""
    is_torsion_point(P::EllipticCurvePoint{QQFieldElem}) -> Bool

Returns whether the point $P$ is a torsion point.
"""
function is_torsion_point(P::EllipticCurvePoint{T}) where T <: Union{AbsSimpleNumFieldElem,QQFieldElem}
  o = order(P)
  return o != 0
end

@doc raw"""
    is_torsion_point(P::EllipticCurvePoint{fqPolyRepFieldElem}) -> Bool

Returns whether the point $P$ is a torsion point.
"""
function is_torsion_point(P::EllipticCurvePoint{fqPolyRepFieldElem})
  return true
end

################################################################################
#
#  Torsion points over QQ
#
################################################################################

# via theorem of Lutz-Nagell
@doc raw"""
    torsion_points_lutz_nagell(E::EllipticCurve{QQFieldElem}) -> Vector{EllipticCurvePoint}

Computes the rational torsion points of an elliptic curve using the
>Lutz-Nagell theorem.
"""
function torsion_points_lutz_nagell(F::EllipticCurve{QQFieldElem})

  if F.short == false
    (G, trafo, ruecktrafo) = short_weierstrass_model(F)
  else
    G = F
  end

  # transform the curve to an equivalent one with integer coefficients, if necessary
  (E, trafo_int, trafo_rat) = integral_model(G)

  res = [infinity(E)]
  d = discriminant(E)

  # Lutz-Nagell: necessary: y = 0 or y^2 divides d

  ycand = collect(squaredivisors(numerator(d))) # candidates for y-coordinate

  push!(ycand,0)

  pcand = Tuple{ZZRingElem, ZZRingElem}[] # candidates for torsion points

  Zx, x = polynomial_ring(FlintZZ, "x")

  _, _, _, a4, a6 = a_invariants(E)

  # Lutz-Nagell: coordinates of torsion points need to be in ZZ
  for i = 1:length(ycand)
    # are there corresponding integer x-values?
    xcand = zeros(x^3 + numerator(a4)*x + numerator(a6) - ycand[i]^2)
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
      Q = P
      for j = 2:12
        Q = Q + P
        if is_infinite(Q)
          push!(res, P)
          break
        end
      end
    end
  end

  torsionpoints = res

  #if F.short == false
  #  for i = 1:length(torsionpoints)
  #    torsionpoints[i]= ruecktrafo(trafo_rat(torsionpoints[i]))
  #  end
  #else
  #  for i = 1:length(torsionpoints)
  #    torsionpoints[i] = trafo_rat(torsionpoints[i])
  #  end
  #end
  return torsionpoints
end

# via division polynomials
@doc raw"""
    torsion_points_division_poly(E::EllipticCurve{QQFieldElem}) -> Array{EllipticCurvePoint}

Computes the rational torsion points of a rational elliptic curve $E$ using
division polynomials.
"""
function torsion_points_division_poly(F::EllipticCurve{QQFieldElem})

  # if necessary, transform curve into short form
  if F.short == false
    (G, trafo, ruecktrafo) = short_weierstrass_model(F)
  else
    G = F
  end

  # transform the curve to an equivalent one with integer coefficients, if necessary
  (E, trafo_int, trafo_rat) = integral_model(G)

  # curve has integer coefficients
  _, _, _, A, B = map(numerator, a_invariants(E))

  torsionpoints = [infinity(E)]

  # points of order 2 (point has order 2 iff y-coordinate is zero)
  # (note: these points are not detected by the division polynomials)

  Zx, x = polynomial_ring(FlintZZ, "x")

  s = zeros(x^3 + A*x + B) # solutions of x^3 + Ax + B = 0
  if length(s) != 0
    for i = 1:length(s)
      P = E([s[i], 0])
      push!(torsionpoints, P)
    end
  end

  # Mazur: order of torsion point is at most 12
  for n = 7 : 12 # points of smaller order will also be found
    Psi = division_polynomial_univariate(E,n)[1]
    z = roots(Psi)

    if length(z) == 0
      continue
    end

    # z contains candidates for x-coordinates of torsion points
    for i = 1:length(z)

      # are there corresponding integer-square y-coordinates?
      if isinteger(z[i])
        zi = numerator(z[i])
        ysquarecand = zi^3 + A*zi + B

        if ysquarecand < 0
          continue
        end

        a = isqrtrem(ysquarecand)

        if a[1] == 0 # then ysquarecand = 0, so have found torsion point
          P = E([zi, ysquarecand])

        # if not already contained in torsionpoints, add P
          if !(P in torsionpoints)
            push!(torsionpoints, P)
          end

          continue
        end

      # now ysquarecand > 0
        if a[2] == 0 # then y is a square of an integer
          P = E([zi, a[1]])
          Q = E([zi, -a[1]])

        # if not already contained in torsionpoints, add P and Q
          if !(P in torsionpoints)
            push!(torsionpoints, P)
            push!(torsionpoints, Q)
          end
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

  return torsionpoints::Vector{EllipticCurvePoint{QQFieldElem}}
end

# function for users
@doc raw"""
    torsion_points(E::EllipticCurve{QQFieldElem}) -> Vector{EllipticCurvePoint{QQFieldElem}}

Returns the rational torsion points of $E$.
"""
function torsion_points(E::EllipticCurve{QQFieldElem})
  if isdefined(E, :torsion_points)
    return E.torsion_points::Vector{EllipticCurvePoint{QQFieldElem}}
  end

  t = torsion_points_division_poly(E::EllipticCurve{QQFieldElem})
  E.torsion_points = t
  return t
end

################################################################################
#
#  Torsion structure
#
################################################################################

@doc raw"""
    torsion_structure(E::EllipticCurve{QQFieldElem}) -> (A::Vector{ZZRingElem},
                                           B::Vector{EllipticCurvePoint{QQFieldElem}}

Compute the structure of the rational torsion group of an elliptic curve $E$.
Then `A` is an array with `A = [n]` resp. `A = [n,m]` such that the
rational torsion of $E$ is isomorphic to $\mathbf Z/n\mathbf Z$ resp.
$\mathbf Z/n\mathbf Z \times \mathbf Z/m\mathbf Z$.
And `B` is an array of points with `B = [P]` and $P$ has order $n$ resp.
`B = [P, Q]` and $P$ has order $n$, $Q$ has order $m$.
"""
function torsion_structure(E::EllipticCurve{QQFieldElem})
  T = torsion_points(E)
  grouporder = length(T)
  orders = ZZRingElem[]

  for i in 1:grouporder
    push!(orders, 0)
  end

 # determine orders of group elements
  for i in 1:grouporder
    j = 1
    while (j < 13) && (orders[i] == 0)
      if (j*T[i]).is_infinite == true
        orders[i] = j
      end
    j = j + 1
    end
  end

  # find generators
  if in(grouporder, orders) == true # is the group cyclic?
    k = something(findfirst(isequal(grouporder), orders), 0)
    return ZZRingElem[grouporder], [T[k]]
  else # group not cyclic
    m = div(grouporder, 2)
    k1 = something(findfirst(isequal(2), orders), 0)
    k2 = something(findlast(isequal(m), orders), 0) # findlast to get different points if m = 2
    points = [T[k1], T[k2]]
  return (ZZRingElem[2, m], points)
  end
end

################################################################################
#
#  Torsion over more general fields
#
################################################################################

@doc raw"""
    torsion_bound(E::EllipticCurve{AbsSimpleNumFieldElem}, n::Int) -> ZZRingElem


Bound the order of the torsion subgroup of $E by considering
the order of the reduction of $E$ modulo $n$ distinct primes
with good reduction
"""
function torsion_bound(E::EllipticCurve{AbsSimpleNumFieldElem}, n::Int)
  K = base_field(E)
  R = ring_of_integers(K)
  badp = bad_primes(E)
  #First prime is 3
  p = next_prime(2)
  i = 0
  bound = 0
  disc_K = ZZ(discriminant(K))
  disc_E = R(discriminant(E))
  while i < n
    L = prime_ideals_over(R, p)
    for P in L
      if !divides(disc_K, p)[1] && !divides(disc_E, R(p))[1]
        i=i+1
        EP = modp_reduction(E,P)
        bound = gcd(bound, order(EP))
      end
    end
    p = next_prime(p)
  end
  return(ZZRingElem(bound))
end

################################################################################
#
#  p^r-Torsion part
#
################################################################################

#Adapted from Sage: ell_generic.py
@doc raw"""
    pr_torsion_basis(E::EllipticCurve{AbsSimpleNumFieldElem}, p::ZZRingElem, r = Int) -> Vector{EllipticCurvePoint}

Compute a basis for the p-power torsion subgroup. When r is given the algorithm stops searching after
having found a basis that spans p^r points.
"""
function pr_torsion_basis(E::EllipticCurve{T}, p, r = typemax(Int)) where T <: Union{AbsSimpleNumFieldElem, QQFieldElem}

  if !is_prime(p)
    error("p should be a prime number")
  end

  #First we find all the p-torsion points
  p_torsion = division_points(infinity(E), p)
  p_rank = Int(log(ZZRingElem(p), ZZRingElem(length(p_torsion))))

  if p_rank == 0
    return Tuple{elem_type(E), Int}[]
  elseif p_rank == 1
  #If the dimension of the p-torsion is 1.
    P = p_torsion[1]
    if is_infinite(P)
      P=p_torsion[2]
    end
    k = 1
    if r==1
      return [(P, k)]
    end

    #We keep dividing P by p until we have found a generator for the p^r-torsion.
    pts = division_points(P, p)

    while length(pts) > 0
      k += 1
      P = pts[1]
      if r <= k
        return [(P, k)]
      end
      points = division_points(P, p)
    end
    return [(P, k)]
  else  #The p-torsion has rank 2
    P1 = popfirst!(p_torsion)
    while is_infinite(P1)
      P1 = popfirst!(p_torsion)
    end
    P2 = popfirst!(p_torsion)
    #We find a linearly independent basis for the p-torsion.
    while linearly_dependent(P1, P2)
     P2 = popfirst!(p_torsion)
    end

    k = 1
    log_order = 2
    if r<= 2
      return [(P1, 1),(P2, 1)]
    end

    #We keep dividing P1 and P2 by p until this is no longer possible
    pts1 = division_points(P1, p)
    pts2 = division_points(P2, p)
    while length(pts1) > 0 && length(pts2) > 0
      k += 1
      P1 = pts1[1]
      P2 = pts2[1]
      log_order += 2
      if r<=log_order
        return [(P1, k),(P2, k)]
      end
      pts1 = division_points(P1, p)
      pts2 = division_points(P2, p)
    end
  #Now k is the maximal integer for which P1,P2 are a basis
  #for the p^k torsion

  #But there could still be a p^k torsion point which can be divided
  #further, so we search for a linear combination of P1 and P2 to
  #see if this is the case.

    if length(pts1) > 0
      pts = pts1
    elseif length(pts2) > 0
      P1, P2 = P2, P1
      pts = pts2
    else
      for Q in elem_type(E)[P1+a*P2 for a in (1:p-1)]
          # Q runs through P1+a*P2 for a=1,2,...,p-1
        pts = division_points(Q, p)
        if length(pts) > 0
          P1 = Q
          break
        end
      end
    end
    if length(pts)==0
      return [(P1, k), (P2, k)]
    end
  #If we have found a P1 that we can divide further,
  #we continue trying to divide P1 by p. If we fail
  #we replace P1 again by a linear combination P1+a*P2 for
  #some a in [1..p-1]. We continue with this until we can no longer
  #divide any linear combination and we have found the full torsion structure
  #Z/p^n x Z/p^k for some n >k.

    n = k
    while true
      P1 = pts[1]
      n += 1
      log_order += 1
      if r <= log_order
        return [(P1, n),(P2, k)]
      end

      pts = division_points(P1, p)
      if length(pts) == 0
        for Q in elem_type(E)[P1+a*P2 for a in (1:p-1)]
        # Q runs through P1+a*P2 for a=1,2,...,p-1
          pts = division_points(Q, p)
          if length(pts) > 0
            break
          end
        end
        if length(pts) == 0
          return [(P1, n), (P2, k)]
        end
      end
    end
  end
end

#Returns [m, n] with m >n. This is inconsistent with the way torsion_structure
#returns elements for EllipticCurve over QQ.
@doc raw"""
    torsion_structure(E::EllipticCurve{AbsSimpleNumFieldElem}) -> (A::Vector{ZZRingElem},
                                           B::Vector{EllipticCurvePoint{AbsSimpleNumFieldElem}}

Compute the structure of the rational torsion group of an elliptic curve $E$.
Then `A` is an array with `A = [n]` resp. `A = [n,m]` such that the
rational torsion of $E$ is isomorphic to $\mathbf Z/n\mathbf Z$ resp.
$\mathbf Z/n\mathbf Z \times \mathbf Z/m\mathbf Z$.
And `B` is an array of points with `B = [P]` and $P$ has order $n$ resp.
`B = [P, Q]` and $P$ has order $n$, $Q$ has order $m$.
"""
function torsion_structure(E::EllipticCurve{AbsSimpleNumFieldElem})

  T1 = T2 = infinity(E)
  k1 = k2 = ZZRingElem(1)
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

  structure = ZZRingElem[]

  if k1 == 1
    structure = [ZZRingElem(1)]
    gens = [infinity(E)]
  elseif k2 == 1
    structure = [ZZRingElem(k1)]
    gens = [T1]
  else
    structure = [ZZRingElem(k1), ZZRingElem(k2)]
    gens = [T1, T2]
  end
  return structure, gens
end


################################################################################
#
#  Misc
#
################################################################################

function linearly_dependent(P1::EllipticCurvePoint{T}, P2::EllipticCurvePoint{T}) where T

#if !istorsion_point(P1)||!istorsion_point(P2)
#  throw(DomainError, "Points need to be torsion_points")
#end

  A = P1
  B = P2

  while is_finite(A)
    while is_finite(B)
      if is_infinite(A+B)
        return true
      end
      B+=P2
    end
    A+=P1
    B+=P2
  end
  return false
end

################################################################################
#
#  Division polynomials
#
################################################################################
"""
    division_polynomial_univariate(E::EllipticCurve, n::Int, [x]) -> Poly

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
function division_polynomial_univariate(E::EllipticCurve, n::S, x = polynomial_ring(base_field(E),"x")[2]) where S<:Union{Integer, ZZRingElem}

  R = parent(x)



  if is_short_weierstrass_model(E)
    n == 0 ? poly = 0 : poly = divpol_g_short(E,n,x)
    if mod(n,2) == 0
      _, _, _, A, B = a_invariants(E)
      twotorsfactor = 4*(x^3+A*x+B)
    else
      twotorsfactor = one(R)
    end
  else
    n == 0 ? poly = 0 : poly = divpol_g(E,n,x)
      if mod(n,2) == 0
        b2, b4, b6 = b_invariants(E)
        twotorsfactor = 4*x^3+b2*x^2+2*b4*x+b6
      else
        twotorsfactor = one(R)
      end
  end
  return twotorsfactor*poly, poly, twotorsfactor
end


"""
    division_polynomial(E::EllipticCurve, n::Int, x, y) -> Poly

Compute the n-th division polynomial of an elliptic curve defined over a field
k following Mazur and Tate. When x and or y are given the output is
automatically evaluated using the given values.
"""
function division_polynomial(E::EllipticCurve, n::S, x = polynomial_ring(base_field(E),"x")[2], y = polynomial_ring(parent(x),"y")[2]) where S<:Union{Integer, ZZRingElem}
  R = parent(y)

  if n == 0
    return zero(R)
  end

  if is_short_weierstrass_model(E)
     if mod(n,2) == 0
      return 2*y*divpol_g_short(E,n,x)
    else
      return R(divpol_g_short(E,n,x))
    end
  else
    a1, _, a3 = a_invariants(E)
    if mod(n,2) == 0
      return (2*y + a1*x + a3)*divpol_g(E,n,x)
    else
      return R(divpol_g(E,n,x))
    end
  end
end


function divpol_g_short(E::EllipticCurve, n::S, x = polynomial_ring(base_field(E),"x")[2]) where S<:Union{Integer, ZZRingElem}

  Kx = parent(x)
  _, _, _, A, B = a_invariants(E)

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

function divpol_g(E::EllipticCurve, n::S, x = polynomial_ring(base_field(E),"x")[2]) where S<:Union{Integer, ZZRingElem}

  Kx = parent(x)

  b2, b4, b6, b8 = E.b_invariants
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

