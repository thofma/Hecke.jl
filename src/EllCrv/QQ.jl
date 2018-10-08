################################################################################
#
#             EllCrv/QQ.jl : Rational elliptic curves
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

export integral_model, istorsion_point, laska_kraus_connell, minimal_model,
       order, tates_algorithm_global, tates_algorithm_local, tidy_model,
       torsion_points_division_poly, torsion_points_lutz_nagell,
       torsion_points, torsion_structure

################################################################################
#
#  Order of a point
#
################################################################################

@doc Markdown.doc"""
***
    order(P::EllCrvPt{fmpq}) -> fmpz

Returns the order of the point $P$ or $0$ if the order is infinite.
"""
function order(P::EllCrvPt{fmpq})
  Q = P
  for i in 1:12
    if !isfinite(Q)
      return fmpz(i)
    end
    Q = Q + P
  end

  return fmpz(0)
end

################################################################################
#
#  Test if point is torsion point
#
################################################################################

@doc Markdown.doc"""
    istorsion_point(P::EllCrvPt{fmpq}) -> fmpz

> Returns whether the point $P$ is a torsion point.
"""
function istorsion_point(P::EllCrvPt{fmpq})
  o = order(P)
  return o != 0
end

################################################################################
#
#  Torsion points
#
################################################################################

# via theorem of Lutz-Nagell
@doc Markdown.doc"""
***
    torsion_points_lutz_nagell(E::EllCrv{fmpq}) -> Array{EllCrvPt, 1}

> Computes the rational torsion points of an elliptic curve using the
>Lutz-Nagell theorem.
"""
function torsion_points_lutz_nagell(F::EllCrv{fmpq})

  if F.short == false
    (G, trafo, ruecktrafo) = short_weierstrass_model(F)
  else
    G = F
  end

  # transform the curve to an equivalent one with integer coefficients, if necessary
  (E, trafo_int, trafo_rat) = integral_model(G)

  res = [infinity(E)]
  d = disc(E)

  # Lutz-Nagell: necessary: y = 0 or y^2 divides d

  ycand = collect(squaredivisors(numerator(d))) # candidates for y-coordinate

  push!(ycand,0)

  pcand = Tuple{fmpz, fmpz}[] # candidates for torsion points

  Zx, x = PolynomialRing(FlintZZ, "x")

  # Lutz-Nagell: coordinates of torsion points need to be in ZZ
  for i = 1:length(ycand)
    # are there corresponding integer x-values?
    xcand = zeros(x^3 + (numerator(E.coeff[1]))*x + (numerator(E.coeff[2])) - ycand[i]^2)
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
        if isinfinite(Q)
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
@doc Markdown.doc"""
***
    torsion_points_division_poly(E::EllCrv{fmpq}) -> Array{EllCrvPt}

> Computes the rational torsion points of an rational elliptic $E$ curve using
> division polynomials.
"""
function torsion_points_division_poly(F::EllCrv{fmpq})

  # if necessary, transform curve into short form
  if F.short == false
    (G, trafo, ruecktrafo) = short_weierstrass_model(F)
  else
    G = F
  end

  # transform the curve to an equivalent one with integer coefficients, if necessary
  (E, trafo_int, trafo_rat) = integral_model(G)

  # check whether we already know the torsion points or not
  if isdefined(E, :torsion_points)
    if F.short == false
      F.torsion_points = EllCrvPt{fmpq}[]
      for i = 1:length(E.torsion_points)
        push!(F.torsion_points, ruecktrafo(trafo_rat(E.torsion_points[i])))
      end
    else
      F.torsion_points = EllCrvPt{fmpq}[]
      for i = 1:length(E.torsion_points)
        push!(F.torsion_points, trafo_rat(E.torsion_points[i]))
      end
    end
    return F.torsion_points::Array{EllCrvPt{fmpq}, 1}
  end

  # curve has integer coefficients
  A = numerator(E.coeff[1])
  B = numerator(E.coeff[2])

  torsionpoints = [infinity(E)]

  # points of order 2 (point has order 2 iff y-coordinate is zero)
  # (note: these points are not detected by the division polynomials)

  Zx, x = PolynomialRing(FlintZZ, "x")

  s = zeros(x^3 + A*x + B) # solutions of x^3 + Ax + B = 0
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

  return torsionpoints::Array{EllCrvPt{fmpq}, 1}
end

# function for users
@doc Markdown.doc"""
***
    torsion_points(E::EllCrv{fmpq}) -> Array{EllCrvPt{fmpq}, 1}

> Returns the rational torsion points of $E$.
"""
function torsion_points(E::EllCrv{fmpq})
  if isdefined(E, :torsion_points)
    return E.torsion_points::Array{EllCrvPt{fmpq}, 1}
  end

  t = torsion_points_division_poly(E::EllCrv{fmpq})
  E.torsion_points = t
  return t
end

################################################################################
#
#  Torsion structure
#
################################################################################

@doc Markdown.doc"""
***
    torsion_structure(E::EllCrv{fmpq}) -> (A::Array{fmpz, 1},
                                           B::Array{EllCrvPt{fmpq}, 1}

> Computes the structure of the rational torsion group of an elliptic curve $E$.
> Then `A` is an array with `A = [n]` resp. `A = [n,m]` such that the
> rational torsion of $E$ is isomorphic to $\mathbf Z/n\mathbf Z$ resp.
> $\mathbf Z/n\mathbf Z \times \mathbf Z/m\mathbf Z$.
> And `B` is an array of points with `B = [P]` and $P$ has order $n$ resp.
> `B = [P, Q]` and $P$ has order $n$, $Q$ has order $m$.
"""
function torsion_structure(E::EllCrv{fmpq})
  T = torsion_points(E)
  grouporder = length(T)
  orders = fmpz[]

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
    k = something(findfirst(isequal(grouporder), orders), 0)
    return (fmpz[grouporder], [T[k]])
  else # group not cyclic
    m = div(grouporder, 2)
    k1 = something(findfirst(isequal(2), orders), 0)
    k2 = something(findlast(isequal(m), orders), 0) # findlast to get different points if m = 2
    points = [T[k1], T[k2]]
  return (fmpz[2, m], points)
  end
end

################################################################################
#
#  Changing the model
#
################################################################################

@doc Markdown.doc"""
***
integral_model(E::EllCrv{fmpq}) -> (F::EllCrv{fmpz}, function, function)

> Given an elliptic curve $E$ over $\mathbf Q$ in short form, returns an
> isomorphic curve $F$ with model over $\mathbf Z$. The second and third
> return values are the isomorpisms $E \to F$ and $F \to E$.
"""
function integral_model(E::EllCrv{fmpq})
  A = E.coeff[1]
  B = E.coeff[2]

  mue = lcm(denominator(A), denominator(B))
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

  return E_int::EllCrv{fmpq}, trafo_int, trafo_rat
end

################################################################################
#
#  Algorithm of Laska-Kraus-Connel
#
################################################################################

@doc Markdown.doc"""
***
    laska_kraus_connell(E::EllCrv{fmpz}) -> Array{Nemo.fmpz}

> Given an elliptic curve over $\mathbf Q$ with integral model, this returns an
> isomorphic elliptic curve over $\mathbf Q$ with minimal discriminant.
"""
# algorithm of Laska-Kraus-Connell
function laska_kraus_connell(E::EllCrv{fmpq})
  a1 = numerator(E.coeff[1])
  a2 = numerator(E.coeff[2])
  a3 = numerator(E.coeff[3])
  a4 = numerator(E.coeff[4])
  a6 = numerator(E.coeff[5])

  b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

  delta = divexact(c4^3 - c6^2, 1728)

  u = fmpz(1)
  g = gcd(c6^2, delta)

  fac = factor(g)

  for (p, ord) in fac
    d = div(ord, 12)

    if p == 2
      a = divexact(c4, 2^(4*d))
      a = mod(a, 16)
      if a > 8
        a = a - 16
      end

      b = divexact(c6, 2^(6*d))
      b = mod(b, 32)
      if b > 16
        b = b - 32
      end

      if (mod(b, 4) != 3) && !((a == 0) && ((b == 0) || (b == 8)))
        d = d - 1
      end

    elseif p == 3
      ord1 = valuation(c6, 3)

      if (ord1 == 6*d + 2)
        d = d - 1
      end
    end
    u = u * p^d
  end

  c4 = divexact(c4, u^4)
  c6 = divexact(c6, u^6)

  b2 = mod(-c6, 12)
  if b2 > 6
      b2 = b2 - 12
  end

  b4 = divexact(b2^2 - c4, 24)
  b6 = divexact(-b2^3 + 36*b2*b4 - c6, 216)

  na1 = mod(b2, 2)
  na2 = divexact(b2 - na1, 4)
  na3 = mod(b6, 2)
  na4 = divexact(b4 - na1*na3, 2)
  na6 = divexact(b6 - na3, 4)

  return EllipticCurve([na1, na2, na3, na4, na6])::EllCrv{fmpq}
end

################################################################################
#
# T(r, s, t, u) transformation
#
################################################################################

# transformation T(r,s,t,u) as in cremona's book
function transform_rstu(E::EllCrv{fmpq}, T::Array{S, 1}) where S
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
    if !isfinite(P)
      return infinity(F)
    end

    xnew = divexact(1, u^2)*(P.coordx - r)
    ynew = divexact(1, u^3)*(P.coordy - s*u^2*xnew - t)
    Q = F([xnew, ynew])
    return Q
  end

  trafo2 = function(P) # transformes a point on F into a point on E
    if !isfinite(P)
      return infinity(E)
    end

    xnew = u^2*P.coordx + r
    ynew = u^3*P.coordy + s*u^2*P.coordx + t
    Q = E([xnew, ynew])
    return Q
  end

  return F, trafo1, trafo2
end

################################################################################
#
#  Tates algorithm
#
################################################################################

@doc Markdown.doc"""
***
    tates_algorithm_local(E::EllCrv{fmpz}, p::Int) -> EllipticCurve{fmpq}, String, fmpz, fmpz

> Returns a tuple $(\tilde E, K, f, c)$, where $\tilde E$ is a minimal model
> for $E$ at the prime $p$, $K$ is the Kodaira symbol, $f$ is the conduator
> valuation at $p$ and $c$ is the local Tamagawa number at $p$.
"""
# tate's algorithm, see Cremona, p. 66
function tates_algorithm_local(E::EllCrv{fmpq}, p)

  p = FlintZZ(p)

  a1 = numerator(E.coeff[1])
  a2 = numerator(E.coeff[2])
  a3 = numerator(E.coeff[3])
  a4 = numerator(E.coeff[4])
  a6 = numerator(E.coeff[5])

  b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

  delta = disc(E)
  delta = numerator(delta)

  n = valuation(delta, p)

  # test for type I0
  if n == 0
    return (E, "I0", FlintZZ(0), FlintZZ(1))::Tuple{EllCrv{fmpq}, String, fmpz, fmpz}
  end

  # change coordinates so that p | a3, a4, a6
  if p == 2
    if mod(b2, p) == 0
      r = smod(a4, p)
      t = smod(r*(1 + a2 + a4) + a6, p)
    else
      r = smod(a3, p)
      t = smod(r + a4, p)
    end

  elseif p == 3
    if mod(b2, p) == 0
      r = smod(-b6, p)
    else
      r = smod(-b2*b4, p)
    end

    t = smod(a1*r + a3, p)
  else
    if mod(c4, p) == 0
      r = - invmod(FlintZZ(12), p)*b2
    else
      r = - invmod(FlintZZ(12)*c4, p)*(c6 + b2*c4)
    end
      t = - invmod(FlintZZ(2), p)* (a1*r + a3)
      r = smod(r, p)
      t = smod(t, p)
  end

  trans = transform_rstu(E, [r, 0, t, 1])
  E = trans[1]

  a1 = numerator(E.coeff[1])
  a2 = numerator(E.coeff[2])
  a3 = numerator(E.coeff[3])
  a4 = numerator(E.coeff[4])
  a6 = numerator(E.coeff[5])

  b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

  # test for types In, II, III, IV
  if mod(c4, p) != 0
    if quadroots(1, a1, -a2, p)
      cp = FlintZZ(n)
    elseif mod(n, 2) == 0
      cp = FlintZZ(2)
    else
      cp = FlintZZ(1)
    end

    Kp = "I$(n)"
    fp = FlintZZ(1)

    return (E, Kp, fp, cp)::Tuple{EllCrv{fmpq}, String, fmpz, fmpz}
  end

  if mod(a6, p^2) != 0
    Kp = "II"
    fp = FlintZZ(n)
    cp = FlintZZ(1)
    return (E, Kp, fp, cp)::Tuple{EllCrv{fmpq}, String, fmpz, fmpz}
  end

  if mod(b8, p^3) != 0
    Kp = "III"
    fp = FlintZZ(n-1)
    cp = FlintZZ(2)
    return (E, Kp, fp, cp)::Tuple{EllCrv{fmpq}, String, fmpz, fmpz}
  end

  if mod(b6, p^3) != 0
    if quadroots(1, divexact(a3, p), divexact(-a6, p^2), p)
      cp = FlintZZ(3)
    else
      cp = FlintZZ(1)
    end
    Kp = "IV"
    fp = n - 2
    return (E, Kp, FlintZZ(fp), cp)::Tuple{EllCrv{fmpq}, String, fmpz, fmpz}
  end

  # change coordinates so that p | a1, a2; p^2 | a3, a4; p^3 | a6
  if p == 2
    s = smod(a2, 2)
    t = 2 * smod(divexact(a6, 4), 2)
  else
    s = -a1 * invmod(FlintZZ(2), p)
    t = -a3 * invmod(FlintZZ(2), p)
  end

  trans = transform_rstu(E, fmpz[0, s, t, 1])
  E = trans[1]

  a1 = numerator(E.coeff[1])
  a2 = numerator(E.coeff[2])
  a3 = numerator(E.coeff[3])
  a4 = numerator(E.coeff[4])
  a6 = numerator(E.coeff[5])

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
    fp = FlintZZ(n - 4)
    cp = 1 + nrootscubic(b, c, d, p)
    return (E, Kp, fp, FlintZZ(cp))::Tuple{EllCrv{fmpq}, String, fmpz, fmpz}

  # test for double root: type Im*
  elseif mod(x, p) != 0

    # change coordinates so that the double root is T = 0
    if p == 2
      r = c
    elseif p == 3
      r = b*c
    else
      r = (b*c - 9*d) * invmod(FlintZZ(2)*x, p)
    end

    r = p * smod(r, p)

    trans = transform_rstu(E, [r, 0, 0, 1])
    E = trans[1]

    a1 = numerator(E.coeff[1])
    a2 = numerator(E.coeff[2])
    a3 = numerator(E.coeff[3])
    a4 = numerator(E.coeff[4])
    a6 = numerator(E.coeff[5])

    b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

    # make a3, a4, a6 repeatedly more divisible by p
    m = 1
    mx = p^2
    my = p^2
    cp = FlintZZ(0)

    while cp == 0
      xa2 = divexact(a2, p)
      xa3 = divexact(a3, my)
      xa4 = divexact(a4, p*mx)
      xa6 = divexact(a6, mx*my)

      if mod(xa3^2 + 4*xa6, p) !=  0
        if quadroots(1, xa3, -xa6, p)
          cp = FlintZZ(4)
        else
          cp = FlintZZ(2)
        end

      else
        if p == 2
          t = my * xa6
        else
          t = my * smod(-xa3*invmod(FlintZZ(2), p), p)
        end

        trans = transform_rstu(E, [0, 0, t, 1])
        E = trans[1]

        a1 = numerator(E.coeff[1])
        a2 = numerator(E.coeff[2])
        a3 = numerator(E.coeff[3])
        a4 = numerator(E.coeff[4])
        a6 = numerator(E.coeff[5])

        b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

        my = my*p
        m = m + 1
        xa2 = divexact(a2, p)
        xa3 = divexact(a3, my)
        xa4 = divexact(a4, p*mx)
        xa6 = divexact(a6, mx*my)

        if mod(xa4^2 - 4*xa2*xa6, p) != 0
          if quadroots(xa2, xa4, xa6, p)
            cp = FlintZZ(4)
          else
            cp = FlintZZ(2)
          end

        else
          if p == 2
            r = mx * smod(xa6*xa2, 2)
          else
            r = mx * smod(-xa4 * invmod(2*xa2, p), p)
          end

          trans = transform_rstu(E, [r, 0, 0, 1])
          E = trans[1]

          a1 = numerator(E.coeff[1])
          a2 = numerator(E.coeff[2])
          a3 = numerator(E.coeff[3])
          a4 = numerator(E.coeff[4])
          a6 = numerator(E.coeff[5])

          b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

          mx = mx*p
          m = m + 1
        end
      end
    end

    fp = n - m - 4
    Kp = "I$(m)*"

    return (E, Kp, FlintZZ(fp), FlintZZ(cp))::Tuple{EllCrv{fmpq}, String, fmpz, fmpz}

  else
    # Triple root case: types II*, III*, IV* or non-minimal
    # change coordinates so that the triple root is T = 0
    if p == 3
      rp = -d
    else
      rp = -b * invmod(FlintZZ(3), p)
    end

    r = p * smod(rp, p)

    trans = transform_rstu(E, [r, 0, 0, 1])
    E = trans[1]

    a1 = numerator(E.coeff[1])
    a2 = numerator(E.coeff[2])
    a3 = numerator(E.coeff[3])
    a4 = numerator(E.coeff[4])
    a6 = numerator(E.coeff[5])

    b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

    x3 = divexact(a3, p^2)
    x6 = divexact(a6, p^4)

    # Test for type IV*
    if mod(x3^2 + 4* x6, p) != 0
      if quadroots(1, x3, -x6, p)
        cp = FlintZZ(3)
      else
        cp = FlintZZ(1)
      end
      Kp = "IV*"
      fp = FlintZZ(n - 6)

      return (E, Kp, fp, FlintZZ(cp))::Tuple{EllCrv{fmpq}, String, fmpz, fmpz}
    else
      if p == 2
        t = x6
      else
        t = x3 * invmod(FlintZZ(2), p)
      end

      t = -p^2 * smod(t, p)

      trans = transform_rstu(E, [0, 0, t, 1])
      E = trans[1]

      a1 = numerator(E.coeff[1])
      a2 = numerator(E.coeff[2])
      a3 = numerator(E.coeff[3])
      a4 = numerator(E.coeff[4])
      a6 = numerator(E.coeff[5])

      b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

      # Test for types III*, II*
      if mod(a4, p^4) != 0
        Kp = "III*"
        fp = FlintZZ(n - 7)
        cp = FlintZZ(2)

        return (E, Kp, fp, FlintZZ(cp))::Tuple{EllCrv{fmpq}, String, fmpz, fmpz}
      elseif mod(a6, p^6) != 0
        Kp = "II*"
        fp = FlintZZ(n - 8)
        cp = FlintZZ(1)

        return (E, Kp, fp, FlintZZ(cp))::Tuple{EllCrv{fmpq}, String, fmpz, fmpz}
      else
        E = transform_rstu(E, [0, 0, 0, p])[1]
        return tates_algorithm_local(E, p)::Tuple{EllCrv{fmpq}, String, fmpz, fmpz}
      end
    end
  end
end

@doc Markdown.doc"""
***
    tates_algorithm_global(E::EllCrv{fmpq}) -> EllCrv{fmpq}

> Returns a global reduced minimal model for $E$ using Tate's algorithm.
"""
function tates_algorithm_global(E)
  delta = abs(numerator(disc(E)))
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

  return E::EllCrv{fmpq}
end

################################################################################
#
#  Minimal model(s)
#
################################################################################

@doc Markdown.doc"""
***
    minimal_model(E::EllCrv{fmpq}) -> EllCrv{fmpq}

> Returns the reduced global minimal model of $E$.
"""
function minimal_model(E::EllCrv{fmpq})
  return tates_algorithm_global(E)
end

@doc Markdown.doc"""
***
    minimal_model(E::EllCrv{fmpq}) -> EllCrv{fmpq}

> Returns a model of $E$, which is minimal at $p$. It is assumed that $p$
> is prime.
"""
function minimal_model(E::EllCrv{fmpq}, p::Int)
  Ep = tates_algorithm_local(E, p)
  return Ep
end

@doc Markdown.doc"""
***
    tidy_model(E::EllCrv{fmpz}) -> EllCrv{fmpz}
> Given an elliptic curve with minimal model, this functions returns an
> isomorphic curve with reduced minimal model, that is, $a_1, a_3 \in \{0, 1\}$
> and $a_2 \in \{-1,0,1\}$.
"""
function tidy_model(E::EllCrv{fmpq})

  a1 = numerator(E.coeff[1])
  a2 = numerator(E.coeff[2])
  a3 = numerator(E.coeff[3])
  a4 = numerator(E.coeff[4])
  a6 = numerator(E.coeff[5])

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

  E = transform_rstu(E, [r, s, t, 1])[1]

  return E
end

################################################################################
#
#  Integral invariants
#
################################################################################

# this needs to be rewritten
@doc Markdown.doc"""
    get_b_integral(E::EllCrv{fmpz}) -> Nemo.fmpz
> Computes the invariants b2, b4, b6, b8 of an elliptic curve E with integer coefficients.
"""
function get_b_integral(E)
  a1 = numerator(E.coeff[1])
  a2 = numerator(E.coeff[2])
  a3 = numerator(E.coeff[3])
  a4 = numerator(E.coeff[4])
  a6 = numerator(E.coeff[5])

  b2 = a1^2 + 4*a2
  b4 = a1*a3 + 2*a4
  b6 = a3^2 + 4*a6
  b8 = a1^2*a6 - a1*a3*a4 + 4*a2*a6 + a2*a3^2 - a4^2

  return b2,b4,b6,b8
end

@doc Markdown.doc"""
    get_b_c_integral(E::EllCrv{fmpz}) -> Nemo.fmpz
> Computes the invariants b2, b4, b6, b8, c4, c6 of an elliptic curve E with integer coefficients.
"""
function get_b_c_integral(E)
    a1 = numerator(E.coeff[1])
    a2 = numerator(E.coeff[2])
    a3 = numerator(E.coeff[3])
    a4 = numerator(E.coeff[4])
    a6 = numerator(E.coeff[5])

    b2 = a1^2 + 4*a2
    b4 = a1*a3 + 2*a4
    b6 = a3^2 + 4*a6
    b8 = a1^2*a6 - a1*a3*a4 + 4*a2*a6 + a2*a3^2 - a4^2

    c4 = b2^2 - 24*b4
    c6 = -b2^3 + 36*b2*b4 - 216*b6

    return b2,b4,b6,b8,c4,c6
end

