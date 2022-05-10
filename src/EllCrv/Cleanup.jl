################################################################################
#
#             EllCrv/Cleanup.jl : Needs more love
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


################################################################################
#
#  Independence test
#
################################################################################

# see Robledo, p. 47
@doc Markdown.doc"""
    is_independent(S::Array{EllCrvPt{fmpq}}) -> Bool

Tests whether a given set of points $S$ on a rational elliptic curve
is linearly independent. Returns true if they are independent, otherwise false.
This function may return false results.
"""
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

################################################################################
#
#  Arithmetic geometric mean
#
################################################################################

@doc Markdown.doc"""
    agm(x::Float64, y::Float64, e::Int) -> Float64
  Returns the arithmetic-geometric mean of $x$ and $y$.
"""
function agm(x::Float64, y::Float64, e::Int = 5)
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

################################################################################
#
#  Real period
#
################################################################################

# see Cohen
@doc Markdown.doc"""
    real_period(E::EllCrv{fmpz}) -> Float64
  Returns the real period of an elliptic curve $E$ with integer coefficients.
"""
function real_period(E)
  a1 = numerator(E.coeff[1])
  a2 = numerator(E.coeff[2])
  a3 = numerator(E.coeff[3])
  a4 = numerator(E.coeff[4])
  a6 = numerator(E.coeff[5])

  b2, b4, b6, b8 = get_b_integral(E)

  delta = discriminant(E)
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

################################################################################
#
#  Logarithmic height of a rational number
#
################################################################################

@doc Markdown.doc"""
    height(x::fmpq) -> Float64

Computes the height of a rational number $x$.
"""
function log_height(x::fmpq)
  a = Float64(numerator(x))
  b = Float64(denominator(x))
  return log(max(abs(a),abs(b)))
end

# every rational point is given by P = (a/c^2, b/c^3), gcd(a,c) = gcd(b,c) = 1. then h(P) = max(|a|, c^2)
# but is it always in this form?
@doc Markdown.doc"""
    naive_height(P::EllCrvPt{fmpq}) -> Float64

Computes the naive height of a point $P$.
"""
function naive_height(P)
  x = P.coordx
  a = Float64(numerator(x))
  c2 = Float64(denominator(x))

  h = log(max(abs(a), abs(c2)))
  return h
end

# p.75 Cremona
@doc Markdown.doc"""
    points_with_bounded_naive_height(E:EllCrv, B::Int) -> Array{EllCrvPt}

Computes all rational points on a curve $E$ with integer coefficients which have naive height <= $B$.
"""
function points_with_bounded_naive_height(E, B)
  a1 = numerator(E.coeff[1])
  a2 = numerator(E.coeff[2])
  a3 = numerator(E.coeff[3])
  a4 = numerator(E.coeff[4])
  a6 = numerator(E.coeff[5])

  # 2-torsion
  f(x) = x^3 + Float64(a2)*x^2 + Float64(a4)*x + Float64(a6)
  torsiontwo = sort(fzeros(f))
  x0 = torsiontwo[1]

  R, z = PolynomialRing(FlintZZ, "z")

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
            P = E([FlintQQ(a,c^2), FlintQQ(b, c^3)])
            push!(points, P)
          end
        end
      end
    end
  end

  return points
end

@doc Markdown.doc"""
torsion_points_via_height(E::EllCrv{fmpz}) ->  Array{EllCrvPt}
Returns the rational torsion points of a curve $E$ with integer coefficients.
"""
function torsion_points_via_height(E::EllCrv{fmpq})

  if E.short == true
    E = EllipticCurve([0, 0, 0, E.coeff[1], E.coeff[2]])
  end

  jay = j(E)
  hj = log_height(jay) # height of the j-invariant
  jfloat = Float64(numerator(jay))/Float64(denominator(jay))

  delta = numerator(discriminant(E))
  b2, b4, b6, b8 = get_b_integral(E)
  twostar = 2
  if b2 == 0
    twostar = 1
  end

  # mu(E)
  mu = (1/6)*( log(abs(Float64(delta))) + log(max(1, abs(jfloat))) ) + log(max(1, abs(Float64(b2)/12))) + log(twostar)

  B = (1/12)*hj + mu + 1.922

  # all torsion points have naive height <= B, see Cremona, p. 77
  torsion_candidates = points_with_bounded_naive_height(E, B)
  torsion_points = [infinity(E)]

  # check which points of the candidates are torsion points (order of a torsion point is <= 12)
  for P in torsion_candidates
    is_torsion = false
    k = 7
    while (is_torsion == false) && (k <= 12)
      if (k*P).is_infinite == true
        is_torsion = true
      end
      k = k + 1
    end

    if is_torsion == true
      push!(torsion_points, P)
    end
  end

  return torsion_points
end

@doc Markdown.doc"""
independent_points_up_to(E::EllCrv{fmpq}, B::Int) -> Array{EllCrvPt}
Returns a maximal set of independent points with naive height <= $B$
"""
function independent_points_up_to(E::EllCrv{fmpq},B::IntegerUnion)

  if E.short == true
      E = EllipticCurve([0, 0, 0, E.coeff[1], E.coeff[2]])
  end

  points = points_with_bounded_naive_height(E,B)
  counter = 1
  M_ind = Matrix{Float64}(0,0)
  M_cand = Matrix{Float64}(1,1)
  points_ind = []

  for p in points
    is_torsion = false
    i = 7
    while (i < 13) && (is_torsion == false)
      if (i*p).is_infinite == true
        is_torsion = true
      end
      i = i + 1
    end

    if is_torsion == true
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

################################################################################
#
#  BSD
#
################################################################################

@doc Markdown.doc"""
mod_red(E::EllCrv, B::Int) -> (P::Array{Int}, N::Array{Nemo.fmpz})
input: E elliptic curve given in long form over ZZ
output: arrays P, N, where
  P contains all primes smaller than B (for which E/F_p is non-singular)
  N[i] = #E(F_P[i])
"""
function mod_red(E, B)
    minmodel = EllipticCurve(laska_kraus_connell(E)) # global minimal model for E
    P = primes(B) # primes smaller than B
    N = Nemo.fmpz[]

    for i in 1:length(P)
        p = P[i]
        R = GF(p, cached = false)
        Ep = EllipticCurve([R(numerator(minmodel.coeff[1])), R(numerator(minmodel.coeff[2])), R(numerator(minmodel.coeff[3])), R(numerator(minmodel.coeff[4])), R(numerator(minmodel.coeff[5]))],  false) # reduction of E mod p

        if  discriminant(Ep) != 0 # can only determine group order if curve is non-singular
            ord = order_best(Ep)
            push!(N, ord)
        else
            P[i] = 0
        end
    end

    P = deleteat!(P, findin(P, 0)) # delete all zeros from P

    return P, N
end

@doc Markdown.doc"""
check_weak_bsd(E::EllCrv, B::Int) -> (a::Float64, b::Float64)
checks weak bsd-conjecture for elliptic curve $E$ given in long form over ZZ, positive integer $B$
returns linear regression values for log(log(B)) and sum of log(N_p/p) for p <= B
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
