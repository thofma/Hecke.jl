################################################################################
#
#             EllipticCurve/Pairings.jl: Functions for computing various pairings
#                                on elliptic curves
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
# (C) 2022 Jeroen Hanselman
#
################################################################################

################################################################################
#
#  Weil pairing
#
################################################################################

# Compute the value of f(R) where f(x, y) = y -a*x - b is the equation defining
# the line through P and Q.
# Inspired by the Sage implementation by David Hansen in ell_point.py
function straight_line(P::EllipticCurvePoint{T}, Q::EllipticCurvePoint{T}, R::EllipticCurvePoint{T}) where T
  @req parent(P) == parent(Q) == parent(R) "P, Q and R need to lie on the same curve"
  if is_infinite(R)
    error("R has to be a finite point")
  end
  E = parent(P)
  K = base_field(E)

  if is_infinite(P) || is_infinite(Q)
    if P == Q
      #Degenerate case
      return one(K)
    end

    if is_infinite(P)
      #Vertical line
      return R[1] - Q[1]
    end

    if is_infinite(Q)
      #Vertical line
      return R[1] - P[1]
    end
  end

  if P == Q
    #Line tangent to P
    a1, a2, a3, a4, a6 = a_invariants(E)
    num = 3*P[1]^2 + 2*a2*P[1] + a4 - a1*P[2]
    denom = 2*P[2] + a1*P[1] + a3

    if denom == 0
      return R[1] - P[1]
    end
    slope = num//denom
  else
    if P[1] == Q[1]
      #Vertical line
      return R[1] - P[1]
    else
      #Line through P and Q
      slope = (Q[2] - P[2])// (Q[1] - P[1])
    end
  end

  return R[2] - P[2] - slope * (R[1] - P[1])
end

# Evaluate the function f_{n, P} at the point Q, where the divisor of
# f_{n, P} is given by n*[P]-[n*P]-(n-1)*[O].
# Linearly dependent points might end up dividing by zero and give a DivideError
function _try_miller(P::EllipticCurvePoint{T}, Q::EllipticCurvePoint{T}, n::Int) where T
  @req parent(P) == parent(Q) "P and Q need to lie on the same curve"
  @req is_finite(Q) "Q must be finite"
  @req n != 0 "n must be non-zero"

  n_negative = n < 0
  if n_negative
    n = -n
  end

  t = one(base_field(parent(P)))
  V = P
  nbinary = digits(n, base=2)
  i = nbits(n) - 1

  while i > 0
    S = 2 * V
    ell = straight_line(V, V, Q)
    vee = straight_line(S, -S, Q)
    if iszero(vee)
      return false, vee
    end
    t = t^2*ell//vee
    V = S
    if nbinary[i] == 1
      S = V + P
      ell = straight_line(V, P, Q)
      vee = straight_line(S, -S, Q)
      if iszero(vee)
        return false, vee
      end
      t = t*ell//vee
      V = S
    end
    i = i - 1
  end

  if n_negative
    vee = straight_line(V, -V, Q)
    if iszero(vee) || iszero(t)
      return false, vee
    end
    t = 1//(t*vee)
  end
  return true, t
end

@doc raw"""
    weil_pairing(P::EllipticCurvePoint, Q::EllipticCurvePoint, n::Int) -> FieldElem

Given two $n$-torsion points $P$ and $Q$ on an elliptic curve, return the Weil
pairing $e_n(P, Q)$.
"""
function weil_pairing(P::EllipticCurvePoint{T}, Q::EllipticCurvePoint{T}, n::Int) where T
  E = parent(P)
  K = base_field(E)
  O = infinity(E)
  @req E == parent(Q) "P and Q need to be points on the same curve."
  @req n*P == O && n*Q == O "P and Q need to be n-torsion points."

  if P == Q || P == O || Q == O
    return one(K)
  end

  fl, m1 = _try_miller(P, Q, n)
  fl2, m2 = _try_miller(Q, P, n)
  if !fl || !fl2
    return one(K)
  else
    (-1)^n * divexact(m1, m2)
  end
end

@doc raw"""
    tate_pairing(P::EllipticCurvePoint{T}, Q::EllipticCurvePoint{T}, n::Int) where T

Given an $n$-torsion point $P$ and another point $Q$ on an elliptic curve over
a finite field $K$. Return the Tate pairing $t_n(P, Q)$ by returning a
representative of the coset modulo $n$-th powers.

See also [reduced_tate_pairing](@ref) if one wants an $n$-th root.
"""
function tate_pairing(P::EllipticCurvePoint{T},
                      Q::EllipticCurvePoint{T}, n::IntegerUnion) where {T <: FinFieldElem}
  E = parent(P)
  @req E == parent(Q) "P and Q need to be points on the same curve."
  @req n*P == infinity(E) "P is not of order dividing n."

  if is_finite(Q) && begin fl, result = _try_miller(P, Q, n); fl; end
    return result
  else
    # If Q is infinite or miller fails, do the following
    R = rand(E)
    #Avoid obvious problematic points
    while R == P || R == -Q || R == P-Q || is_infinite(R)
      R = rand(E)
    end
    num = tate_pairing(P, Q + R, n)
    denom = tate_pairing(P, R, n)
    result = num//denom
  end
end

#Assuming that P and Q are defined over the same field which contains the nth roots of unity.
#Should be identical to reduced_tate_pairing in Magma
@doc raw"""
    reduced_tate_pairing(P::EllipticCurvePoint, Q::EllipticCurvePoint, n::Int) -> FieldElem

Given an $n$-torsion point $P$ and another point $Q$ on an elliptic curve over
a finite field $K$, eturn the reduced Tate pairing $t_n(P, Q)^{(\#K - 1)/n}$.

See also [`tate_pairing`](@ref).
"""
function reduced_tate_pairing(P::EllipticCurvePoint, Q::EllipticCurvePoint, n)
  E = parent(P)
  @req E == parent(Q) "P and Q need to be points on the same curve."
  K = base_field(E)
  d = degree(K)
  q = order(K)
  @req is_divisible_by(q - 1, n) "K needs to contain the nth roots of unity."
  @req n*P == infinity(E) "P must be of order n."

  e = div(q - 1, n)
  return tate_pairing(P, Q, n)^e
end
