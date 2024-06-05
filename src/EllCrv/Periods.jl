################################################################################
#
#             EllipticCurve/Periods.jl: Functions for computing the period matrix of
#                                an  elliptic curve
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
#  Real period
#
################################################################################

# Following The complex AGM, periods of elliptic curves over C and complex
#elliptic logarithms by John E. Cremona and Thotsaphon Thongjunthug
@doc raw"""
    real_period(E::EllipticCurve{QQFieldElem}, prec::Int) -> Float64
Return the real period of an elliptic curve $E$ over QQ
"""
function real_period(E::EllipticCurve{QQFieldElem}, prec::Int = 100)
  return real(period_real_embedding(E, nothing, prec)[1])
end

@doc raw"""
    periods(E::EllipticCurve{ZZRingElem}, prec::Int) -> Float64
Return the period lattices of an elliptic curve $E$ over a number field for each possible
embedding in $mathb{C}$.
"""
function periods(E::EllipticCurve{T}, prec::Int = 100) where T <: Union{QQFieldElem, AbsSimpleNumFieldElem}
  K = base_field(E)
  if K == QQ
    return [period_real_embedding(E, nothing, prec)]
  end

  phis = complex_embeddings(K)
  return [isreal(phi) ? period_real_embedding(E, phi, prec) : period_complex_embedding(E, phi, prec) for phi in phis]

end

#Compute the period lattice of an elliptic curve over a number field using a chosen real embedding.
function period_real_embedding(E::EllipticCurve{T}, phi, prec::Int = 100) where T<: Union{QQFieldElem, AbsSimpleNumFieldElem}

  attempt = 1
  K = base_field(E)

  while true
    precnew = attempt*prec

    if phi === nothing
      b2, b4, b6, b8 = map(ArbField(precnew), b_invariants(E))
    else
      b2, b4, b6, b8 = map(real, (map(evaluation_function(phi, precnew), b_invariants(E))))
    end

    delta = (-b2^2*b8 - 8*b4^3 - 27*b6^2 + 9*b2*b4*b6)
    R = parent(b2)
    C = AcbField(precision(R))

    Cx, x = polynomial_ring(C, "x")
    f = 4*x^3 +b2*x^2 +2*b4*x +b6
    root = roots(f, initial_prec = precnew)
    filter!(isreal, root)
    root = map(real, root)

    pi = const_pi(R)
    i = onei(C)
    if delta < 0 # only one real root
      e1 = root[1]
      a = 3*e1 + b2/4
      b = sqrt(3*e1^2 + b2/2*e1 + b4/2)
      w1 = C(2*pi / agm(2*sqrt(b), sqrt(2*b + a)))
      w2 = -w1/2 + i*pi / agm(2*sqrt(b), sqrt(2*b - a))
    else

      root = sort(root)
      e1 = root[3]
      e2 = root[2]
      e3 = root[1]
      w1 = C(pi / agm(sqrt(e1-e3), sqrt(e2-e3)))
      w2 = i*pi / agm(sqrt(e1-e3), sqrt(e2-e3))
    end

    if Hecke.radiuslttwopower(w1,-prec) && Hecke.radiuslttwopower(w2,-prec)
      return [w1,w2]
    end
    attempt+=attempt
  end
end

#Compute the period lattice of an elliptic curve over a number field using a chosen embedding.
#Also works for real embeddings, but as the other one exclusively uses real arithmetic, it is probably
#faster.
function period_complex_embedding(E::EllipticCurve{T}, phi, prec = 100) where T <: Union{QQFieldElem, AbsSimpleNumFieldElem}

  attempt = 1
  K = base_field(E)

  while true
    precnew = attempt*prec

    if phi === nothing
      b2, b4, b6, b8 = map(AcbField(precnew), b_invariants(E))
    else
      b2, b4, b6, b8 = map(evaluation_function(phi, precnew), b_invariants(E))
    end

    C = parent(b2)
    Cx, x = polynomial_ring(C, "x")
    f = 4*x^3 +b2*x^2 +2*b4*x +b6
    e1, e2, e3 = roots(f, initial_prec = precnew)

    a = sqrt(e1 - e3)
    b = sqrt(e1 - e2)
    c = sqrt(e2 - e3)

    i = onei(C)
    pi = const_pi(C)

    w1 = pi/agm(a,b)
    w2 = i*pi/agm(c, a)
    if Hecke.radiuslttwopower(w1,-prec) && Hecke.radiuslttwopower(w2,-prec)
      return [w1,w2]
    end
    attempt+=attempt
  end
end

@doc raw"""
    faltings_height(E::EllipticCurve{QQFieldElem}, prec::Int) -> Float64

Return the Faltings height of E. This is defined as -1/2log(A) where A is the covolume
of the period lattice of the mnimal model of E.
"""
function faltings_height(E::EllipticCurve{QQFieldElem}, prec::Int = 100)

  attempt = 2
  E, phi = minimal_model(E)
  while true
    precnew = attempt*prec

    result = _faltings(E, precnew)

    if Hecke.radiuslttwopower(result,-prec)
      return result
    end
  attempt+=attempt
  end
  return result
end

@doc raw"""
    stable_faltings_height(E::EllipticCurve{QQFieldElem}, prec::Int) -> Float64

Return the stable Faltings height of E. This is defined as
1/12*(log(denominator(j)) - abs(delta))-1/2log(A) where j is the j-invariant,
delta is the discriminant and A is the covolume
of the period lattice of the chosen model of E.
"""
function stable_faltings_height(E::EllipticCurve{QQFieldElem}, prec = 100)
  attempt = 2
  while true
    precnew = attempt*prec
    R = ArbField(precnew)

    jpart = log(R(denominator(j_invariant(E))))
    deltapart = log(abs(R(discriminant(E))))
    result = (jpart - deltapart)/12 + _faltings(E, precnew)
    if Hecke.radiuslttwopower(result,-prec)
      return result
    end
    attempt+=attempt
  end
end

#Compute -1/2log(A) where A is the covolume of the period lattice of E.
function _faltings(E::EllipticCurve, prec::Int)
   L = periods(E, prec)[1]
   M = matrix(ArbField(prec), 2, 2, [real(L[1]), imag(L[1]), real(L[2]), imag(L[2])])
   return -log(det(M))/2
end


