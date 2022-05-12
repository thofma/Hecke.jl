################################################################################
#
#             EllCrv/Heights.jl : Height functions on elliptic curves
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
export local_height, real_height, canonical_height, naive_height

################################################################################
#
#  Naive Height 
#
################################################################################

@doc Markdown.doc"""
    naive_height(P::EllCrvPt{fmpq}, prec) -> ArbField

return the naive height of a point $P$ on an elliptic curve defined over $\mathbb{Q}$. 
"""
function naive_height(P::EllCrvPt{fmpq}, prec = 100)
  attempt = 1

  while true
    R = ArbField(attempt*prec)
    x = P.coordx
    p = numerator(x)
    q = denominator(x)
    result = log(R(max(abs(p),abs(q))))
    if radiuslttwopower(result, -prec)
      return result
    end
    attempt = 2*attempt
  end
end

################################################################################
#
#  Local Height at finite prime
#
################################################################################

# Equal to Magma command with Renormalization flag. In Magma the default is to add a factor of (1/6)log Δv at every place.

#TODO: Fine-tune precision

@doc Markdown.doc"""
    local_height(P::EllCrvPt{fmpq}, p::Int, prec::Int) -> ArbField

Computes the local height of a point $P$ on an elliptic curve defined over 
$\mathbb{Q}$ at the prime $p$.
"""
function local_height(P::EllCrvPt{fmpq}, p, prec = 100)

  E = P.parent
  F = minimal_model(E)
  phi = isomorphism(E,F)
  
  P = phi(P)
  
  d = ceil(Int, prec*log(10,2))
  
  p = FlintZZ(p)
    
  x = P.coordx
  y = P.coordy

  a1, a2, a3, a4, a6 = map(numerator,(a_invars(F)))

  b2,b4,b6,b8,c4,c6 = get_b_c_integral(F)

  delta = discriminant(E)

  A = 3*x^2 + 2*a2*x + a4 - a1*y
  B = 2*y + a1*x + a3 # = psi2(P)
  C = 3*x^4 + b2 * x^3 + 3*b4*x^2 + 3*b6*x + b8 # = psi3(P)
  L = 0
  
  attempt = 2
  while true 
    R = ArbField(attempt*prec)
    
    if !is_finite(P)
      return R(0)
    end

    if (A != 0 && valuation(A, p) <= 0) || (B != 0 && valuation(B, p) <= 0)
      if x != 0
        L = max(0, -valuation(x, p))
      else
        L = 0
      end
    elseif (c4 != 0 && valuation(c4, p) == 0)
      N = valuation(delta, p)
      if B == 0
        M = N//2
        L = M*(M - N)//N
      else
        M = min(valuation(B, p), N//2)
        L = M*(M - N)//N
      end
    elseif ( C == 0 || ( C != 0 && B != 0 && valuation(C, p) >= 3*valuation(B, p)))
      L = -2*valuation(B, p)//3
    else
      L = -valuation(C, p)//4
    end
    result = L*log(R(p))
    if Hecke.radiuslttwopower(result,-prec)
      return result
    end
      attempt = 2*attempt
  end
end

################################################################################
#
#  Real Height
#
################################################################################

#Precision is given in bits (as Real Field also works this way), but maybe this should be changed. In Magma precision is given in decimals

@doc Markdown.doc"""
    real_height(P::EllCrvPt{fmpq}, prec::Int) -> ArbField

Computes the real height of a point $P$ on an elliptic curve defined 
over $\mathbb{Q}$.
"""
function real_height(P::EllCrvPt{fmpq}, prec = 100)

  attempt = 3
  d = ceil(Int, prec*log(10,2)) 
  
  E = P.parent
  F = minimal_model(E)
  phi = isomorphism(E,F)
  
  P = phi(P)

  a1, a2, a3, a4, a6 = map(numerator,(a_invars(F)))
  
  b2, b4, b6, b8, c4, c6 = get_b_c_integral(F)
  H = max(4, abs(b2), 2*abs(b4), 2*abs(b6), abs(b8))
  _b2 = b2-12
  _b4 = b4-b2+6
  _b6 = b6-2*b4+b2-4
  _b8 = b8-3*b6+3*b4-b2+3

  N = ceil(Int, (5/3)*d + 1/2 + (3/4)*log(7+(4/3)*log(H)))

  while true

    R = ArbField(attempt*prec)   
    x = R(P.coordx)
    y = R(P.coordy)

    if abs(x)<0.5 
      t = 1/(x+1)
      beta = 0
    else
      t = 1/x
      beta = 1
    end

    mu = -log(abs(t))
    f = 1

    for n in (0:N)
      f = f/4
      if beta==1
        w = b6*t^4+2*b4*t^3+b2*t^2+4*t
        z = 1-b4*t^2-2*b6*t^3-b8*t^4
        zw = z+w
      else
        w = _b6*t^4+2*_b4*t^3+_b2*t^2+4*t
        z = 1-_b4*t^2-2*_b6*t^3-_b8*t^4
        zw = z+w
      end
      if abs(w) <= 2*abs(z)
        mu = mu+f*log(abs(z))
        t = w/z
      else
        mu = mu+f*log(abs(zw))
        t = w/zw
        beta = 1-beta
      end
    end
    if isfinite(mu) & (radius(mu)<R(10)^(-d))
    # Algorithm is only precise up to d decimals
      add_error!(mu,R(10)^(-d))
      return(mu)
    else 
      attempt = 2*attempt
    end
  end
end

################################################################################
#
#  Néron-Tate Height
#
################################################################################
@doc Markdown.doc"""
    neron_tate_height(P::EllCrvPt{fmpq}, prec::Int) -> ArbField

Compute the Néron-Tate height (or canonical height) of a point $P$ on an 
elliptic curve defined over $\mathbb{Q}$.
"""
function neron_tate_height(P::EllCrvPt{fmpq}, prec = 100)
  return canonical_height(P,prec)
end

@doc Markdown.doc"""
    canonical_height(P::EllCrvPt{fmpq}, prec::Int) -> ArbField

Compute the Néron-Tate height (or canonical height) of a point $P$ on an 
elliptic curve defined over $\mathbb{Q}$.
"""
function canonical_height(P::EllCrvPt{fmpq}, prec = 100)
  attempt = 1

  while true
    R = Nemo.RealField(attempt*prec)   
    E = P.parent
    disc = discriminant(E)
    d = (denominator(P.coordx))
    h = real_height(P, attempt*prec) + log(R(d))
    plist = bad_primes(E)

    for p in plist
      if !divides(d,p)[1]
       h = h + local_height(P,p, attempt*prec)
      end
    end
    if Hecke.radiuslttwopower(h,-prec)
      return h
    else
      attempt = 2*attempt
    end
  end
end
