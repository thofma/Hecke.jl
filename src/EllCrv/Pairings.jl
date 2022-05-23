################################################################################
#
#             EllCrv/Periods.jl: Functions for computing the period matrix of
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
# (C) 2022 Jeroen Hanselman
#
################################################################################

export weil_pairing

################################################################################
#
#  Weil pairing
#
################################################################################

#Compute the value of f(R) where y = f(x) is the equation defining the line through P and Q
#Following the Sage implementation by David Hansen in ell_point.py
function straight_line(P::EllCrvPt{T}, Q::EllCrvPt{T}, R::EllCrvPt{T}) where T

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
      #Vertical line: x - Q[1] 
      return R[1] - Q[1]
    end
    
    if is_infinite(Q)
      #Vertical line: x - P[1] 
      return R[1] - P[1]
    end
  end
  
  if P == Q
    a1, a2, a3, a4, a6 = a_invars(E)
    num = 3*P[1]^2 + 2*a2*P[1] + a4 - a1*P[2]
    denom = 2*P[2] + a1*P[1] + a3
  
    if denom == 0
      return R[1] - P[1]
    end
    slope = num//denom
  else
    if P[1] == Q[1]
      #Vertical line: x - P[1] 
      return R[1] - P[1]
    else
      slope = (Q[2] - P[2])// (Q[1] - P[1])
    end
  end
  
  return R[2] - P[2] - slope * (R[1] - P[1])
end
# Evaluate the function f_{n, P} at the point Q, where the divisor of
# f_{n, P} is given by n*[P]-[n*P]-(n-1)*[O].
function miller(P::EllCrvPt{T}, Q:: EllCrvPt{T}, n::Int) where T
  @req parent(P) == parent(Q) @req parent(P) == parent(Q) == parent(R) "P, Q and R need to lie on the same curve"
  @req is_finite(Q) "Q cannot be infinity"
  @req n != 0 "n cannot be zero"
  
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
    t = t^2*ell//vee
    V = S
    if nbinary[i] == 1
      S = V + P
      ell = straight_line(V, P, Q)
      vee = straight_line(S, -S, Q)
      t = t*ell//vee
      V = S
    end
    i = i - 1
  end
  
  if n_negative
    vee = straight_line(V, -V, Q)
    t = 1//(t*vee)
  end
  return t 
end

function weil_pairing(P::EllCrvPt{T}, Q::EllCrvPt{T}, n::Int) where T
  E = parent(P)
  K = base_field(E)
  O = infinity(E)
  @req E == parent(Q) "P and Q need to be points on the same curve."
  @req n*P == O && n*Q == O "P and Q need to be n-torsion points."
  
  if P == Q || P == O || Q == O
    return one(K)
  end
  
  try
    return (-1)^n*div(miller(P, Q, n), miller(Q, P, n))
  catch DivideError
    return one(K)
  end
  
end

