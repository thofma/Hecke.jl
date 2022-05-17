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
# (C) 2022 Jeroen Hanselman
#
################################################################################

export agm, periods, real_period

################################################################################
#
#  Arithmetic geometric mean
#
################################################################################


function agm_one(y::AcbField, e::Int = 5)
  0 < e || throw(DomainError())
  err = e*radius(y)
  a = (1+y)/2
  b = sqrt(y)
  
  diff1 = abs(a-b)
  diff2 = abs(a+b)
  if diff1 > diff2 
    #pair is bad as |a-b| > |a+b| so we replace b by -b
    b = -b
    diff2 = diff1
  end
  if radius(diff) < err
    return a
  end
  
  #Find agm of new pair
  return agm(a, b)
end

@doc Markdown.doc"""
    agm(x::AcbField, y::AcbField, e::Int) -> AcbField
  Returns the arithmetic-geometric mean of $x$ and $y$.
"""
function agm(x::AcbField, y::AcbField, e::Int = 5)
  return x*agm_one(y/x)
end


################################################################################
#
#  Real period
#
################################################################################

# See The complex AGM, periods of elliptic curves over C and complex elliptic logarithms
# by John E. Cremona and Thotsaphon Thongjunthug
@doc Markdown.doc"""
    real_period(E::EllCrv{fmpq}, prec::Int) -> Float64
  Return the real period of an elliptic curve $E$ over QQ
"""
function real_period(E::EllCrv{fmpq}, prec = 100)
  return real(_period(E, nothing, prec)[1])
end

@doc Markdown.doc"""
    periods(E::EllCrv{fmpz}, prec::Int) -> Float64
  Return the period lattices of an elliptic curve $E$ over a number field for each possible
  embedding in $mathb{C}$.
"""
function periods(E::EllCrv{T}, prec = 100) where T <: Union{fmpq, nf_elem}
  K = base_field(E)
  if K == QQ
    return _period(E, nothing, prec)
  end
  
  phis = complex_embeddings(K)
  return [_period(E, phi, prec) for phi in phis]
  
end


#Compute the period lattice of an elliptic curve over a number field using a chosen embedding
function _period(E::EllCrv{T}, phi, prec = 100) where T <: Union{fmpq, nf_elem}
  
  attempt = 1
  K = base_field(E)
  
  delta = discriminant(E)
  while true
    precnew = attempt*prec
  
  
    if phi == nothing
      b2, b4, b6, b8 = map(AcbField(precnew), b_invars(E))
    else
      b2, b4, b6, b8 = map(evaluation_function(phi, precnew), b_invars(E))
    end
  
    C = parent(b2)
    Cx, x = PolynomialRing(C, "x")
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
