#################################################################################
#
#             EllipticCurve/Misc.jl : Misc functions
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

###############################################################################
#
#  Computing all divisors
#
################################################################################

@doc raw"""
    squaredivisors(n::ZZRingElem) -> Iterator

Computes the numbers whose square divides a given number $n$. It is assumed
that $n$ is not zero.
"""
function squaredivisors(n)
  n == 0 && error("The number must be nonzero")
  return Divisors(n, units = true, power = 2)
end

################################################################################
#
#  Roots of integer polynomials
#
################################################################################


# @doc raw"""
#     quadroots(a::ZZRingElem, b::ZZRingElem, c::ZZRingElem, p::ZZRingElem) -> Bool
#
# Returns true if the quadratic congruence of the quadratic polynomial
# $ax^2 + bx + c = 0$ has a root modulo $p$.
# """
function quadroots(a, b, c, p)
  F_p = GF(p, cached = false)
  R, x = polynomial_ring(F_p, "x", cached = false)
  f = F_p(a)*x^2 + F_p(b)*x + F_p(c)

  if degree(f) == -1
    return true
  elseif degree(f) == 0
    return false
  elseif degree(f) == 1
    return true
  end

  fac = factor(f)
  p = first(keys(fac.fac))

  if fac[p] == 2 # f has a double zero
    return true
  elseif length(fac) == 2 # f splits into two different linear factors
    return true
  else # f does not have a root
    return false
  end
end

function quadroots(a, b, c, _res::Union{Function, MapFromFunc})
  #F_p = GF(p, cached = false)
  aa = _res(a)
  F = parent(aa)
  R, x = polynomial_ring(F, "x", cached = false)
  f = aa*x^2 + _res(b)*x + _res(c)

  if degree(f) == -1
    return true
  elseif degree(f) == 0
    return false
  elseif degree(f) == 1
    return true
  end

  fac = factor(f)
  p = first(keys(fac.fac))

  if fac[p] == 2 # f has a double zero
    return true
  elseif length(fac) == 2 # f splits into two different linear factors
    return true
  else # f does not have a root
    return false
  end
end

function quadroots(a::AbsSimpleNumFieldElem, b::AbsSimpleNumFieldElem, c::AbsSimpleNumFieldElem, pIdeal:: AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  R = order(pIdeal)
  F, phi = residue_field(R, pIdeal)
  P, x = polynomial_ring(F, "x", cached = false)

  t = [phi(R(numerator(s)))//phi(R(denominator(s))) for s in [a, b, c]]

  f = t[1]*x^2 + t[2]*x + t[3]

  if degree(f) == -1
    return true
  elseif degree(f) == 0
    return false
  elseif degree(f) == 1
    return true
  end

  fac = factor(f)
  p = first(keys(fac.fac))

  if fac[p] == 2 # f has a double zero
    return true
  elseif length(fac) == 2 # f splits into two different linear factors
    return true
  else # f does not have a root
    return false
  end
end

@doc raw"""
    nrootscubic(b::ZZRingElem, c::ZZRingElem, d::ZZRingElem, p::ZZRingElem) -> ZZRingElem

Returns the number of roots of the polynomial $x^3 + bx^2 + cx + d = 0$
modulo $p$.
"""
function nrootscubic(b, c, d, p)
  F_p = GF(p, cached = false)
  R, x = polynomial_ring(F_p, "x")
  f = x^3 + F_p(b)*x^2 + F_p(c)*x + F_p(d)

  fac = factor(f)

  if length(fac) == 1
    if fac[first(keys(fac.fac))] == 3
      return FlintZZ(3)
    else
      return FlintZZ(0)
    end
  elseif length(fac) == 2
    if fac[first(keys(fac.fac))]== 1 && fac[first(keys(fac.fac))] == 1
      # one linear and one irreducible quadratic factor
      return FlintZZ(1)
    else
      return FlintZZ(3) #one double and one single root
    end
  else
    return FlintZZ(3)
  end
end

function nrootscubic(b::AbsSimpleNumFieldElem, c::AbsSimpleNumFieldElem, d::AbsSimpleNumFieldElem, pIdeal:: AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  R = order(pIdeal)
  F, phi = residue_field(R, pIdeal)
  P, x = polynomial_ring(F, "x", cached = false)

  t = [phi(R(numerator(s)))//phi(R(denominator(s))) for s in [b,c,d]]

  f = x^3 + t[1]*x^2 + t[2]*x + t[3]

  fac = factor(f)
  if length(fac) == 1
    if fac[first(keys(fac.fac))] == 3
      return FlintZZ(3)
    else
      return FlintZZ(0)
    end
  elseif length(fac) == 2
    if fac[first(keys(fac.fac))]== 1 && fac[first(keys(fac.fac))] == 1
      # one linear and one irreducible quadratic factor
      return FlintZZ(1)
    else
      return FlintZZ(3) #one double and one single root
    end
  else
    return FlintZZ(3)
  end
end

function smod(a::T, b::S) where {T, S}
  z = mod(a, b)
  if 2*z > b
    z = z - b
  end
  return z
end

@doc raw"""
	normal_basis(K::FinField, L::FinField) -> FinFieldElem

Return a normal element of $L$ over $K = \mathbf F_q$, i.e. an
element $a$ in L such that 1, a^q, a^(q^2), ..., a^(q^n) forms
a K-basis of L.
"""
function normal_basis(K::T, L::T) where T<:FinField

  p1 = characteristic(K)
  p2 = characteristic(L)

  r1 = degree(K)
  r2 = degree(L)

  q = p1^r1

  @assert p1 == p2
  n = divexact(r2, r1)
  while true
    alpha = rand(L)
    a = [alpha^(q^i) for i in (0:n-1)]
    M = matrix([tr(i * j) for i in a, j in a])
    if !iszero(det(M))
      return alpha
    end
  end
end


function mod(a::AbsSimpleNumFieldElem, I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  R = order(I)
  k, phi = residue_field(R, I)
  a_num = phi(R(numerator(a)))
  a_denom = phi(R(denominator(a)))
  b = a_num//a_denom
  return preimage(phi, b)
end

@doc raw"""
	inv_mod(a::AbsSimpleNumFieldOrderElem, I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> AbsSimpleNumFieldOrderElem

Return a lift of the inverse of an element modulo a prime ideal.
"""
function Base.invmod(a::AbsSimpleNumFieldOrderElem, I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  R = order(I)
  k, phi = residue_field(R, I)
  return preimage(phi, inv(phi(R(a))))
end

function Base.invmod(a::AbsSimpleNumFieldElem, I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  R = order(I)
  k, phi = residue_field(R, I)
  a_num = phi(R(numerator(a)))
  a_denom = phi(R(denominator(a)))
  b = a_num//a_denom
  return preimage(phi, inv(b))
end

@doc raw"""
	pth_root_mod(a::AbsSimpleNumFieldOrderElem, I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> AbsSimpleNumFieldOrderElem

Return a lift of the pth root of an element mod a prime ideal lying over p.
"""
function pth_root_mod(a::AbsSimpleNumFieldOrderElem, pIdeal::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  R = order(pIdeal)
  p = pIdeal.gen_one
  k, phi = residue_field(R, pIdeal)
  return preimage(phi, pth_root(phi(R(a))))
end

function pth_root_mod(a::AbsSimpleNumFieldElem, pIdeal::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  R = order(pIdeal)
  p = pIdeal.gen_one
  k, phi = residue_field(R, pIdeal)
  a_num = phi(R(numerator(a)))
  a_denom = phi(R(denominator(a)))
  b = a_num//a_denom
  return preimage(phi, pth_root(b))
end

