#################################################################################
#
#             EllCrv/Misc.jl : Misc functions
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

@doc Markdown.doc"""
    squaredivisors(n::fmpz) -> Iterator

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

@doc Markdown.doc"""
    zeros(f::fmpz_poly) -> Vector{fmpz}

Computes the integer zeros of a given polynomial $f$.
"""
function zeros(f::fmpz_poly)

  fac = factor(f)
  zeros = Nemo.fmpz[]

    # check if there are monic linear factors <-> zeros
  for i in fac
    if degree(i[1]) == 1 && leading_coefficient(i[1]) == 1
      push!(zeros, -coeff(i[1],0))
    end
  end

  return zeros
end

################################################################################
#
# Test if element has a squareroot
#
################################################################################

@doc Markdown.doc"""
    is_square(x::ResElem{fmpz}) -> (Bool, ResElem)

Checks if an element $x$ of a ResidueRing of $Z$ is a square, say of y
returns (true, y) in that case and (false, 0) otherwise
"""
function Nemo.is_square_with_sqrt(x::ResElem{fmpz})
    R = parent(x)
    p = modulus(R)
    xnew = x.data

    j = jacobi_symbol(xnew, p)
    if j == 0
        return true, zero(R)
    elseif j == 1
        root = sqrtmod(xnew, p)
        return true, R(root)
    else
        return false, zero(R)
    end
end

function Nemo.is_square_with_sqrt(x::Union{nmod, gfp_elem})
    R = parent(x)
    p = modulus(R)
    xnew = x.data

    j = jacobi_symbol(fmpz(xnew), fmpz(p))
    if j == 0
        return true, zero(R)
    elseif j == 1
        root = sqrtmod(fmpz(xnew), fmpz(p))
        return true, R(root)
    else
        return false, zero(R)
    end
end


@doc Markdown.doc"""
    is_square(x::FinFieldElem) -> (Bool, FinFieldElem)

Checks if an element $x$ of $\mathbf F_q$ is a square, say of $y$.
Returns `(true, y)` in that case and `(false, 0)` otherwise
"""
function Nemo.is_square_with_sqrt(x::FinFieldElem)
    R = parent(x)
    S, t = PolynomialRing(R, "t", cached = false)

    # check if x is a square by considering the polynomial f = t^2 - x
    # x is a square in F_q iff f has a root in F_q
    f = t^2 - x
    fac = factor(f)

    p = first(keys(fac.fac))

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

# @doc Markdown.doc"""
#     quadroots(a::fmpz, b::fmpz, c::fmpz, p::fmpz) -> Bool
#
# Returns true if the quadratic congruence of the quadratic polynomial
# $ax^2 + bx + c = 0$ has a root modulo $p$.
# """
function quadroots(a, b, c, p)
  F_p = GF(p, cached = false)
  R, x = PolynomialRing(F_p, "x", cached = false)
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

function quadroots(a, b, c, pIdeal:: NfOrdIdl)
  R = order(pIdeal)
  F, phi = ResidueField(R, pIdeal)
  P, x = PolynomialRing(F, "x", cached = false)
  f = phi(R(a))*x^2 + phi(R(b))*x + phi(R(c))

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

@doc Markdown.doc"""
    nrootscubic(b::fmpz, c::fmpz, d::fmpz, p::fmpz) -> fmpz

Returns the number of roots of the polynomial $x^3 + bx^2 + cx + d = 0$
modulo $p$.
"""
function nrootscubic(b, c, d, p)
  F_p = GF(p, cached = false)
  R, x = PolynomialRing(F_p, "x")
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

function nrootscubic(b, c, d, pIdeal:: NfOrdIdl)
  R = order(pIdeal)
  F, phi = ResidueField(R, pIdeal)
  P, x = PolynomialRing(F, "x", cached = false)
  
  f = x^3 + phi(R(b))*x^2 + phi(R(c))*x + phi(R(d))

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

@doc Markdown.doc"""
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

@doc Markdown.doc"""
	order(R::ResRing{fmpz}) -> Nemo.fmpz

Return the order of a finite field of a residue ring of $\mathbf Z$.
"""
function order(R::ResRing{fmpz})
  return abs(modulus(R))
end

@doc Markdown.doc"""
    characteristic(R::ResRing{fmpz}) -> Nemo.fmpz

Returns the characteristic of $R$
"""
function characteristic(R::ResRing{fmpz})
  return abs(modulus(R))
end

jacobi_symbol(x::Integer, y::fmpz) = jacobi_symbol(fmpz(x), y)

@doc Markdown.doc"""
	inv_mod(a::NfOrdElem, I::NfOrdIdl) -> NfOrdElem

Return a lift of the inverse of an element modulo a prime ideal.
"""
function Base.invmod(a::NfOrdElem, I::NfOrdIdl)
  R = order(I)
  k, phi = ResidueField(R, I)
  return preimage(phi, inv(phi(R(a))))
end

@doc Markdown.doc"""
	pth_root_mod(a::NfOrdElem, I::NfOrdIdl) -> NfOrdElem

Return a lift of the pth root of an element mod a prime ideal lying over p.
"""
function pth_root_mod(a::NfOrdElem, I::NfOrdIdl)
  R = order(I)
  p = pIdeal.gen_one
  k, phi = ResidueField(R, I)
  return preimage(phi, pth_root(phi(R(a))))
end


