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

doc"""
***
    Divisors(n::fmpz) -> Array{fmpz, 1}

> Computes the divisors of a given number $n$. It is assumed that $n$ is not
> zero.
"""
function divisors(n)
  n == 0 && error("The number must be nonzero")
  # special cases
  if (n == 1) || (n == -1)
    return fmpz[1,-1]
  end
  if (n == 0)
    return fmpz[]
  end
  
  if n < 0
    n = -n
  end

  d = isqrtrem(n) # d = (s,r) where s is sqrt(n) rounded down and r = n - s^2
  divi = Nemo.fmpz[]

  i = d[1]+1
  while i <= n
    if mod(n,i) == 0
      # add i and n/i to list of divisors (and their negative)
      push!(divi,i)
      push!(divi,-i)
      push!(divi, div(n,i))
      push!(divi, -div(n,i))
    end
    i = i + 1
  end
  
  # case where n is a square. then d[1] = sqrt(n) is a divisor
  if d[2] == 0 
    push!(divi,d[1])
    push!(divi,-d[1])
  end
  return divi
end

doc"""
***
    squaredivisors(n::fmpz) -> Array{fmpz, 1}

> Computes the numbers whose square divides a given number $n$. It is assumed
> that $n$ is not zero.
"""
function squaredivisors(n)
  n == 0 && error("The number must be nonzero")  
  divi = Nemo.fmpz[]
  divis = divisors(n)
  for i in 1:length(divis)
    if mod(n, divis[i]^2) == 0
      push!(divi, divis[i])
    end
  end
        
  return divi
end

################################################################################
#
#  Roots of integer polynomials
#
################################################################################

doc"""
***
  zeros(f::fmpz_poly) -> Array{fmpz, 1}

> Computes the integer zeros of a given polynomial $f$.
"""
function zeros(f::fmpz_poly)

  fac = factor(f)
  zeros = Nemo.fmpz[]
    
    # check if there are monic linear factors <-> zeros
  for i in fac
    if degree(i[1]) == 1 && lead(i[1]) == 1
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

doc"""
***
  issquare(x::ResElem{fmpz}) -> (Bool, ResElem)

> Checks if an element x of a ResidueRing of $Z$ is a square, say of y
> returns (true, y) in that case and (false, 0) otherwise 
"""
function issquare(x::ResElem{fmpz})
    R = parent(x)
    p = modulus(R)
    xnew = x.data
    
    j = jacobi(xnew, p)
    if j == 0
        return true, zero(R)
    elseif j == 1
        root = sqrtmod(xnew, p)
        return true, R(root)
    else
        return false, zero(R)
    end
end

doc"""
***
    issquare(x::FinFieldElem) -> (Bool, FinFieldElem)

> Checks if an element $x$ of $\mathbf F_q$ is a square, say of $y$.
> Returns `(true, y)` in that case and `(false, 0)` otherwise 
"""
function issquare(x::FinFieldElem)
    R = parent(x)
    S, t = PolynomialRing(R, "t")
    
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

doc"""
***
  quadroots(a::fmpz, b::fmpz, c::fmpz, p::fmpz) -> Bool

> Returns true if the quadratic congruence if the quadratic polynomial
> $ax^2 + bx + c = 0$ has a root modulo $p$.
"""
function quadroots(a, b, c, p)
  F_p = ResidueRing(ZZ, p)
  R, x = PolynomialRing(F_p, "x")
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

doc"""
***
    nrootscubic(b::fmpz, c::fmpz, d::fmpz, p::fmpz) -> fmpz

> Returns the number of roots of the polynomial $x^3 + bx^2 + cx + d = 0$
> modulo $p$.
"""
function nrootscubic(b, c, d, p)
  F_p = ResidueRing(ZZ, p)
  R, x = PolynomialRing(F_p, "x")
  f = x^3 + F_p(b)*x^2 + F_p(c)*x + F_p(d)
  
  fac = factor(f)
  
  if length(fac) == 1
    if fac[first(keys(fac.fac))] == 3
      return ZZ(3)
    else
      return ZZ(0)
    end
  elseif length(fac) == 2
    if fac[first(keys(fac))]== 1 && fac[first(keys(fac))] == 1
      # one linear and one irreducible quadratic factor
      return ZZ(1)
    else 
      return ZZ(3) #one double and one single root
    end
  else 
    return ZZ(3)
  end  
end

function smod{T, S}(a::T, b::S)
  z = mod(a, b)
  if 2*z > b
    z = z - b
  end
  return z
end


doc"""
***
		order(R::ResRing{fmpz}) -> Nemo.fmpz
> Returns the order of a finite field of a residue ring of $\mathbf Z$.
""" 
function order(R::ResRing{fmpz})
  return abs(modulus(R))
end

doc"""
characteristic(R::ResRing{fmpz}) -> Nemo.fmpz
> Returns the characteristic of R
"""
function characteristic(R::ResRing{fmpz})
  return abs(modulus(R))
end

function characteristic(R::FlintRationalField)
  return fmpz(0)
end

