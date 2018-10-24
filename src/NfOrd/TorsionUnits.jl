################################################################################
#
#    NfOrd/TorsionUnits.jl : Torsion units in generic number field orders 
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
#
#  Copyright (C) 2015, 2016 Tommy Hofmann
#
################################################################################

export torsion_unit_group

################################################################################
#
#  Torsion unit test
#
################################################################################

@doc Markdown.doc"""
***
    istorsion_unit(x::NfOrdElem, checkisunit::Bool = false) -> Bool

> Returns whether $x$ is a torsion unit, that is, whether there exists $n$ such
> that $x^n = 1$.
> 
> If `checkisunit` is `true`, it is first checked whether $x$ is a unit of the
> maximal order of the number field $x$ is lying in.
"""
function istorsion_unit(x::NfOrdElem, checkisunit::Bool = false)
  return istorsion_unit(x.elem_in_nf, checkisunit)
end

################################################################################
#
#  Order of a single torsion unit
#
################################################################################

@doc Markdown.doc"""
***
    torsion_unit_order(x::NfOrdElem, n::Int)

> Given a torsion unit $x$ together with a multiple $n$ of its order, compute
> the order of $x$, that is, the smallest $k \in \mathbb Z_{\geq 1}$ such
> that $x^k = 1$.
>
> It is not checked whether $x$ is a torsion unit.
"""
function torsion_unit_order(x::NfOrdElem, n::Int)
  return torsion_unit_order(x.elem_in_nf, n)
end

################################################################################
#
#  Functions for user
#
################################################################################

@doc Markdown.doc"""
***
    torsion_units(O::NfOrd) -> Array{NfOrdElem, 1}

> Given an order $O$, compute the torsion units of $O$.
"""
function torsion_units(O::NfOrd)
  ord, g = _torsion_units(O)
  res = Array{NfOrdElem, 1}(undef, ord)
  res[1] = O(1)
  res[2] = g
  for i = 3:ord
    res[i] = g*res[i-1]
  end
  return res
end

@doc Markdown.doc"""
***
    torsion_units_gen(O::NfOrd) -> NfOrdElem

> Given an order $O$, compute a generator of the torsion units of $O$.
"""
function torsion_units_gen(O::NfOrd)
  return _torsion_units(O)[2]
end

@doc Markdown.doc"""
***
    torsion_units_gen_order(O::NfOrd) -> NfOrdElem

> Given an order $O$, compute a generator of the torsion units of $O$ as well as its order.
"""
function torsion_units_gen_order(O::NfOrd)
  ord, g = _torsion_units(O)
  return g, ord
end

@doc Markdown.doc"""
***
    torsion_unit_group(O::NfOrd) -> GrpAb, Map

> Given an order $O$, returns the torsion units as an abelian group $G$
> together with a map $G \to \mathcal O^\times$.
"""
function torsion_unit_group(O::NfOrd)
  ord, g = _torsion_units(O)
  f = AbToNfOrdMultGrp(O, ord, g)
  return domain(f), f
end

function _torsion_units(O::NfOrd)
   if isdefined(O, :torsion_units)
    return O.torsion_units
  end

  z = _torsion_units_gen(O)
  O.torsion_units = z
  return O.torsion_units
end

################################################################################
#
#  Torsion units via lattice enumeration
#
################################################################################


function _torsion_units_lattice_enum(O::NfOrd)
  n = degree(O)
  K = nf(O)
  r1, r2 = signature(K)
  B = basis(O)

  if r1 > 0
    return [ O(1), -O(1) ], -O(1)
  end

  function _t2_pairing(x, y, p)
    local i
    v = minkowski_map(x, p)
    w = minkowski_map(y, p)
 
    t = zero(parent(v[1]))
 
    for i in 1:r1
      t = t + v[i]*w[i]
    end
 
    for i in (r1 + 1):(r1 + 2*r2)
      t = t + v[i]*w[i]
    end
 
    return t
  end

  p = 64

  gram_found = false

  could_enumerate = false

  A = ArbField(p, false)
  M = ArbMatSpace(A, n, n,false)()
  
  while true
    A = ArbField(p, false)
    M = ArbMatSpace(A, n, n, false)()

    gram_found = true

    @vprint :UnitGroup 1 "Computing Gram matrix with precision $p ... \n"

    for i in 1:n, j in 1:n
      M[i,j] = _t2_pairing(B[i], B[j], p)
      if !isfinite(M[i, j])
        p = 2*p
        gram_found = false
        break
      end
    end

    if gram_found
      break
    end
  end

  @vprint :UnitGroup 1 "Gram matrix is $M\n"

  @vprint :UnitGroup 1 "Enumerating elements with T_2 bounded by $n ... \n"
  l = enumerate_using_gram(M, A(n))

  R = Array{NfOrdElem, 1}()

  for i in l
    if O(i) == zero(O)
      continue
    end
    if istorsion_unit(O(i))
      push!(R, O(i))
    end
  end

  i = 0

  for outer i in 1:length(R)
    if torsion_unit_order(R[i], length(R)) == length(R)
      break
    end
  end

  return R, R[i]
end

################################################################################
#
#  Torsion units via root lifting
#
################################################################################

# For each n _euler_phi_inverse_maximum_ is the maximal i,
# such that varphi(i) divides n
#
# Magma code:
# [Maximum(&cat[ EulerPhiInverse(d) : d in Divisors(n)  | #EulerPhiInverse(d) ne 0 ]) : n in [1..250]];
const _euler_phi_inverse_maximum =
[ 2, 6, 2, 12, 2, 18, 2, 30, 2, 22, 2, 42, 2, 6, 2, 60, 2, 54, 2, 66, 2, 46, 2,
90, 2, 6, 2, 58, 2, 62, 2, 120, 2, 6, 2, 126, 2, 6, 2, 150, 2, 98, 2, 138, 2,
94, 2, 210, 2, 22, 2, 106, 2, 162, 2, 174, 2, 118, 2, 198, 2, 6, 2, 240, 2,
134, 2, 12, 2, 142, 2, 270, 2, 6, 2, 12, 2, 158, 2, 330, 2, 166, 2, 294, 2, 6,
2, 276, 2, 62, 2, 282, 2, 6, 2, 420, 2, 6, 2, 250, 2, 206, 2, 318, 2, 214, 2,
378, 2, 242, 2, 348, 2, 18, 2, 354, 2, 6, 2, 462, 2, 6, 2, 12, 2, 254, 2, 510,
2, 262, 2, 414, 2, 6, 2, 274, 2, 278, 2, 426, 2, 6, 2, 630, 2, 6, 2, 298, 2,
302, 2, 30, 2, 46, 2, 474, 2, 6, 2, 660, 2, 486, 2, 498, 2, 334, 2, 588, 2, 22,
2, 346, 2, 118, 2, 690, 2, 358, 2, 594, 2, 6, 2, 564, 2, 18, 2, 12, 2, 382, 2,
840, 2, 6, 2, 394, 2, 398, 2, 750, 2, 6, 2, 618, 2, 6, 2, 636, 2, 422, 2, 642,
2, 6, 2, 810, 2, 6, 2, 726, 2, 446, 2, 870, 2, 454, 2, 458, 2, 94, 2, 708, 2,
158, 2, 12, 2, 478, 2, 1050, 2, 46, 2, 12, 2, 166, 2, 30, 2, 502 ]

# One should/could also try to be closer to Algorithm 1
# in Molin, "On the calculation of roots of unity in a number field"
function _torsion_group_order_divisor(O::NfOrd, N::Int = 5)

  if degree(O) <= 250
    upper_bound = _euler_phi_inverse_maximum[degree(O)]
  else
    error("Not implemented yet")
  end

  p = upper_bound + 1
  m = fmpz(0)
  stable = 0

  first = true

  while true
    p = next_prime(p)
    if isramified(O, p) || isindex_divisor(O, p)
      continue
    end
    lp = prime_decomposition_type(O, p)

    m_new = m

    for (f, e) in lp
      m_new = gcd(m_new, fmpz(p)^f - 1)
    end

    if first
      m_new, _ = ppio(m_new, discriminant(O))
      if isodd(m_new)
        m_new = 2 * m_new
      end
      first = false
    end
    
    if m_new == 2
      return fmpz(2)
    end

    if m_new == m
      stable += 1
    else
      stable = 0
    end

    if stable == 5 && m_new <= upper_bound
      return m_new
    end

    m = m_new
  end
end

function _torsion_units_lifting(O::NfOrd)

  r1, r2 = signature(O)

  if r1 > 0
    return [ O(1), -O(1) ], -O(1)
  end

  m = _torsion_group_order_divisor(O)
  Oy, y = PolynomialRing(O, "y", cached = false)
  f = y^Int(m) - 1
  R = _roots_hensel(f)

  i = 1
  for outer i in 1:length(R)
    if torsion_unit_order(R[i], length(R)) == length(R)
      break
    end
  end

  @assert O(-1) in R

  return R, R[i]
end

function _torsion_units_gen(O::NfOrd)
  r1, r2 = signature(O)

  if r1 > 0
    return 2, O(-1)
  end

  m = _torsion_group_order_divisor(O)
  Ky, y = PolynomialRing(nf(O), "y", cached = false)
  fac = factor(m).fac
  gen = O(1)
  ord = 1
  for (p, v) in fac
    if p == 2 && v == 1
      mul!(gen, gen, O(-1))
      ord *= 2
      continue
    end
    for i = 1:v
      f = divexact(y^(Int(p)^(v+1-i)) - 1, y^(Int(p)^(v-i)) - 1)
      R = _roots_hensel(f, 1)
      if !isempty(R)
        mul!(gen, gen, O(R[1]))
        ord *= Int(p)^(v+1-i)
        break
      end
    end  
  end

  return ord, gen

end
