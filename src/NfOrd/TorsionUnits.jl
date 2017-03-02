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

################################################################################
#
#  Torsion unit test
#
################################################################################

doc"""
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

doc"""
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
#  Torsion units via lattice enumeration
#
################################################################################

doc"""
***
    torsion_units(O::NfOrd) -> Array{NfOrdElem, 1}

> Given an order $O$, compute the torsion units of $O$.
"""
function torsion_units(O::NfOrd)
  ar, g = _torsion_units(O)
  return ar
end

doc"""
***
    torsion_units(O::NfOrd) -> NfOrdElem

> Given an order $O$, compute a generator of the torsion units of $O$.
"""
function torsion_units_gen(O::NfOrd)
  ar, g = _torsion_units(O)
  return g
end

function _torsion_units(O::NfOrd)
   if isdefined(O, :torsion_units)
    return O.torsion_units
  end

  z = _torsion_units_lifting(O)
  O.torsion_units = z
  return O.torsion_units
end

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

  A = ArbField(p)
  M = ArbMatSpace(A, n, n)()
  
  while true
    A = ArbField(p)
    M = ArbMatSpace(A, n, n)()

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

  for i in 1:length(R)
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

function _torsion_group_order_divisor(O::NfOrd, N::Int = 5)

  p = 1
  m = fmpz(0)
  m_old = fmpz(0)
  stable = 0

  while true
    p = next_prime(p)
    if isramified(O, p)
      continue
    end
    lp = prime_decomposition(O, p)
    m_new = m_old
    for (P, e) in lp
      m_new = gcd(m_new, norm(P) - 1)
    end

    if m_new == m_old
      stable += 1
    end

    if stable == 5
      return m_new
    end

    m_old = m_new
  end
end

function _torsion_units_lifting(O::NfOrd)

  r1, r2 = signature(O)

  if r1 > 0
    return [ O(1), -O(1) ], -O(1)
  end

  m = _torsion_group_order_divisor(O)
  Oy, y = O["y"]
  f = y^Int(m) - 1
  R = _roots_hensel(f)

  i = 1
  for i in 1:length(R)
    if torsion_unit_order(R[i], length(R)) == length(R)
      break
    end
  end

  if !(O(-1) in R)
    push!(R, O(-1))
  end

  return R, R[i]
end

