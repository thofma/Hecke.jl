################################################################################
#
#    AbsSimpleNumFieldOrder/TorsionUnits.jl : Torsion units in generic number field orders
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

@doc raw"""
    is_torsion_unit(x::AbsSimpleNumFieldOrderElem, checkisunit::Bool = false) -> Bool

Returns whether $x$ is a torsion unit, that is, whether there exists $n$ such
that $x^n = 1$.

If `checkisunit` is `true`, it is first checked whether $x$ is a unit of the
maximal order of the number field $x$ is lying in.
"""
function is_torsion_unit(x::AbsSimpleNumFieldOrderElem, checkisunit::Bool = false)
  return is_torsion_unit(x.elem_in_nf, checkisunit)
end

################################################################################
#
#  Order of a single torsion unit
#
################################################################################

@doc raw"""
    torsion_unit_order(x::AbsSimpleNumFieldOrderElem, n::Int)

Given a torsion unit $x$ together with a multiple $n$ of its order, compute
the order of $x$, that is, the smallest $k \in \mathbb Z_{\geq 1}$ such
that $x^k = 1$.

It is not checked whether $x$ is a torsion unit.
"""
function torsion_unit_order(x::AbsSimpleNumFieldOrderElem, n::Int)
  return torsion_unit_order(x.elem_in_nf, n)
end

################################################################################
#
#  Interface: number fields
#
################################################################################

function is_torsion_unit_group_known(K::NumField)
  return has_attribute(K, :torsion_units)
end

function torsion_unit_group(K::NumField)
  ord, gen = _torsion_units_gen(K)
  mp = AbToNfMultGrp(K, ord, gen)
  return domain(mp), mp
end

function torsion_units(K::NumField)
  ord, gen = _torsion_units_gen(K)
  return powers(gen, ord-1)
end

function torsion_units_generator(K::NumField)
  ord, gen = _torsion_units_gen(K)
  return gen
end

function torsion_units_order(K::NumField)
  ord, gen = _torsion_units_gen(K)
  return ord
end

function torsion_units_gen_order(K::NumField)
  ord, gen = _torsion_units_gen(K)
  return gen, ord
end

################################################################################
#
#  Interface: orders
#
################################################################################

@doc raw"""
    torsion_units(O::AbsSimpleNumFieldOrder) -> Vector{AbsSimpleNumFieldOrderElem}

Given an order $O$, compute the torsion units of $O$.
"""
function torsion_units(O::T) where T <: Union{AbsNumFieldOrder, RelNumFieldOrder}
  g, ord = torsion_units_gen_order(O)
  return powers(g, ord-1)
end

@doc raw"""
    torsion_units_generator(O::AbsSimpleNumFieldOrder) -> AbsSimpleNumFieldOrderElem

Given an order $O$, compute a generator of the torsion units of $O$.
"""
function torsion_units_generator(O::T) where T <: Union{AbsNumFieldOrder, RelNumFieldOrder}
  return torsion_units_gen_order(O)[1]
end

@doc raw"""
    torsion_units_gen_order(O::AbsSimpleNumFieldOrder) -> AbsSimpleNumFieldOrderElem

Given an order $O$, compute a generator of the torsion units of $O$ as well as its order.
"""
function torsion_units_gen_order(O::T) where T <: Union{AbsNumFieldOrder, RelNumFieldOrder}
  ord, g = _torsion_units_gen(nf(O))
  if is_maximal_known_and_maximal(O)
    return O(g), ord
  end
  #We need to check which torsion units are in the order.
  lf = factor(ord)
  ord_O = 1
  for (p, v) in lf
    if p == 2 && isone(v)
      ord_O *= 2
      continue
    end
    p_int = Int(p)
    ord_p = p_int^v
    u = g^divexact(ord, ord_p)
    while !(u in O)
      u = u^p_int
      ord_p = divexact(ord_p, p_int)
    end
    ord_O *= ord_p
  end
  #ord_O is the order of the torsion units in O
  @assert iszero(mod(ord, ord_O))
  genO = O(g^divexact(ord, ord_O))
  return genO, ord_O
end

@doc raw"""
    torsion_unit_group(O::AbsSimpleNumFieldOrder) -> GrpAb, Map

Given an order $\mathcal O$, returns the torsion units as an abelian group $G$
together with a map $G \to \mathcal O^\times$.
"""
function torsion_unit_group(O::T) where T <: Union{AbsNumFieldOrder, RelNumFieldOrder}
  g, ord = torsion_units_gen_order(O)
  f = AbToNfOrdMultGrp(O, ord, O(g))
  return domain(f), f
end

################################################################################
#
#  Torsion units via lattice enumeration
#
################################################################################


function _torsion_units_lattice_enum(O::AbsSimpleNumFieldOrder)
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

  local A, M

  while true
    A = ArbField(p; cached=false)
    M = zero_matrix(A, n, n)

    gram_found = true

    @vprintln :UnitGroup 1 "Computing Gram matrix with precision $p ..."

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

  @vprintln :UnitGroup 1 "Gram matrix is $M"

  @vprintln :UnitGroup 1 "Enumerating elements with T_2 bounded by $n ..."
  l = enumerate_using_gram(M, A(n))

  R = Vector{AbsSimpleNumFieldOrderElem}()

  for i in l
    if O(i) == zero(O)
      continue
    end
    if is_torsion_unit(O(i))
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
function _torsion_group_order_divisor(K::AbsSimpleNumField)

  if degree(K) <= 250
    upper_bound = _euler_phi_inverse_maximum[degree(K)]
  else
    error("Not implemented yet")
  end

  p = upper_bound + 1
  m = ZZRingElem(0)
  stable = 0

  first = true

  if is_maximal_order_known(K)
    disc = abs(discriminant(maximal_order(K)))
  elseif is_defining_polynomial_nice(K)
    disc = discriminant(EquationOrder(K))
  else
    disc_1 = discriminant(K.pol)
    disc = numerator(disc_1)*denominator(disc_1)
  end
  threshold = 5*degree(K)

  while true
    p = next_prime(p)
    Rp = Nemo.GF(p, cached=false)
    Rpt, t = polynomial_ring(Rp, "t", cached=false)
    gp = Rpt(K.pol)

    if degree(gp) != degree(K) || !is_squarefree(gp)
      continue
    end

    lp = collect(keys(factor_distinct_deg(gp)))

    minf = minimum(lp)

    if first
      m_new = ZZRingElem(p)^minf - 1
      m_new, _ = ppio(m_new, disc)
      if isodd(m_new)
        m_new = 2 * m_new
      end
      first = false
    else
      m_new = gcd(m, powermod(ZZRingElem(p), minf, m) - 1)
    end

    if m_new == 2
      return ZZRingElem(2)
    end

    if m_new == m
      stable += 1
    else
      stable = 0
    end
    if !is_divisible_by(ZZRingElem(degree(K)), euler_phi(m_new))
      stable = 0
    end

    if stable == threshold && m_new <= upper_bound
      return m_new
    end

    m = m_new
  end
end

function _torsion_group_order_divisor(K::NumField)

  if absolute_degree(K) <= 250
    upper_bound = _euler_phi_inverse_maximum[absolute_degree(K)]
  else
    error("Not implemented yet")
  end

  p = upper_bound + 1
  m = ZZRingElem(0)
  stable = 0

  first = true

  OK = maximal_order(K)
  disc = abs(absolute_discriminant(OK))
  d1 = absolute_discriminant(K)
  threshold = 5*absolute_degree(K)

  while true
    p = next_prime(p)
    if divides(numerator(d1), ZZRingElem(p))[1] || divides(denominator(d1), ZZRingElem(p))[1]

    end
    lP = prime_decomposition(OK, p)

    lp = ZZRingElem[degree(x[1]) for x in lP]

    minf = minimum(lp)

    if first
      m_new = ZZRingElem(p)^minf - 1
      m_new, _ = ppio(m_new, disc)
      if isodd(m_new)
        m_new = 2 * m_new
      end
      first = false
    else
      m_new =  gcd(m, powermod(ZZRingElem(p), minf, m) - 1)
    end

    if m_new == 2
      return ZZRingElem(2)
    end

    if m_new == m
      stable += 1
    else
      stable = 0
    end
    if !is_divisible_by(ZZRingElem(absolute_degree(K)), euler_phi(m_new))
      stable = 0
    end

    if stable == threshold && m_new <= upper_bound
      return m_new
    end

    m = m_new
  end
end


function _torsion_units_gen(K::AbsSimpleNumField)
 return get_attribute!(K, :torsion_units) do
  r1, r2 = signature(K)
  if r1 > 0
    return 2, K(-1)
  end

  m = _torsion_group_order_divisor(K)
  Ky = polynomial_ring(K, "y", cached = false)[1]
  fac = factor(m).fac
  gen = K(1)
  ord = 1
  Zx, x = polynomial_ring(FlintZZ, "x")
  for (p, v) in fac
    if p == 2 && v == 1
      mul!(gen, gen, K(-1))
      ord *= 2
      continue
    end
    for i = v:-1:1
      f = cyclotomic(Int(p)^i, x)
      fK = map_coefficients(K, f, parent = Ky)
      r = _roots_hensel(fK, max_roots = 1, is_normal = true, root_bound = ZZRingElem[one(ZZRingElem) for i in 1:(r1 + r2)])
      if length(r) > 0
        mul!(gen, gen, r[1])
        ord *= Int(p)^(i)
        break
      end
    end
  end
  return ord, gen
 end::Tuple{Int, AbsSimpleNumFieldElem}
end

function _torsion_units_gen(K::NumField)
 return get_attribute!(K, :torsion_units) do
  r1, r2 = signature(K)
  if r1 > 0
    return 2, K(-1)
  end

  m = _torsion_group_order_divisor(K)
  Ky = polynomial_ring(K, "y", cached = false)[1]
  fac = factor(m).fac
  gen = one(K)
  ord = 1
  Zx, x = polynomial_ring(FlintZZ, "x")
  for (p, v) in fac
    if p == 2 && v == 1
      mul!(gen, gen, K(-1))
      ord *= 2
      continue
    end
    for i = v:-1:1
      f = cyclotomic(Int(p)^i, x)
      r = roots(K, f)
      if length(r) > 0
        mul!(gen, gen, r[1])
        ord *= Int(p)^(i)
        break
      end
    end
  end
  return ord, gen
 end::Tuple{Int, elem_type(K)}
end
