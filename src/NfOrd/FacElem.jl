################################################################################
#
# NfOrd/FacElem.jl : Factored elements over number fields
#
# This file is part of hecke.
#
# Copyright (c) 2015: Claus Fieker, Tommy Hofmann
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

# Get FacElem from ClassGrpCtx
function FacElem(x::ClassGrpCtx, y::fmpz_mat, j::Int)
  return FacElem(x.R, [ deepcopy(y[j, i]) for i in 1:cols(y) ])
end

function FacElem(x::ClassGrpCtx, y::Array{fmpz, 1})
  return FacElem(x.R, [ deepcopy(y[i]) for i in 1:length(y) ])
end

# Get the trivial factored element from an ordinary element
function FacElem(x::nf_elem)
  z = FacElem{nf_elem, AnticNumberField}()
  z.fac[x] = fmpz(1)
  z.parent = FacElemMon(parent(x))
  return z
end

global _ISTOR = []

function istorsion_unit(x::FacElem{T}, checkisunit::Bool = false, p::Int = 16) where T
  global _ISTOR
  push!(_ISTOR, (x, checkisunit, p))
  @vprint :UnitGroup 1 "Checking if factored element is torsion\n"

  if checkisunit
    _isunit(x) ? nothing : return false
  end

  p = max(nbits(maxabs_exp(x))+nbits(length(x.fac)), p)

  K = base_ring(x)
  d = degree(K)
  r, s = signature(K)

  while true

    if nbits(p) > 15
      error("Precision is too high")
    end

    @vprint :UnitGroup 2 "Precision is now $(p) \n"
    l = 0
    @vprint :UnitGroup 2 "Computing conjugates ... \n"
    @v_do :UnitGroup 2 pushindent()
    cx = conjugates_arb_log(x, p)
    @v_do :UnitGroup 2 popindent()
    @vprint :UnitGroup 2 "Conjugates log are $cx\n"
    A = ArbField(p)
    B = log(A(1) + A(1)//A(6) * log(A(d))//A(d^2))
    for i in 1:r
      k = abs(cx[i])
      if ispositive(k)
        return false, p
      elseif isnonnegative(B - k)
        l = l + 1
      else
        println("fail 1")
      end
    end
    for i in 1:s
      k = cx[r + i]//2
      if ispositive(k)
        return false, p
      elseif isnonnegative(B - k)
        l = l + 1
      else
        println("fail 2")
      end
    end

    if l == r + s
      return true, p
    end

    p = 2*p
  end
end

function norm(x::FacElem{nf_elem})
  b = fmpq[]
  c = fmpz[] 
  for (a, e) in x.fac
    push!(b, norm(a))
    push!(c, e)
  end
  return evaluate(FacElem(b, c))
end

_base_ring(x::nf_elem) = parent(x)::AnticNumberField

_base_ring(x::FacElem{nf_elem}) = base_ring(x)::AnticNumberField

*(x::FacElem{nf_elem}, y::NfOrdElem) = x*elem_in_nf(y)

*(x::NfOrdElem, y::FacElem{nf_elem}) = y*x

function _conjugates_arb_log(A::FacElemMon{AnticNumberField}, a::nf_elem, abs_tol::Int)
  if haskey(A.conj_log_cache, abs_tol)
    if haskey(A.conj_log_cache[abs_tol], a)
      return A.conj_log_cache[abs_tol][a]
    else
      z = conjugates_arb_log(a, abs_tol)
      A.conj_log_cache[abs_tol][a] = z
      return z
    end
  else
    A.conj_log_cache[abs_tol] = Dict{nf_elem, arb}()
    z = conjugates_arb_log(a, abs_tol)
    A.conj_log_cache[abs_tol][a] = z
    return z
  end
end

function conjugates_arb(x::FacElem{nf_elem, AnticNumberField}, abs_tol::Int)
  d = degree(_base_ring(x))
  res = Array{acb}(d)

  i = 1

  for a in base(x)
    z = conjugates_arb(a, abs_tol)
    if i == 1
      for j in 1:d
        res[j] = z[j]^x.fac[a]
      end
    else
      for j in 1:d
        res[j] = res[j] * z[j]^x.fac[a]
      end
    end
    i = i + 1
  end

  return res
end

function conjugates_arb_log(x::FacElem{nf_elem, AnticNumberField}, abs_tol::Int)
  K = _base_ring(x)
  r1, r2 = signature(K)
  d = r1 + r2
  res = Array{arb}(d)

  i = 1

  target_tol = abs_tol

  while true
    prec_too_low = false
    for (i, a) in enumerate(base(x))
      z = _conjugates_arb_log(parent(x), a, abs_tol)
      if i == 1
        for j in 1:d
          res[j] = parent(z[j])()
          muleq!(res[j], z[j], x.fac[a])
          if !radiuslttwopower(res[j], -target_tol) || !isfinite(res[j])
            prec_too_low = true
            break
          end
          #res[j] = x.fac[a] * z[j]
        end
      else
        for j in 1:d
          addmul!(res[j], z[j], x.fac[a])
          #res[j] = res[j] + x.fac[a]*z[j]
          if !radiuslttwopower(res[j], -target_tol) || !isfinite(res[j])
            prec_too_low = true
            break
          end
        end
      end
      if prec_too_low
        break
      end
    end
    if prec_too_low
      abs_tol = 2 * abs_tol
      continue
    end

    for j in 1:d
      expand!(res[j], -target_tol)
    end
    return res
  end
end

function conjugates_arb_log(x::FacElem{nf_elem, AnticNumberField}, R::ArbField)
  z = conjugates_arb_log(x, -R.prec)
  return map(R, z)
end

doc"""
    valuation(a::FacElem{nf_elem, AnticNumberField}, P::NfOrdIdl) -> fmpz
> The valuation of $a$ at $P$.
"""
function valuation(a::FacElem{nf_elem, AnticNumberField}, P::NfOrdIdl)
  val = fmpz(0)
  for (a, e) = a.fac
    val += valuation(a, P)*e
  end
  return val
end

doc"""
    valuation(A::FacElem{NfOrdFracIdl, NfOrdFracIdlSet}, p::NfOrdIdl)
    valuation(A::FacElem{NfOrdIdl, NfOrdIdlSet}, p::NfOrdIdl)
> The valuation of $A$ at $P$.
"""
function valuation(A::FacElem{NfOrdIdl, NfOrdIdlSet}, p::NfOrdIdl)
  return sum(valuation(I, p)*v for (I, v) = A.fac)
end

function valuation(A::FacElem{NfOrdFracIdl, NfOrdFracIdlSet}, p::NfOrdIdl)
  return sum(valuation(I, p)*v for (I, v) = A.fac)
end

doc"""
     ideal(O::NfOrd, a::FacElem{nf_elem, AnticNumberField)
> The factored fractional ideal $a*O$.
"""
function ideal(O::NfOrd, a::FacElem{nf_elem, AnticNumberField})
  de = Dict{NfOrdFracIdl, fmpz}()
  for (e, k) = a.fac
    I = ideal(O, e)
    if haskey(de, I)
      de[I] += k
    else
      de[I] = k
    end
  end
  return FacElem(de)
end

#the normalise bit ensures that the "log" vector lies in the same vector space
#well, the same hyper-plane, as the units
doc"""
    conjugates_arb_log_normalise(x::nf_elem, p::Int = 10)
    conjugates_arb_log_normalise(x::FacElem{nf_elem, AnticNumberField}, p::Int = 10)
> The "normalised" logarithms, ie. the array $c_i\log |x^{(i)}| - 1/n\log|N(x)|$,
> so the (weighted) sum adds up to zero.
"""
function conjugates_arb_log_normalise(x::nf_elem, p::Int = 10)
  K = parent(x)
  r,s = signature(K)
  c = conjugates_arb_log(x, p)
  n = sum(c)//degree(K)
  for i=1:r
    c[i] -= n
  end
  for i=r+1:r+s
    c[i] -= n
    c[i] -= n
  end
  return c
end
 
#the normalise bit ensures that the "log" vector lies in the same vector space
#well, the same hyper-plane, as the units
function conjugates_arb_log_normalise(x::FacElem{nf_elem, AnticNumberField}, p::Int = 10)
  K = base_ring(x)
  r,s = signature(K)
  c = conjugates_arb_log(x, p)
  n = sum(c)//degree(K)
  for i=1:r
    c[i] -= n
  end
  for i=r+1:r+s
    c[i] -= n
    c[i] -= n
  end
  return c
end
 
function _conj_arb_log_matrix_normalise_cutoff(u::Array{T, 1}, prec::Int = 32) where T
  z = conjugates_arb_log_normalise(u[1], prec)
  A = ArbMatSpace(parent(z[1]), length(u), length(z)-1)()
  for i=1:length(z)-1
    A[1,i] = z[i]
  end

  for j=2:length(u)
    z = conjugates_arb_log_normalise(u[j], prec)
    for i=1:length(z)-1
      A[j,i] = z[i]
    end
  end
  return A
end

