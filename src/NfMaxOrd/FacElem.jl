################################################################################
#
# NfMaxOrd/FacElem.jl : Factored elements over number fields
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
  return FacElem(x.R, [ y[j, i] for i in 1:cols(y) ])
end

# Get the trivial factored element from an ordinary element
function FacElem(x::nf_elem)
  z = FacElem{nf_elem}()
  z.fac[x] = fmpz(1)
  z.parent = FacElemMon{nf_elem}(parent(x))
  return z
end

base_ring(x::nf_elem) = parent(x)

function is_unit(x::FacElem{nf_elem})
  return abs(norm(x)) == 1
end

function is_torsion_unit{T}(x::FacElem{T}, checkisunit::Bool = false, p::Int = 16)
  @vprint :UnitGrp 1 "Checking if factored element is torsion\n"
  if checkisunit
    _is_unit(x) ? nothing : return false
  end

  K = base_ring(x)
  d = degree(K)
  r, s = signature(K)

  while true

    if nbits(p) > 15
      error("Precision is too high")
    end

    @vprint :UnitGrp 2 "Precision is now $(p) \n"
    l = 0
    @vprint :UnitGrp 2 "Computing conjugates ... \n"
    @v_do :UnitGrp 2 pushindent()
    cx = conjugates_arb_log(x, -p)
    @v_do :UnitGrp 2 popindent()
    @vprint :UnitGrp 2 "Conjugates log are $cx\n"
    A = ArbField(p)
    B = log(A(1) + A(1)//A(6) * log(A(d))//A(d^2))
    for i in 1:r
      k = abs(cx[i])
      if ispositive(k)
        return false
      elseif isnonnegative(B - k)
        l = l + 1
      end
    end
    for i in 1:s
      k = cx[r + i]//2
      if ispositive(k)
        return false
      elseif isnonnegative(B - k)
        l = l + 1
      end
    end

    if l == r + s
      return true
    end

    p = 2*p

  end
end

function norm(x::FacElem{nf_elem})
  z = fmpq(1)
  for a in base(x)
    z = z*norm(a)^x.fac[a]
  end
  return z
end

_base_ring(x::nf_elem) = parent(x)::AnticNumberField

_base_ring(x::FacElem{nf_elem}) = base_ring(x)::AnticNumberField

*(x::FacElem{nf_elem}, y::NfOrdElem) = x*elem_in_nf(y)

*(x::NfOrdElem, y::FacElem{nf_elem}) = y*x

function _conjugates_arb_log(A::FacElemMon{nf_elem}, a::nf_elem, abs_tol::Int)
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

function conjugates_arb(x::FacElem{nf_elem}, abs_tol::Int)
  d = degree(_base_ring(x))
  res = Array(acb, d)

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

function conjugates_arb_log(x::FacElem{nf_elem}, abs_tol::Int)
  K = _base_ring(x)
  r1, r2 = signature(K)
  d = r1 + r2
  res = Array(arb, d)

  i = 1

  for a in base(x)
    z = _conjugates_arb_log(parent(x), a, abs_tol)
    if i == 1
      for j in 1:d
        res[j] = x.fac[a]*z[j]
      end
    else
      for j in 1:d
        res[j] = res[j] + x.fac[a]*z[j]
      end
    end
    i = i + 1
  end

  return res
end

function conjugates_arb_log(x::FacElem{nf_elem}, R::ArbField)
  z = conjugates_arb_log(x, -R.prec)
  return map(R, z)
end

