################################################################################
#
#          GenNfOrdUnits.jl : Units in generic number field orders 
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
#  Copyright (C) 2015 Tommy Hofmann
#
################################################################################

export UnitGrpCtx

export is_unit, is_torsion_unit, is_independent

type UnitGrpCtx
  order::GenNfOrd
  rank::Int
  units::Array{NfOrderElem, 1}
  regulator::arb
  tentative_regulator::arb
  regulator_precision::Int
  torsion_unit::NfOrderElem
  torsion_units_order::Int

  function UnitGrpCtx(O::GenNfOrd)
    z = new()
    z.order = O
    z.rank = -1
    z.regulator_precision = -1
    z.torsion_units_order = -1
    z.units = Array{NfOrderElem, 1}()
    return z
  end
end

function unit_rank(O::GenNfOrd)
  r1, r2 = signature(nf(O))
  return r1 + r2 - 1
end

function is_unit(x::NfOrderElem)
  return abs(norm(x)) == 1 
end

################################################################################
#
#  Torsion units
#
################################################################################

function is_torsion_unit(x::NfOrderElem)
  !is_unit(x) && return false
  # test for the signature etc
  c = conjugate_data(parent(x))
  _find_real(c)
  d = degree(parent(x))
  while true
    l = 0
    #println("precision is $(c.prec)")
    for i in 1:degree(parent(x))
      k = abs(_evaluate(parent(nf(parent(x)).pol)(x.elem_in_nf), c.roots[i]))
      A = parent(k)
      if ispositive(k - A(1))
        return false
      elseif isnonnegative( A(1) + A(1)/A(6) * log(A(d))/A(d^2) - k)
        l = l + 1
      end
    end
    if l == d
      return true
    end
    refine(c)
    _find_real(c)
  end
end

function is_independent(x::Array{nf_elem, 1}, rts::acb_root_ctx)
  K = parent(x[1])
  deg = degree(K)
  r, s = signature(K)
  rr = r + s
  while true
    println("precision is $(rts.prec)");
    A = ArbMatSpace(length(x), r + s, rts.prec)()
    Ar = ArbField(rts.prec)
    for k in 1:length(x)
      for i in 1:r
        A[k, i] = log(abs(_evaluate(parent(K.pol)(x[k]), rts.real_roots[i])))
      end
      for i in 1:s
        A[k, r + i] = 2*log(abs(_evaluate(parent(K.pol)(x[k]), rts.complex_roots[i])))
      end
    end
    B = A*transpose(A)
    C = parent(B)()
    p = Array(Cint, B.r)
    d = det(B)
    y = ((Ar(1)/sqrt(Ar(rr)))^rr * (Ar(21)/Ar(128) * log(Ar(deg))/(Ar(deg)^2))^rr)^2
    println(y,d)
    if isfinite(d) && ispositive(y - d)
      return false
    elseif isfinite(d) && ispositive(d)
      return true
    end
    refine(rts)
    _find_real(rts)
  end
end

function is_independent(x::Array{nf_elem, 1})
  println("testing if $x are independent")
  K = parent(x[1])
  deg = degree(K)
  r,s = signature(K)
  rr = r + s
  rts = acb_root_ctx(K.pol, 64)
  _find_real(rts)
  return is_independent(x, rts)
end

function is_independent(x::Array{NfOrderElem, 1})
  rts = conjugate_data(parent(x[1]))
  return is_independent([ deepcopy(y.elem_in_nf) for y in x] , rts)
end

function torsion_units(O::GenNfOrd)
  n = degree(O)
  K = nf(O)
  rts = conjugate_data(O)
  _find_real(rts)
  A = ArbField(rts.prec)
  M = ArbMatSpace(n, n, rts.prec)()
  r1, r2 = signature(O)
  for i in 1:n
    for j in 1:n
      t = AcbField(rts.prec)(0)
      for k in 1:n
        t = t + _evaluate(parent(K.pol)(basis(O)[i].elem_in_nf), rts.roots[k])*conj(_evaluate(parent(K.pol)(basis(O)[j].elem_in_nf), rts.roots[k]))
      end
      M[i,j] = real(t)
    end
  end
  #println(M)
  l = enumerate_using_gram(M, A(n))
  #println(l)
  R = Array{NfOrderElem, 1}()
  for i in l
    if is_torsion_unit(O(i))
      push!(R, O(i))
    end
  end
  return R
end

function conjugate(x::NfOrderElem, i::Int)
  rts = conjugate_data(parent(x))
  _find_real(rts)
  K = nf(parent(x))
  return _evaluate(parent(K.pol)(x.elem_in_nf), rts.roots[i])
end

################################################################################
#
#  Free part of the unit group
#
################################################################################

function _reg(x::Array{nf_elem, 1})
   K = parent(x[1])
  deg = degree(K)
  r,s = signature(K)
  rr = r + s
  rts = acb_root_ctx(K.pol, 256)
  _find_real(rts)
  println("precision is $(rts.prec)");
  A = ArbMatSpace(length(x), r + s - 1, rts.prec)()
  Ar = ArbField(rts.prec)
  g = fmpq_poly()
  
  if r > 1
      r = r - 1
  else
      s = s - 1
  end

  for k in 1:length(x)

    for i in 1:r
      A[k, i] = log(abs(_evaluate(parent(K.pol)(x[k]), rts.real_roots[i])))
    end
    for i in 1:s
      A[k, r + i] = 2*log(abs(_evaluate(parent(K.pol)(x[k]), rts.complex_roots[i])))
    end
  end
  return det(A)
end

order(u::UnitGrpCtx) = u.order

function _unit_group_find_units(u::UnitGrpCtx, x::ClassGrpCtx)
  O = order(u)
  ker, rnk = nullspace(transpose(fmpz_mat(x.M)))
  rnk = Int(rnk)
  ker = transpose(ker)
  K = nf(order(x.FB.ideals[1]))
  r = unit_rank(O)
  r1, r2 = signature(O)


#  if length(K) < r
#    println("Kernel has dimension $(length(K)) but unit rank is $(r)")
#  end

  A = u.units

  a = K(1)

  j = 0

  for j in 1:rnk
    for i in 1:cols(ker)
      if ker[j, i] == 0 
        continue
      end
      a = a * (x.R[i])^(Int(ker[j, i]))
    end
    break
  end

  y = O(a, false)

  if !is_torsion_unit(y)
    push!(A, y)
  end

  while(length(A) < r)
    j = j + 1
    if j > rows(ker)
      println("found $(length(A)) many units but i need $r many")
      return length(A)
    end
    if is_zero_row(ker, j)
      continue
    end

    a = K(1)

    for i in 1:cols(ker)
      if ker[j, i] == 0
        continue
      end
      println("multiplying with $(x.R[i]^Int(ker[j, i])))")
      a = a * (x.R[i])^(Int(ker[j, i]))
      println("now a is $a")
    end

    y = O(a, false)
    
    if is_torsion_unit(y)
      continue
    end
    _add_unit(u, y)
  end
  u.tentative_regulator = _reg( [ y.elem_in_nf for y in u.units ])

  AA = ArbMatSpace(r, r, conjugate_data(O).prec)()

  println(AA)

  if r1 > 1
      r1 = r1 - 1
  else
      r2 = r2 - 1
  end


  for k in 1:r
    for i in 1:r1
      AA[k, i] = log(abs(_evaluate(parent(K.pol)(u.units[k].elem_in_nf), conjugate_data(O).real_roots[i])))
    end
    for i in 1:r2
      AA[k, r1 + i] = 2*log(abs(_evaluate(parent(K.pol)(u.units[k].elem_in_nf), conjugate_data(O).complex_roots[i])))
    end
  end

  A_all = ArbMatSpace(rnk, r, conjugate_data(O).prec)()

  for k in 1:rnk
    a = K(1)
    for i in 1:cols(ker)
      if ker[k, i]  == 0
        continue
      end
      a = a * (x.R[i])^(Int(ker[k, i]))
    end
    if is_torsion_unit(O(a, false))
      continue
    end
    println("$k, $a")
    for i in 1:r1
      A_all[k, i] = log(abs(_evaluate(parent(K.pol)(a), conjugate_data(O).real_roots[i])))
    end
    for i in 1:r2
      A_all[k, r1 + i] = 2*log(abs(_evaluate(parent(K.pol)(a), conjugate_data(O).complex_roots[i])))
    end
  end

  X = A_all * inv(AA)

  return X
end

function _add_unit(u::UnitGrpCtx, x::NfOrderElem)
  if is_independent( vcat(u.units, [ x ]))
    push!(u.units, x)
  end
  nothing
end

