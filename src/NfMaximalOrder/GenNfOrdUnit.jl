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

export UnitGrpCtx, FactoredElem, FactoredElemMon

export is_unit, is_torsion_unit, is_independent, pow!

type UnitGrpCtx{T <: Union{nf_elem, FactoredElem{nf_elem}}}
  order::GenNfOrd
  rank::Int
  units::Array{T, 1}
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
    z.units = Array{T, 1}()
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

function is_torsion_unit(x::nf_elem)
  abs(norm(x)) != 1 && return false
  d = degree(parent(x))
  c = conjugate_data_arb(parent(x))

  while true
    l = 0
    cx = conjugates_arb(x)
    A = parent(cx[1])
    for i in 1:degree(parent(x))
      k = cx[i]
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
  end
end

function is_torsion_unit(x::FactoredElem{nf_elem})
  K = base_ring(x)
  d = degree(K)
  c = conjugate_data_arb(K)
  while true
    l = 0
    cx = conjugates_arb(x)
    A = parent(cx[1])
    for i in 1:degree(K)
      k = cx[i]
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
  end
end

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
  end
end

function conjugates_arb(x::nf_elem)
  K = parent(x)
  d = degree(K)
  res = Array(arb, d)
  c = conjugate_data_arb(K)

  for i in 1:d
    res[i] = abs(evaluate(parent(K.pol)(x), c.roots[i]))
    if !isfinite(res[i])
      refine(c)
      return conjugates_arb(x)
    end
  end
  
  return res
end


function conjugates_log(x::nf_elem)
  K = parent(x)  
  d = degree(K)
  r1, r2 = signature(K)
  c = conjugate_data_arb(K)
  println("precision is $(c.prec)");

  # We should replace this using multipoint evaluation of libarb
  z = Array(arb, r1 + r2)
  for i in 1:r1
    z[i] = log(abs(evaluate(parent(K.pol)(x),c.real_roots[i])))
    if !isfinite(z[i])
      refine(c)
      return conjugates_log(x)
    end
  end
  for i in 1:r2
    z[r1 + i] = 2*log(abs(evaluate(parent(K.pol)(x), c.complex_roots[i])))
    if !isfinite(z[r1 + i])
      refine(c)
      return conjugates_log(x)
    end
  end
  return z
end

function is_independent{T <: Union{nf_elem, FactoredElem{nf_elem}}}(x::Array{T, 1})
  # I should first check if there are enough units ...
  # this is bad
  if eltype(x) == nf_elem
    K = parent(x[1])::NfNumberField
  elseif eltype(x) == FactoredElem{nf_elem}
    K = base_ring(x[1])::NfNumberField
  end
  deg = degree(K)
  r1, r2 = signature(K)
  c = conjugate_data_arb(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  while true
    println("precision is $(c.prec)");
    A = ArbMatSpace(length(x), rr, c.prec)()::arb_mat
    Ar = ArbField(c.prec)
    for k in 1:length(x)
      conlog = conjugates_log(x[k])
      for i in 1:rr
        A[k, i] = conlog[i]
      end
    end
    B = A*transpose(A)
    C = parent(B)()
    p = Array(Cint, B.r)
    d = det(B)
    y = (Ar(1)/Ar(r))^r * (Ar(21)/Ar(128) * log(Ar(deg))/(Ar(deg)^2))^(2*r)
    println(y, d)
    if isfinite(d) && ispositive(y - d)
      return false
    elseif isfinite(d) && ispositive(d)
      return true
    end
    refine(c)
  end
end

function add_dependent_unit{S, T <: Union{nf_elem, FactoredElem{nf_elem}}}(x::Array{T, 1}, y::S)
  # I need to find a relation

  if eltype(x) == nf_elem
    K = parent(x[1])::NfNumberField
  elseif eltype(x) == FactoredElem{nf_elem}
    K = base_ring(x[1])::NfNumberField
  end
  deg = degree(K)
  r1, r2 = signature(K)
  c = conjugate_data_arb(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  println("precision is $(c.prec)");
  A = ArbMatSpace(length(x), rr, c.prec)()
  b = ArbMatSpace(1, rr, c.prec)()
  Ar = ArbField(c.prec)
  for k in 1:length(x)
    conlog = conjugates_log(x[k])
    println("logs of $(x[k]): $conlog")
    for i in 1:rr
      A[k, i] = conlog[i]
    end
  end
  conlog = conjugates_log(y)
  for i in 1:rr
    b[1,i] = conlog[i]
  end
  println(A)
  B = A*transpose(A)
  println(B)
  B = transpose(A)*inv(B)
  println(B)
  v = b*B

  z = Array(fmpq, r)

  rreg = abs(_reg(x)) # use submatrix of A instead or store it

  println(midpoint(20*rreg))

  bound = fmpz(BigInt(ceil(BigFloat(midpoint(20*rreg))))) # fix this

  for i in 1:r
    z[i] = approximate(v[1, i], bound)
  end

  dlcm = den(z[1])

  for i in 2:length(z)
    dlcm = lcm(dlcm, den(z[i]))
  end

  zz = Array(fmpz, r + 1)

  for i in 1:r
    zz[i] = num(z[i]*dlcm)
  end 

  zz[r + 1] = -dlcm

  if !check_relation_mod_torsion(x, y, zz)
    error("Relation is wrong")
  end

  g = zz[1]

  for i in 1:length(zz)
    g = gcd(g, zz[i])
    if g == 1
      break
    end
  end

  for i in 1:length(zz)
    zz[i] = div(zz[i], g)
  end

  println(zz)

  m = MatrixSpace(FlintZZ, r + 1, 1)(reshape(zz, r + 1, 1))

  h, u = hnf_with_transform(m)

  @assert h[1,1] == 1

  u = inv(u)

  m = submat(u, 1:r+1, 2:r+1)

  return transform(vcat(x, y), m)
end

function check_relation_mod_torsion(x::Array{FactoredElem{nf_elem}, 1}, y::FactoredElem{nf_elem}, z::Array{fmpz, 1})
# this should be improved
  (length(x) + 1 != length(z)) && error("Lengths of arrays does not fit")
  r = x[1]^z[1]

  for i in 2:length(x)
    r = r*x[i]^z[i]
  end 

  return is_torsion_unit(r*y^z[length(z)])
end

function _pow{T <: Union{nf_elem, FactoredElem{nf_elem}}}(x::Array{T, 1}, y::Array{fmpz, 1})
  if eltype(x) == nf_elem
    K = parent(x[1])::NfNumberField
  elseif eltype(x) == FactoredElem{nf_elem}
    K = base_ring(x[1])::NfNumberField
  end

  zz = deepcopy(y)

  z = Array(fmpz, length(x))

  for i in 1:length(x)
    z[i] = mod(zz[i], 2)
    zz[i] = zz[i] - z[i]
  end

  r = K(1)

  return zz
end

function approximate(x::arb, y::fmpz)
  println(x)
  found = true
  q = 1
  while(found)
    cf, re = cfrac(fmpq(fmpr(midpoint(x))), q)
    z = fmpq(cf)
    println(z)
    if den(z) <= y && contains(x, z)
      return z
    end
    q = q + 1
    if q > 30
      error("Something went wrong")
    end
  end
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

function _reg{T <: Union{nf_elem, FactoredElem{nf_elem}}}(x::Array{T, 1})
  if eltype(x) == nf_elem
    K = parent(x[1])::NfNumberField
  elseif eltype(x) == FactoredElem{nf_elem}
    K = base_ring(x[1])::NfNumberField
  end
  deg = degree(K)
  r1, r2 = signature(K)
  c = conjugate_data_arb(K)
  rr = r1 + r2
  r = rr - 1 # unit rank
  A = ArbMatSpace(r, r, c.prec)()
  for i in 1:r
    conlog = conjugates_log(x[i])
    for j in 1:r
      A[i, j] = conlog[j]
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

  A = u.units

  j = 0

  while(length(A) < r)
    j = j + 1

    if j > rows(ker)
      println("found only $(length(A)) many units but I need $r many")
      return length(A)
    end

    if is_zero_row(ker, j)
      continue
    end

    println("testing element $j")

    y = FactoredElem(x, ker, j)

    if is_torsion_unit(y)
      println("torsion unit: $y")
      continue
    end
    _add_unit(u, y)
  end

  u.tentative_regulator = _reg(A)
end

#  AA = ArbMatSpace(r, r, conjugate_data(O).prec)()
#
#  println(AA)
#
#  if r1 > 1
#      r1 = r1 - 1
#  else
#      r2 = r2 - 1
#  end
#
#
#  for k in 1:r
#    for i in 1:r1
#      AA[k, i] = log(abs(_evaluate(parent(K.pol)(u.units[k].elem_in_nf), conjugate_data(O).real_roots[i])))
#    end
#    for i in 1:r2
#      AA[k, r1 + i] = 2*log(abs(_evaluate(parent(K.pol)(u.units[k].elem_in_nf), conjugate_data(O).complex_roots[i])))
#    end
#  end
#
#  A_all = ArbMatSpace(rnk, r, conjugate_data(O).prec)()
#
#  for k in 1:rnk
#    a = K(1)
#    for i in 1:cols(ker)
#      if ker[k, i]  == 0
#        continue
#      end
#      a = a * (x.R[i])^(Int(ker[k, i]))
#    end
#    if is_torsion_unit(O(a, false))
#      continue
#    end
#    println("$k, $a")
#    for i in 1:r1
#      A_all[k, i] = log(abs(_evaluate(parent(K.pol)(a), conjugate_data(O).real_roots[i])))
#    end
#    for i in 1:r2
#      A_all[k, r1 + i] = 2*log(abs(_evaluate(parent(K.pol)(a), conjugate_data(O).complex_roots[i])))
#    end
#  end
#
#  X = A_all * inv(AA)
#
#  return X
#end

function _add_unit(u::UnitGrpCtx, x::FactoredElem{nf_elem})
  if is_independent( vcat(u.units, [ x ]))
    push!(u.units, x)
  end
  nothing
end

################################################################################
#
#  Factored elements over number fields/orders
#
################################################################################

# Get FactoredElem from ClassGrpCtx

function FactoredElem(x::ClassGrpCtx, y::fmpz_mat, j::Int)
  return FactoredElem(x.R, [ y[j, i] for i in 1:cols(y) ])
end

# Compute (log(abs(x_1)),...) where x_i is the ith conjugate

function conjugates_log(x::FactoredElem{nf_elem})
  M = parent(x)
  K = base_ring(x)  
  d = degree(K)
  r1, r2 = signature(K)
  res = Array(arb, r1 + r2)
  c = conjugate_data_arb(K)
  println("precision is $(c.prec)");

  for i in 1:r1+r2
    res[i] = ArbField(c.prec)(0)
  end

  println("Cached logarithms: $(M.basis_conjugates_log)")

  for a in base(x)
    # We should replace this using multipoint evaluation of libarb
    if haskey(M.basis_conjugates_log, a) && M.basis_conjugates_log[a][1] == c.prec
      z = M.basis_conjugates_log[a][2] 
      for i in 1:r1+r2
        res[i] = res[i] + x.fac[a]*z[i]
      end
    else
      z = Array(arb, r1 + r2)
      for i in 1:r1
        z[i] = log(abs(evaluate(parent(K.pol)(a),c.real_roots[i])))
      end
      for i in 1:r2
        z[r1 + i] = 2*log(abs(evaluate(parent(K.pol)(a), c.complex_roots[i])))
      end
      M.basis_conjugates_log[a] = (c.prec, z)
      for i in 1:r1+r2
        res[i] = res[i] + x.fac[a]*z[i]
        if !isfinite(res[i])
          refine(c)
          return conjugates_log(x)
        end
      end
    end
  end
  return res
end

function conjugates_arb(x::FactoredElem{nf_elem})
  K = base_ring(x)
  M = parent(x)
  d = degree(K)
  res = Array(arb, d)
  c = conjugate_data_arb(K)
  
  for i in 1:d
    res[i] = ArbField(c.prec)(1)
  end

  for a in base(x)
    if haskey(M.basis_conjugates, a) && M.basis_conjugates[a][1] == c.prec
      z = M.basis_conjugates[a][2] 
      for i in 1:d
        res[i] = res[i]*z[i]^x.fac[a]
      end
    else
      z = Array(arb, d)
      for i in 1:d
        z[i] = abs(evaluate(parent(K.pol)(a),c.roots[i]))
      end
      M.basis_conjugates[a] = (c.prec, z)
      for i in 1:d
        res[i] = res[i]*z[i]^x.fac[a]
        if !isfinite(res[i])
          refine(c)
          return conjugates_arb(x)
        end
      end
    end
  end
  return res
end

function ^{T <: Union{nf_elem, FactoredElem{nf_elem}}}(x::T, y::fmpz)
  if y == 0
    return parent(x)(1)
  elseif y == 1
    return deepcopy(x)
  elseif mod(y, 2) == 0
    z = x^(div(y, 2))
    return z*z
  elseif mod(y, 2) == 1
    return x^(y-1) * x
  end
end
