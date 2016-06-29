################################################################################
#
#  NfMaxOrd/LinearAlgebra.jl : Linear algebra over maximal orders
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
# (C) 2016 Tommy Hofmann
#
################################################################################

using Hecke

function _det_bound(M::GenMat{NfOrdElem{NfMaxOrd}})
  n = rows(M)
  O = base_ring(M)
  d = degree(O)
  c1, c2 = Hecke.base_change_const(O)

  return fmpz(BigInt(ceil(sqrt(c2)*c1^(n/2)*BigInt(n)^n*BigInt(d)^n*BigInt(_max_max(M))^n)))
end

function _max_max(M::GenMat{NfOrdElem{NfMaxOrd}})
  d = FlintZZ(1)
  for i in 1:rows(M)
    for j in 1:cols(M)
      if !iszero(M[i, j])
        v = elem_in_basis(M[i, j])
        for k in degree(base_ring(M))
          d = max(d, abs(v[k]))
        end
      end
    end
  end
  return d
end
  
#function det(M::GenMat{NfOrdElem{NfMaxOrd}})
#  O = base_ring(M)::NfMaxOrd
#  B = _det_bound(M)
#  p = next_prime(2^60) # magic numbers
#  P = fmpz(1)
#  i = 1
#  res = zero(O)
#  t = 0.0
#  while P < 2*B
#    # reject some bad primes
#    if true  
#      #println("$p");
#      Omodp, pi_p = quo(O, ideal(O, p))
#      Mmodp = MatrixSpace(Omodp, rows(M), cols(M))(M)
#      t += @elapsed detmodp = pi_p\Hecke.det(Mmodp)
#      if i == 1
#        res = detmodp
#      elseif i >= 2
#        g, e, f = gcdx(P, fmpz(p))
#        @assert isone(g)
#        res = f*p*res + e*P*detmodp
#        res = mod_sym(res, P*p)
#        #@assert _basis_coord_nonneg(res)
#      end
#      P = P*p
#      p = next_prime(p)
#      i += 1
#    end
#  end
#  #println("Modular determinant time: $t");
#  return res
#end

function _get_coeff_raw(x::nmod_poly, i::Int)
  u = ccall((:nmod_poly_get_coeff_ui, :libflint), UInt, (Ptr{nmod_poly}, Int), &x, i)
  return u
end

function det(M::GenMat{NfOrdElem{NfMaxOrd}}, b = 62)
  O = base_ring(M)::NfMaxOrd
  B = _det_bound(M)
  p = next_prime(2^b) # magic numbers
  P = fmpz(1)
  i = 1
  res = O()
  t_det = 0.0
  t_reducing = 0.0
  t_splitting = 0.0
  used_primes = Array{UInt, 1}()
  tmp_polys = Array{nmod_poly, 1}()

  Zx = PolynomialRing(FlintIntegerRing(), "x")[1]
  tmp_fmpz_poly = Zx()

  while P < 2*B
    # reject some bad primes
    if is_index_divisor(O, p) 
      continue
    end

    ttt = @elapsed lp = prime_decomposition(O, p)

    ramified = false

    for j in 1:length(ttt)
      if lp[j][2] > 1 # || lp[j][1].splitting_type[2] > 3
        ramified = true
        break
      end
    end

    if ramified
      continue
    end

    push!(used_primes, UInt(p))

    t_splitting += ttt

    s = nmod_poly(UInt(p))
    t = nmod_poly(UInt(p))
    g = nmod_poly(UInt(p))
    z = nmod_poly(UInt(p))
    detmodp = nmod_poly(UInt(p))
    polyprod = nmod_poly(UInt(p))
    tmp_nmod_poly = nmod_poly(UInt(p))

    j = 1
    for (Q, e) in lp
      F, mF = ResidueField(O, Q)
      
      MmodQ = MatrixSpace(F, rows(M), cols(M))()
      t_reducing += @elapsed __helper!(MmodQ, mF, M.entries)
      t_det += @elapsed detmodQ = det(MmodQ)

      # now the CRT step

      if j == 1
        polyprod = mF.poly_of_the_field
        ccall((:nmod_poly_set, :libflint), Void, (Ptr{nmod_poly}, Ptr{fq_nmod}), &detmodp, &detmodQ)
      else
        crt!(tmp_nmod_poly, detmodp, detmodQ, polyprod, mF.poly_of_the_field, s, t)
        mul!(polyprod, polyprod, mF.poly_of_the_field)
        set!(detmodp, tmp_nmod_poly)
      end

      j += 1
    end

    push!(tmp_polys, detmodp)

    P = P*p
    p = next_prime(p)
    i += 1
  end

  # now the CRT on each coefficient

  fc = fmpz_comb(used_primes)
  fct = fmpz_comb_temp(fc)
  zz = fmpz()

  @assert length(used_primes) == length(tmp_polys)

  for i in 0:degree(O)
    fmpz_multi_crt_ui!(zz, [ _get_coeff_raw(tmp_polys[j], i) for j in 1:length(tmp_polys) ], fc, fct)
    setcoeff!(tmp_fmpz_poly, i, zz)
  end

  tut = fmpq_poly(tmp_fmpz_poly)
  tut.parent = parent(nf(O).pol)
  res = mod_sym(O(nf(O)(tut)), P)
  
  #println("Modular determinant time: $t_det");
  #println("Time for reducing: $t_reducing");
  #println("Time for splitting: $t_splitting");
  #println("Used $i primes")

  return res
end

# s, t are auxillary variables, r1, r2 are the residues, m1, m2 are the moduli
# aliasing is not allowed (?)
function crt!(z::nmod_poly, r1::nmod_poly, r2::Union{nmod_poly, fq_nmod}, m1::nmod_poly, m2::nmod_poly, s::nmod_poly, t::nmod_poly)
  ccall((:nmod_poly_xgcd, :libflint), Void, (Ptr{nmod_poly}, Ptr{nmod_poly}, Ptr{nmod_poly}, Ptr{nmod_poly}, Ptr{nmod_poly}), &z, &s, &t, &m1, &m2)
  @assert Bool(ccall((:nmod_poly_is_one, :libflint), Cint, (Ptr{nmod_poly}, ), &z))
  # z = s*m1*r2 + t*m2*r1
  mul!(z, s, m1)
  ccall((:nmod_poly_mul, :libflint), Void, (Ptr{nmod_poly}, Ptr{nmod_poly}, Ptr{fq_nmod}), &z, &z, &r2)
  mul!(t, t, m2)
  mul!(t, t, r1)
  add!(z, z, t)
  mul!(s, m1, m2)
  rem!(z, z, s)  
end

function set!(z::nmod_poly, x::nmod_poly)
  ccall((:nmod_poly_set, :libflint), Void, (Ptr{nmod_poly}, Ptr{nmod_poly}), &z, &x)
end

function __helper!(z, mF, entries)
  s = size(entries)
  for i in 1:s[2]
    for j in 1:s[1]
      z[j, i] = mF(entries[j, i])
    end
  end
  return z
end

function mod_sym(x, m)
  z = elem_in_basis(x)
  for i in 1:length(z)
    z[i] = mod(z[i], m)
    if 2*z[i] > m
      z[i] = z[i] - m
    end
  end
  return parent(x)(z)
end

function _basis_coord_nonneg(x)
  b = elem_in_basis(x)
  for i in 1:length(b)
    if b[i] < 0
      return false
    end
  end
  return true
end

function rand(M::GenMatSpace{NfOrdElem{NfMaxOrd}}, B::Union{Int, fmpz})
  z = M()
  for i in 1:rows(z)
    for j in 1:cols(z)
      z[i, j] = Hecke.rand(Hecke.base_ring(M), B)
    end
  end
  return z
end

