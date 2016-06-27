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
  
function det(M::GenMat{NfOrdElem{NfMaxOrd}})
  O = base_ring(M)::NfMaxOrd
  B = _det_bound(M)
  p = next_prime(2^60) # magic numbers
  P = fmpz(1)
  i = 1
  res = zero(O)
  t = 0.0
  while P < 2*B
    # reject some bad primes
    if true  
      println("$p");
      Omodp, pi_p = quo(O, ideal(O, p))
      Mmodp = MatrixSpace(Omodp, rows(M), cols(M))(M)
      t += @elapsed detmodp = pi_p\Hecke.det(Mmodp)
      if i == 1
        res = detmodp
      elseif i >= 2
        g, e, f = gcdx(P, fmpz(p))
        @assert isone(g)
        res = f*p*res + e*P*detmodp
        res = mod_sym(res, P*p)
        #@assert _basis_coord_nonneg(res)
      end
      P = P*p
      p = next_prime(p)
      i += 1
    end
  end
  println("Modular determinant time: $t");
  return res
end

function det2(M::GenMat{NfOrdElem{NfMaxOrd}}, b = 60)
  O = base_ring(M)::NfMaxOrd
  B = _det_bound(M)
  p = next_prime(2^b) # magic numbers
  P = fmpz(1)
  i = 1
  res = O()
  t = 0.0
  t_reducing = 0.0
  t_splitting = 0.0
  while P < 2*B
    # reject some bad primes
    if is_index_divisor(O, p) 
      continue
    end

    ttt = @elapsed lp = prime_decomposition(O, p)

    ramified = false

    for j in 1:length(ttt)
      if lp[j][2] > 1
        ramified = true
        break
      end
    end

    if ramified
      continue
    end

    println("Splitting time: $p $(length(lp)) $ttt ")
    t_splitting += ttt
    for (Q, e) in lp
      F, mF = ResidueField(O, Q)
      #t_reducing += @elapsed Mmodp = MatrixSpace(F, rows(M), cols(M))(map(mF, M.entries))
      Mmodp = MatrixSpace(F, rows(M), cols(M))()
      t_reducing += @elapsed __helper!(Mmodp, mF, M.entries)
      t += @elapsed detmodp = mF\det(Mmodp)
        #@assert _basis_coord_nonneg(res)
    end
    P = P*p
    p = next_prime(p)
    i += 1
  end
  println("Modular determinant time: $t");
  println("Time for reducing: $t_reducing");
  println("Time for splitting: $t_splitting");
  println("Used $i primes")
  return res
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

