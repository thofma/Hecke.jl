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
  p = next_prime(fmpz(2)^30) # magic numbers
  P = fmpz(1)
  i = 1
  res = O()
  t = 0.0
  while P < 2*B
    # reject some bad primes
    if true  
      Omodp, pi_p = quo(O, ideal(O, O(p)))
      Mmodp = MatrixSpace(Omodp, rows(M), cols(M))(M)
      t += @elapsed detmodp = pi_p\Hecke.det(Mmodp)
      if i == 1
        res = detmodp
      elseif i >= 2
        g, e, f = gcdx(P, p)
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

