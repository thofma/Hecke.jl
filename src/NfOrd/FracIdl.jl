################################################################################
#
#          NfOrd/FracIdl.jl : Elements of orders of number fields
#
# This file is part of hecke.
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

export parent, order, basis_mat, basis_mat_inv, basis, norm,
       ring_of_multipliers, ==

################################################################################
#
#  Parent
#
################################################################################

parent(a::NfOrdFracIdl) = a.parent

################################################################################
#
#  Order
#
################################################################################

order(a::NfOrdFracIdlSet) = a.order

order(a::NfOrdFracIdl) = order(parent(a))

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(A::NfOrdFracIdl, dict::ObjectIdDict)
  B = typeof(A)(order(A))
  for i in fieldnames(A)
    if i == :parent
      continue
    end
    if isdefined(A, i)
      setfield!(B, i, deepcopy(getfield(A, i)))
    end
  end
  return B
end


################################################################################
#
#  (Inverse) basis matrix
#
################################################################################

doc"""
***
    basis_mat(I::NfOrdFracIdl) -> FakeFmpqMat

> Returns the basis matrix of $I$ with respect to the basis of the order.
"""
function basis_mat(a::NfOrdFracIdl)
  return deepcopy(a.basis_mat)
end

doc"""
***
    basis_mat_inv(I::NfOrdFracIdl) -> FakeFmpqMat

> Returns the inverse of the basis matrix of $I$.
"""
function basis_mat_inv(a::NfOrdFracIdl)
  if isdefined(a, :basis_mat_inv)
    return deepcopy(a.basis_mat_inv)
  else
    a.basis_mat_inv = inv(basis_mat(a))
    return deepcopy(a.basis_mat_inv)
  end
end

################################################################################
#
#  Basis
#
################################################################################

doc"""
***
    basis(I::NfOrdFracIdl) -> Array{nf_elem, 1}

> Returns the $\mathbf Z$-basis of $I$.
"""
function basis(a::NfOrdFracIdl)
  B = basis_mat(a)
  d = degree(order(a))
  O = order(a)
  K = nf(O)
  Oba = O.basis_nf
  res = Array(nf_elem, d)

  for i in 1:d
    z = K()
    for j in 1:d
      z = z + B.num[i, j]*Oba[j]
    end
    z = divexact(z, B.den)
    res[i] = z
  end

  return res
end

################################################################################
#
#  Norm
#
################################################################################

doc"""
***
    norm(I::NfOrdFracIdl) -> fmpq

> Returns the norm of $I$
"""
function norm(a::NfOrdFracIdl)
  if isdefined(a, :norm)
    return deepcopy(a.norm)
  else
    a.norm = det(basis_mat(a))
    return deepcopy(a.norm)
  end
end

################################################################################
#
#  Equality
#
################################################################################

doc"""
***
    ==(x::NfOrdFracIdl, y::NfOrdFracIdl) -> Bool

> Returns whether $x$ and $y$ are equal.
"""
==(x::NfOrdFracIdl, y::NfOrdFracIdl) = basis_mat(x) == basis_mat(y)

