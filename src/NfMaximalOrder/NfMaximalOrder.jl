################################################################################
#
#       NfMaximalOrder.jl : Maximal orders in absolute number fields
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
# (C) 2015 Tommy Hofmann
#
################################################################################

export NfMaximalOrder

export MaximalOrder, conjugate_data, basis, nf, basis_mat, basis_mat_inv,
       degree, index, is_index_divisor, discriminant

elem_type(::NfMaximalOrder) = NfOrderElem

################################################################################
#
#  Field access
#
################################################################################

function basis_ord(O::NfMaximalOrder)
  if isdefined(O, :basis_ord)
    return O.basis_ord
  end
  b = O.basis_nf
  B = Array(NfOrderElem, length(b))
  for i in 1:length(b)
    v = fill(ZZ(0), length(b))
    v[i] = ZZ(1)
    B[i] = O(b[i], v; check = false)
  end
  O.basis_ord = B
  return B
end

function conjugate_data(O::NfMaximalOrder)
  if isdefined(O, :conjugate_data)
    return O.conjugate_data
  else
    # acb_root_ctx will find the roots of the polynomial
    # precision will be chosen so that roots can be separated
    # starting precision is 64
    O.conjugate_data = acb_root_ctx(nf(O).pol)
    return O.conjugate_data
  end
end

doc"""
***
    nf(O::NfMaximalOrder) -> AnticNumberField

> Returns the ambient number field of $\mathcal O$.
"""
nf(O::NfMaximalOrder) = O.nf

doc"""
***
    degree(O::NfMaximalOrder) -> Int

> Returns the degree of $\mathcal O$, which is just the rank of $\mathcal O$
> as a $\mathbb{Z}$-module or equivalently the degree of the ambient number
> field.
"""
degree(O::NfMaximalOrder) = degree(nf(O))

doc"""
***
    basis_mat(O::NfMaximalOrder) -> FakeFmpqMat

> Returns the basis matrix of $\mathcal O$.
"""
function basis_mat(O::NfMaximalOrder)
  return O.basis_mat
end

doc"""
    basis_mat_inv(O::NfMaximalOrder) -> FakeFmpqMat

> Returns the inverse of the basis matrix of $\mathcal O$.
"""
function basis_mat_inv(O::NfMaximalOrder)
  if isdefined(O, :basis_mat_inv)
    return O.basis_mat_inv
  else
    O.basis_mat_inv = inv(basis_mat(O))
    return O.basis_mat_inv
  end
end

doc"""
***
    basis(O::NfMaximalOrder) -> Array{NfOrderElem, 1}

> Returns the basis of $\mathcal O$.
"""
function basis(O::NfMaximalOrder)
  return basis_ord(O)
end

doc"""
***
    basis(O::NfMaximalOrder, K::AnticNumberField -> Array{nf_elem, 1}

> Returns the basis of $\mathcal O$ as elements of $K$. The number field $K$
> must be the ambient number field of $\mathcal O$.
"""
function basis(O::NfMaximalOrder, K::AnticNumberField)
  nf(O) != K && error()
  return basis_nf(O)
end

function basis_nf(O::NfMaximalOrder)
  return O.basis_nf
end

doc"""
***
    index(O::NfMaximalOrder) -> fmpz

> Returns the index $[ \mathcal{O} : \mathbf{Z}[\alpha]]$ of the equation order
> in the given maximal order $\mathcal O$. Here $\alpha$ is the primitive element
> of the ambient number field.
"""
function index(O::NfMaximalOrder)
  if isdefined(O, :index)
    return O.index
  else
    O.index = divexact(basis_mat(O).den^degree(O), determinant(basis_mat(O).num))
    return O.index
  end
end

doc"""
***
    is_index_divisor(O::NfMaximalOrder, d::Union{fmpz, Int})

> Returns whether $d$ is a divisor of $\operatorname{disc}(\mathcal O)$.
"""
function is_index_divisor(O::NfMaximalOrder, d::Union{fmpz, Int})
  i = index(O)
  return i % d == 0
end

################################################################################
#
#  Constructors for users
#
################################################################################

doc"""
***
    MaximalOrder(K::AnticNumberField) -> NfMaximalOrder

> Returns the maximal order of $K$.

**Example**

    julia> Qx, x = QQ["x"]
    julia> K, a = NumberField(x^3 + 2, "a")
    julia> O = MaximalOrder(K)
"""
function MaximalOrder(K::AnticNumberField)
  O = EquationOrder(K)
  @vprint :NfMaximalOrder 1 "Computing the maximal order ...\n"
  O = _MaximalOrder(O)
  @vprint :NfMaximalOrder 1 "... done\n"
  return NfMaximalOrder(K, basis_mat(O))
end

doc"""
***
    MaximalOrder(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfMaximalOrder

> Assuming that ``primes`` contains all the prime numbers at which the equation
> order $\mathbf{Z}[\alpha]$ of $K = \mathbf{Q}(\alpha)$ is not maximal,
> this function returns the maximal order of $K$.
"""
function MaximalOrder(K::AnticNumberField, primes::Array{fmpz, 1})
  O = EquationOrder(K)
  @vprint :NfMaximalOrder 1 "Computing the maximal order ...\n"
  O = _MaximalOrder(O, primes)
  @vprint :NfMaximalOrder 1 "... done\n"
  return NfMaximalOrder(K, basis_mat(O))
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, O::NfMaximalOrder)
  print(io, "Maximal order of $(nf(O)) \nwith basis $(basis_nf(O))")
end

