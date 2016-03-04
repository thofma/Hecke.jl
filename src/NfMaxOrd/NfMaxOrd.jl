################################################################################
#
#       NfMaxOrd.jl : Maximal orders in absolute number fields
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

export NfMaxOrd

export MaximalOrder, conjugate_data, basis, nf, basis_mat, basis_mat_inv,
       degree, index, is_index_divisor, discriminant

elem_type(::NfMaxOrd) = NfOrdElem

################################################################################
#
#  Field access
#
################################################################################

function basis_ord(O::NfMaxOrd)
  if isdefined(O, :basis_ord)
    return O.basis_ord
  end
  b = O.basis_nf
  B = Array(NfOrdElem, length(b))
  for i in 1:length(b)
    v = fill(ZZ(0), length(b))
    v[i] = ZZ(1)
    B[i] = O(b[i], v; check = false)
  end
  O.basis_ord = B
  return B
end

function conjugate_data(O::NfMaxOrd)
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
    nf(O::NfMaxOrd) -> AnticNumberField

> Returns the ambient number field of $\mathcal O$.
"""
nf(O::NfMaxOrd) = O.nf

doc"""
***
    degree(O::NfMaxOrd) -> Int

> Returns the degree of $\mathcal O$, which is just the rank of $\mathcal O$
> as a $\mathbb{Z}$-module or equivalently the degree of the ambient number
> field.
"""
degree(O::NfMaxOrd) = degree(nf(O))

doc"""
***
    basis_mat(O::NfMaxOrd) -> FakeFmpqMat

> Returns the basis matrix of $\mathcal O$.
"""
function basis_mat(O::NfMaxOrd)
  return O.basis_mat
end

doc"""
    basis_mat_inv(O::NfMaxOrd) -> FakeFmpqMat

> Returns the inverse of the basis matrix of $\mathcal O$.
"""
function basis_mat_inv(O::NfMaxOrd)
  if isdefined(O, :basis_mat_inv)
    return O.basis_mat_inv
  else
    O.basis_mat_inv = inv(basis_mat(O))
    return O.basis_mat_inv
  end
end

doc"""
***
    basis(O::NfMaxOrd) -> Array{NfOrdElem, 1}

> Returns the basis of $\mathcal O$.
"""
function basis(O::NfMaxOrd)
  return basis_ord(O)
end

doc"""
***
    basis(O::NfMaxOrd, K::AnticNumberField -> Array{nf_elem, 1}

> Returns the basis of $\mathcal O$ as elements of $K$. The number field $K$
> must be the ambient number field of $\mathcal O$.
"""
function basis(O::NfMaxOrd, K::AnticNumberField)
  nf(O) != K && error()
  return basis_nf(O)
end

function basis_nf(O::NfMaxOrd)
  return O.basis_nf
end

doc"""
***
    index(O::NfMaxOrd) -> fmpz

> Returns the index $[ \mathcal{O} : \mathbf{Z}[\alpha]]$ of the equation order
> in the given maximal order $\mathcal O$. Here $\alpha$ is the primitive element
> of the ambient number field.
"""
function index(O::NfMaxOrd)
  if isdefined(O, :index)
    return O.index
  else
    O.index = divexact(basis_mat(O).den^degree(O), determinant(basis_mat(O).num))
    return O.index
  end
end

doc"""
***
    is_index_divisor(O::NfMaxOrd, d::Union{fmpz, Int})

> Returns whether $d$ is a divisor of $\operatorname{disc}(\mathcal O)$.
"""
function is_index_divisor(O::NfMaxOrd, d::Union{fmpz, Int})
  i = index(O)
  return i % d == 0
end

function base_change_const(O::NfMaxOrd)
  if O.base_change_const[1] > 0
    return O.base_change_const
  else
    d = degree(O)
    M = transpose(minkowski_mat(O, -64))
    # I need to swap rows (really?)
    r1, r2 = signature(O)
    for i in 2:2:r2
      swap_rows!(M, r1 + i, r1 + 2*r2 - i + 1)
    end

    M = [ Float64(M[i, j]) for i in 1:rows(M), j in 1:cols(M) ]
    N = transpose(M)*M
    r = sort(eigvals(N))
#    N = transpose(M)*M
#    N = MatrixSpace(AcbField(prec(base_ring(N))), rows(N), cols(N))(N)
#    chi = charpoly(PolynomialRing(base_ring(N), "x")[1], N)
#    return chi
#    r = roots(chi)
#    # I want upper bound for the largest and lower bound for the smallest root
#
#    tm = arf_struct(0, 0, 0, 0)
#    ccall((:arf_init, :libarb), Void, (Ptr{arf_struct}, ), &tm)
#    ccall((:arb_get_abs_ubound_arf, :libarb), Void, (Ptr{arf_struct}, Ptr{arb}), &tm, &real(r[end]))
#    # 3 is round to infinity
#    c1 = ccall((:arf_get_d, :libarb), Cdouble, (Ptr{arf_struct}, Cint), &tm, 3)
#
#    ccall((:arb_get_abs_ubound_arf, :libarb), Void, (Ptr{arf_struct}, Ptr{arb}), &tm, &(inv(real(r[1]))))
#    c2 = ccall((:arf_get_d, :libarb), Cdouble, (Ptr{arf_struct}, Cint), &tm, 3)
#
#    ccall((:arf_clear, :libarb), Void, (Ptr{arf_struct}, ), &tm)
#
#    z = (c1, c2)
    z = (r[end], inv(r[1]))
    O.base_change_const = z
    return z
  end
end
################################################################################
#
#  Constructors for users
#
################################################################################

doc"""
***
    MaximalOrder(K::AnticNumberField) -> NfMaxOrd

> Returns the maximal order of $K$.

**Example**

    julia> Qx, x = QQ["x"]
    julia> K, a = NumberField(x^3 + 2, "a")
    julia> O = MaximalOrder(K)
"""
function MaximalOrder(K::AnticNumberField)
  O = EquationOrder(K)
  @vprint :NfMaxOrd 1 "Computing the maximal order ...\n"
  O = _MaximalOrder(O)
  @vprint :NfMaxOrd 1 "... done\n"
  return NfMaxOrd(K, basis_mat(O))
end

doc"""
***
    MaximalOrder(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfMaxOrd

> Assuming that ``primes`` contains all the prime numbers at which the equation
> order $\mathbf{Z}[\alpha]$ of $K = \mathbf{Q}(\alpha)$ is not maximal,
> this function returns the maximal order of $K$.
"""
function MaximalOrder(K::AnticNumberField, primes::Array{fmpz, 1})
  O = EquationOrder(K)
  @vprint :NfMaxOrd 1 "Computing the maximal order ...\n"
  O = _MaximalOrder(O, primes)
  @vprint :NfMaxOrd 1 "... done\n"
  return NfMaxOrd(K, basis_mat(O))
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, O::NfMaxOrd)
  print(io, "Maximal order of $(nf(O)) \nwith basis $(basis_nf(O))")
end

