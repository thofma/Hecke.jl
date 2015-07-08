################################################################################
#
#                   NfOrder.jl : Orders in Number fields
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

import Base: powermod

export NfOrder, NfOrderSet

export powermod, elem_in_basis, EquationOrder, deepcopy, Order

################################################################################
#
#  Types
#
################################################################################

const NfOrderSetID = ObjectIdDict()

type NfOrderSet
  nf::NfNumberField

  function NfOrderSet(a::NfNumberField)
  try
    return NfOrderSetID[a]
  end
    NfOrderSetID[a] = new(a)
    return NfOrderSetID[a]
  end
end

#const NfOrderID = Dict{Tuple{NfNumberField, FakeFmpqMat}, GenNfOrd}()
const NfOrderID = ObjectIdDict()

type NfOrder <: GenNfOrd
  nf::NfNumberField
  basis_nf::Array{nf_elem, 1} # Basis as number field elements
  basis_ord                   # Array{NfOrderElt, 1}
  basis_mat::FakeFmpqMat      # Basis matrix with respect to number field basis
  basis_mat_inv::FakeFmpqMat  # Inverse of basis matrix
  index::fmpz                 # ??
  disc::fmpz                  # Discriminant
  disc_fac                    # ??
  isequationorder::Bool       # Flag for being equation order
  parent::NfOrderSet          # Parent object
  signature::Tuple{Int, Int}  # Signature of the associated number field
                              # (-1, 0) means 'not set'

  function NfOrder()
    z = new()
    # Populate with 'default' values
    z.signature = (-1,0)      
    z.isequationorder = false
    return z
  end
end

# We use outer constructors or else NfOrderElem is not known at this point

# The following constructs the order with basis matrix the identity matrix
function NfOrder(K::NfNumberField)
  A = FakeFmpqMat(one(MatrixSpace(FlintZZ, degree(K), degree(K))))
  if haskey(NfOrderID, (K,A))
    return NfOrderID[(K,A)]::NfOrder
  else
    z = NfOrder()
    z.parent = NfOrderSet(K)
    z.nf = K
    z.basis_mat = A
    z.basis_nf = basis(K)
    z.basis_ord = Array(NfOrderElem, degree(K))
    z.basis_ord[1] = z(K(1), false)
    for i in 2:degree(K)
      z.basis_ord[i] = z(gen(K)^(i-1), false)
    end
    NfOrderID[(K, A)] = z
    return z::NfOrder
  end
end

# Construct the order with basis matrix x
function NfOrder(K::NfNumberField, x::FakeFmpqMat)
  if haskey(NfOrderID, (K,x))
    return NfOrderID[(K,x)]::NfOrder
  else
    z = NfOrder()
    z.parent = NfOrderSet(K)
    z.nf = K
    z.basis_mat = x
    B = Array(NfOrderElem, degree(K))
    BB = Array(nf_elem, degree(K))
    for i in 1:degree(K)
      t = element_from_mat_row(K, x.num, i)//K(x.den)
      BB[i] = t
      B[i] = z(t, false) 
    end
    z.basis_ord = B
    z.basis_nf = BB
    z.parent = NfOrderSet(z.nf)
    NfOrderID[(K,x)] = z
    return z::NfOrder
  end
end

# Construct the order with basis a
function NfOrder(a::Array{nf_elem, 1})
  K = parent(a[1])
  A = FakeFmpqMat(basis_mat(K,a))
  if haskey(NfOrderID, (K,A))
    return NfOrderID[(K,A)]::NfOrder
  else
    z = NfOrder()
    z.parent = NfOrderSet(K)
    z.nf = K
    z.basis_nf = a
    z.basis_mat = A
    z.basis_ord = Array(NfOrderElem, degree(K))
    for i in 1:degree(K)
      z.basis_ord[i] = z(a[i], false)
    end
    NfOrderID[(K,A)] = z
    return z::NfOrder
  end
end

################################################################################
#
#  Copy of an order
#
################################################################################

function deepcopy(O::NfOrder)
  z = NfOrder()
  for x in fieldnames(O)
    # This is slow. Julia can't interfere the type of the right hand side.
    # (According to @code_warntype)
    if isdefined(O, x)
      z.(x) = O.(x)
    end
  end
  return z
end

################################################################################
#
#  Field access
#
################################################################################

function basis_ord(O::NfOrder)
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

function basis(O::NfOrder)
  return basis_ord(O)
end

function basis(O::NfOrder, K::NfNumberField)
  nf(O) != K && error()
  return basis_nf(O)
end

function basis_nf(O::NfOrder)
  return O.basis_nf
end

function basis_mat(O::NfOrder)
  if isdefined(O, :basis_mat)
    return O.basis_mat
  end
  A = basis_nf(O)
  O.basis_mat = FakeFmpqMat(basis_mat(O.nf, B))
  return O.basis_mat
end

function basis_mat_inv(O::NfOrder)
  if isdefined(O, :basis_mat_inv)
    return O.basis_mat_inv
  end
  O.basis_mat_inv = inv(basis_mat(O))
  return O.basis_mat_inv
end

isequationorder(O::NfOrder) = O.isequationorder

nf(O::NfOrder) = O.nf

degree(O::NfOrder) = degree(O.nf)

parent(O::NfOrder) = O.parent

################################################################################
#
#  Binary operations
#
################################################################################

# This works only if something is coprime??
function +(a::NfOrder, b::NfOrder)
  c = sub(_hnf(vcat(den(basis_mat(b))*num(basis_mat(a)),
                    den(basis_mat(a))*num(basis_mat(b))),
               :lowerleft),
          degree(a)+1:2*degree(a),1:degree(a))
  O = Order(nf(a),FakeFmpqMat(c,den(basis_mat(a))*den(basis_mat(b))))
  return O
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::NfOrderSet)
  print(io, "Set of orders of the number field ")
  print(io, a.nf)
end  

function show(io::IO, a::NfOrder)
  print(io, "Order of ")
  println(io, a.nf)
  print(io, "with Z-basis ")
  print(io, basis(a))
end

################################################################################
#
#  Parent object overloading
#
################################################################################

function call(a::NfOrderSet)
  z = NfOrder()
  z.parent = a
  z.nf = a.nf
  return z
end

function Order(a::Array{nf_elem, 1}, check = true) 
  # We should check if it really is a basis and the elements are integral
  return NfOrder(a)
end

function Order(K::NfNumberField, a::FakeFmpqMat, check = true)
  # We should check if a has full rank and the elements are integral?
  return NfOrder(K,a)
end

function EquationOrder(K::NfNumberField)
  z = NfOrder(K)
  z.isequationorder = true
  return z
end

################################################################################
#
#  Discriminant
#
################################################################################

function discriminant(O::NfOrder)
  if isdefined(O, :disc)
    return O.disc
  end
  A = MatrixSpace(ZZ, degree(O), degree(O))()
  B = basis(O)
  for i in 1:degree(O)
    for j in 1:degree(O)
      A[i,j] = ZZ(trace(B[i]*B[j]))
    end
  end
  O.disc = determinant(A)
  return O.disc
end
