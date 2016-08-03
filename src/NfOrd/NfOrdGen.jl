################################################################################
#
#                   NfOrd.jl : Orders in Number fields
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

export deepcopy, basis, basis_nf, elem_in_basis, isequationorder, EquationOrder, Order

################################################################################
#
#  Copy of an order
#
################################################################################

function deepcopy(O::NfOrd)
  z = NfOrd()
  for x in fieldnames(O)
    # This is slow. Julia can't interfere the type of the right hand side.
    # (According to @code_warntype)
    if x != :nf && isdefined(O, x) 
      z.(x) = deepcopy(getfield(O, x))
    end
  end
  z.nf = O.nf
  return z
end

################################################################################
#
#  Field access
#
################################################################################

function basis_ord(O::NfOrd)
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

function basis(O::NfOrd)
  return basis_ord(O)
end

function basis(O::NfOrd, K::AnticNumberField)
  nf(O) != K && error()
  return basis_nf(O)
end

function basis_nf(O::NfOrd)
  return O.basis_nf
end

function basis_mat(O::NfOrd)
  if isdefined(O, :basis_mat)
    return O.basis_mat
  end
  A = basis_nf(O)
  O.basis_mat = FakeFmpqMat(basis_mat(O.nf, B))
  return O.basis_mat
end

function basis_mat_inv(O::NfOrd)
  if isdefined(O, :basis_mat_inv)
    return O.basis_mat_inv
  end
  O.basis_mat_inv = inv(basis_mat(O))
  return O.basis_mat_inv
end

function discriminant(O::NfOrd)
  if isdefined(O, :disc)
    return O.disc
  end

  if isequationorder(O)
    O.disc = num(discriminant(nf(O).pol))
    return O.disc
  end

  return _discriminant(O)
end

isequationorder(O::NfOrd) = O.isequationorder

nf(O::NfOrd) = O.nf

degree(O::NfOrd) = degree(O.nf)

parent(O::NfOrd) = O.parent

################################################################################
#
#  Binary operations
#
################################################################################

# This works only if something is coprime??
function +(a::NfOrd, b::NfOrd)
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

function show(io::IO, a::NfOrdSet)
  print(io, "Set of orders of the number field ")
  print(io, a.nf)
end  

function show(io::IO, a::NfOrd)
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

function Order(a::Array{nf_elem, 1}, check = true) 
  # We should check if it really is a basis and the elements are integral
  return NfOrd(a)
end

function Order(K::AnticNumberField, a::FakeFmpqMat, check = true)
  # We should check if a has full rank and the elements are integral?
  return NfOrd(K, a)
end

function EquationOrder(K::AnticNumberField)
  z = NfOrd(K)
  z.isequationorder = true
  return z
end

