################################################################################
#
#             NfOrd/NfOrdGen.jl : Generic orders in Number fields
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

export EquationOrder, Order

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::NfOrdGenSet)
  print(io, "Set of orders of the number field ")
  print(io, a.nf)
end  

function show(io::IO, a::NfOrdGen)
  print(io, "Order of ")
  println(io, a.nf)
  print(io, "with Z-basis ")
  print(io, basis(a))
end

################################################################################
#
#  Construction
#
################################################################################

doc"""
    Order(B::Array{nf_elem, 1}, check::Bool = true) -> NfOrd

> Returns the order with $\mathbf Z$-basis $B$. If `check` is set, it is checked
> whether $B$ defines an order.
"""
function Order(a::Array{nf_elem, 1}, check::Bool = true) 
  # We should check if it really is a basis and the elements are integral
  return NfOrdGen(nf_elem[ deepcopy(x) for x in a])
end

doc"""
    Order(K::AnticNumberField, A::FakeFmpqMat, check::Bool = true) -> NfOrd

> Returns the order which has basis matrix $A$ with respect to the power basis of $K$.
> If `check` is set, it is checked whether $A$ defines an order.
"""
function Order(K::AnticNumberField, a::FakeFmpqMat, check::Bool = true)
  # We should check if a has full rank and the elements are integral?
  return NfOrdGen(K, deepcopy(a))
end

doc"""
    EquationOrder(K::AnticNumberField) -> NfOrd

> Returns the equation of the number field $K$.
"""
function EquationOrder(K::AnticNumberField)
  z = NfOrdGen(K)
  z.isequationorder = true
  return z
end

################################################################################
#
#  Parent object call overloading
#
################################################################################

function Base.call(O::NfOrdGen, a::nf_elem, check::Bool = true)
  nf(O) != parent(a) &&
          error("Element is not an element of the number field of the order")
  if check
    (x,y) = _check_elem_in_order(a,O)
    !x && error("Number field element not in the order")
    return NfOrdElem{NfOrdGen}(O, deepcopy(a), fmpz[ deepcopy(x) for x in y])
  else
    return NfOrdElem{NfOrdGen}(O, deepcopy(a))
  end
end

function Base.call(O::NfOrdGen, a::Union{fmpz, Integer})
  return NfOrdElem{NfOrdGen}(O, nf(O)(deepcopy(a)))
end

function Base.call(O::NfOrdGen, arr::Array{fmpz, 1})
  return NfOrdElem{NfOrdGen}(O, fmpz[ deepcopy(x) for x in arr ])
end

function Base.call{S <: Integer}(O::NfOrdGen, arr::Array{S, 1})
  return NfOrdElem{NfOrdGen}(O, deepcopy(arr))
end

Base.call(O::NfOrdGen) = NfOrdElem{NfOrdGen}(O)

################################################################################
#
#  Creation from fractional ideals
#
################################################################################

function NfOrdGen(a::NfOrdGenFracIdl)
  z = NfOrdGen(nf(order(a)), a.basis_mat*order(a).basis_mat)
  return z
end

