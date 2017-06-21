################################################################################
#
#    NfOrd/NfOrdFracIdl.jl : Fractional ideals of generic
#                               orders in number fields
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

export frac_ideal

################################################################################
#
#  Construction
#
################################################################################

doc"""
***
    frac_ideal(O::NfOrd, A::FakeFmpqMat) -> NfOrdFracIdl

> Creates the fractional ideal of $\mathcal O$ with basis matrix $A$.
"""
function frac_ideal(O::NfOrd, x::FakeFmpqMat)
  y = hnf(x)
  z = NfOrdFracIdl(O, y)
  return z
end

doc"""
***
    frac_ideal(O::NfOrd, A::fmpz_mat, b::fmpz) -> NfOrdFracIdl

> Creates the fractional ideal of $\mathcal O$ with basis matrix $A/b$.
"""
function frac_ideal(O::NfOrd, x::fmpz_mat, y::fmpz)
  y = FakeFmpqMat(x, y)
  z = NfOrdFracIdl(O, y)
  return z
end

frac_ideal(O::NfOrd, x::fmpz_mat, y::Integer) = frac_ideal(O, x, fmpz(y))

doc"""
***
    frac_ideal(O::NfOrd, I::NfOrdIdl) -> NfOrdFracIdl

> Turns the ideal $I$ into a fractional ideal of $\mathcal O$.
"""
function frac_ideal(O::NfOrd, x::NfOrdIdl)
  z = NfOrdFracIdl(O, x, fmpz(1))
  return z
end

doc"""
***
    frac_ideal(O::NfOrd, I::NfOrdIdl, b::fmpz) -> NfOrdFracIdl

> Creates the fractional ideal $I/b$ of $\mathcal O$.
"""
function frac_ideal(O::NfOrd, x::NfOrdIdl, y::fmpz)
  z = NfOrdFracIdl(O, x, deepcopy(y)) # deepcopy x?
  return z
end

frac_ideal(O::NfOrd, x::NfOrdIdl, y::Integer) = frac_ideal(O, x, fmpz(y))

doc"""
***
    frac_ideal(O::NfOrd, a::nf_elem) -> NfOrdFracIdl

> Creates the principal fractional ideal $(a)$ of $\mathcal O$.
"""
function frac_ideal(O::NfOrd, x::nf_elem)
  z = NfOrdFracIdl(O, deepcopy(x))
  return z
end

doc"""
***
    frac_ideal(O::NfOrd, a::NfOrdElem) -> NfOrdFracIdl

> Creates the principal fractional ideal $(a)$ of $\mathcal O$.
"""
function frac_ideal(O::NfOrd, x::NfOrdElem)
  z = NfOrdFracIdl(O, elem_in_nf(x))
  return z
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, x::NfOrdFracIdl)
  print(io, "Fractional ideal of $(order(x)) with basis matrix\n")
  print(io, "$(basis_mat(x))\n")
end
