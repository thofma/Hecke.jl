################################################################################
#
#                    Types.jl: Types for NfMaximalOrder
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
# (C) 2015 Claus Fieker
# (C) 2015 Tommy Hofmann
#
################################################################################

export GenNfOrd, NfOrderElem, UnitGrpCtx

abstract GenNfOrd <: Ring{Antic}

type NfOrderElem <: RingElem
  elem_in_nf::nf_elem
  elem_in_basis::Array{fmpz, 1}
  has_coord::Bool
  parent::GenNfOrd

  function NfOrderElem(O::GenNfOrd)
    z = new()
    z.parent = O
    z.elem_in_nf = nf(O)() 
    z.elem_in_basis = Array(fmpz, degree(O))
    z.has_coord = false
    return z
  end

  function NfOrderElem(O::GenNfOrd, a::nf_elem)
    z = new()
    z.elem_in_nf = a
    z.elem_in_basis = Array(fmpz, degree(O))
    z.parent = O
    z.has_coord = false
    return z
  end

  function NfOrderElem(O::GenNfOrd, a::nf_elem, arr::Array{fmpz, 1})
    z = new()
    z.parent = O
    z.elem_in_nf = a
    z.has_coord = true
    z.elem_in_basis = arr
    return z
  end

  function NfOrderElem(O::GenNfOrd, arr::Array{fmpz, 1})
    z = new()
    z.elem_in_nf = dot(basis_nf(O), arr)
    z.has_coord = true
    z.elem_in_basis = arr
    z.parent = O
    return z
  end

  function NfOrderElem{T <: Integer}(O::GenNfOrd, arr::Array{T, 1})
    return NfOrderElem(O, map(ZZ, arr))
  end
end

type UnitGrpCtx{T <: Union{nf_elem, FactoredElem{nf_elem}}}
  order::GenNfOrd
  rank::Int
  full_rank::Bool
  units::Array{T, 1}
  regulator::arb
  tentative_regulator::arb
  regulator_precision::Int
  torsion_units::Array{NfOrderElem, 1}
  torsion_units_order::Int

  function UnitGrpCtx(O::GenNfOrd)
    z = new()
    z.order = O
    z.rank = -1
    z.full_rank = false
    z.regulator_precision = -1
    z.torsion_units_order = -1
    z.units = Array{T, 1}()
    return z
  end
end

