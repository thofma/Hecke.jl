################################################################################
#
#  Map/AbGrp.jl : Types for maps with domains of type AbGrp
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
#  Copyright (C) 2015, 2016 Tommy Hofmann
#
################################################################################

################################################################################
#
#  Maps for unit groups of number fields
#
################################################################################

type AbToNfOrdUnitGrp{T, S} <: Map{FinGenGrpAbSnf, FacElemMon{T}}
  header::MapHeader{FinGenGrpAbSnf, FacElemMon{nf_elem}}
  ind_unit::Array{FacElem{T}, 1}
  tor_unit::S

  # This only works if there exists at least one independent unit
  # That is, ind_unit should not have length 1
  function AbToNfOrdUnitGrp(O::NfMaxOrd, ind_unit::Array{FacElem{T}, 1}, tor_unit::NfOrdElem{NfMaxOrd}, tor_ord::Int)
    A = DiagonalGroup(vcat([tor_ord], [ 0 for i in 1:length(ind_unit) ]))
    z = new()
    z.ind_unit = ind_unit
    z.tor_unit = tor_unit

    function _image(a::FinGenGrpAbElem)
      y = Hecke.FacElem(tor_unit.elem_in_nf)^a[1]

      for i in 1:length(z.ind_unit)
        if a[i+1] == 0
          continue
        end
        y = y*z.ind_unit[i]^a[i+1]
      end

      return y
    end

    z.header = MapHeader(A, parent(z.ind_unit[1]), _image)

    return z
  end
end

function AbToNfOrdUnitGrp{T, S}(O::NfMaxOrd, ind_unit::Array{FacElem{T}, 1}, tor_unit::S, tor_ord::Int)
  length(ind_unit) == 0 && error("Not implemented yet")
  return AbToNfOrdUnitGrp{T, S}(O, ind_unit, tor_unit, tor_ord)
end

type AbToNfOrdFracIdlGrp <: Map{FinGenGrpAbSnf, NfMaxOrdIdl}
  header::MapHeader{FinGenGrpAbSnf, NfMaxOrdIdl}
end
