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
#  Maps for multliplicative groups of residue rings of maximal orders
#
################################################################################

mutable struct AbToResRingMultGrp <: Map{GrpAbFinGen, NfOrdQuoRing, HeckeMap, AbToResRingMultGrp}
  header::MapHeader{GrpAbFinGen, NfOrdQuoRing}
  generators::Vector{NfOrdQuoRingElem}
  discrete_logarithm::Function
  
  tame::Dict{NfOrdIdl,Tuple{NfOrdElem,fmpz,Function}} #The multiplicative group, tame part
  wild::Dict{NfOrdIdl,Tuple{Array{NfOrdElem,1},Array{fmpz,1},Function}} #Multiplicative group, wild part
  
  function AbToResRingMultGrp(Q::NfOrdQuoRing, 
                              generators::Vector{NfOrdQuoRingElem},
                              snf_structure::Vector{fmpz},
                              disc_log::Function)
    @assert length(generators) == length(snf_structure)
    @hassert :NfOrdQuoRing 1 all(g->parent(g)==Q,generators)

    G = DiagonalGroup(snf_structure)
    @assert isa(G,GrpAbFinGen)
    @assert issnf(G)

    function _image(a::GrpAbFinGenElem)
      @assert parent(a) == G
      y = one(Q)
      for i in 1:length(generators)
        a[i] == 0 && continue
        y *= generators[i]^a[i]
      end
      return y
    end

    function _preimage(a::NfOrdQuoRingElem)
      @assert parent(a) == Q
      return G(disc_log(a))
    end

    z = new()
    z.header = MapHeader(G,Q,_image,_preimage)
    z.generators = generators
    z.discrete_logarithm = disc_log
    return z
  end
  
  function AbToResRingMultGrp(G::GrpAbFinGen, Q::NfOrdQuoRing, exp::Function, disc_log::Function)
    z = new()
    z.header = MapHeader(G,Q,exp,disc_log)
    
    return z
  end
  
end

mutable struct AbToNfOrdMultGrp <: Map{GrpAbFinGen, NfOrd, HeckeMap, AbToNfOrdMultGrp}
  header::MapHeader{GrpAbFinGen, NfOrd}
  
  function AbToNfOrdMultGrp(O::NfOrd, order::Int, generator::NfOrdElem)
    G = DiagonalGroup([order])

    function _image(a::GrpAbFinGenElem)
      @assert parent(a) == G
      return generator^a[1]
    end

    z = new()
    z.header = MapHeader(G, O, _image)
    return z
  end
end
