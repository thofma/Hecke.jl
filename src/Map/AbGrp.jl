################################################################################
#
#  Map/AbGrp.jl : Types for maps with domains of type GrpAbFinGen
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
#  Copyright (C) 2015 - 2018 Tommy Hofmann, Carlo Sircana
#
################################################################################

export GrpAbFinGenMap

################################################################################
#
#  Morphisms between finitely generated abelian groups
#
################################################################################

mutable struct GrpAbFinGenMap <: Map{GrpAbFinGen, GrpAbFinGen,
                                     HeckeMap, GrpAbFinGenMap}
  header::MapHeader{GrpAbFinGen, GrpAbFinGen}

  map::fmpz_mat
  imap::fmpz_mat
  im::GrpAbFinGen  # if set
  ke::GrpAbFinGen  # if set

  function GrpAbFinGenMap(G::GrpAbFinGen)
    r = new()
    r.header = MapHeader(G, G)
    r.map = identity_matrix(FlintZZ, ngens(G))
    r.imap = identity_matrix(FlintZZ, ngens(G))
    return r
  end

  function GrpAbFinGenMap(From::GrpAbFinGen, To::GrpAbFinGen, M::fmpz_mat)
    r = new()
    r.header = MapHeader(From, To)
    r.map = M
    return r
  end

  function GrpAbFinGenMap(From::GrpAbFinGen, To::GrpAbFinGen, M::fmpz_mat, Mi::fmpz_mat)
    r = new()
    r.header = MapHeader(From, To)
    r.map = M
    r.imap = Mi
    return r
  end

  function GrpAbFinGenMap(M::T) where T <: Map{GrpAbFinGen, GrpAbFinGen}
    r = new()
    D = domain(M)
    r.header = MapHeader(D, codomain(M))
    if ngens(D) == 0
      r.map = matrix(FlintZZ, 0, ngens(codomain(M)), fmpz[])
    else
      r.map = vcat([M(D[i]).coeff for i=1:ngens(D)])
    end
    return r
  end
end

function image(f::Map(GrpAbFinGenMap), a::GrpAbFinGenElem)
  return GrpAbFinGenElem(codomain(f), a.coeff * f.map)
end

function image(phi::GrpAbFinGenMap, U::GrpAbFinGen, add_to_lattice::Bool = !false)
  G = domain(phi)
  fl, inj = issubgroup(U, G)
  return sub(codomain(phi), [phi(inj(U[i])) for i=1:ngens(U)], add_to_lattice)
end

function preimage(f::Map(GrpAbFinGenMap), a::GrpAbFinGenElem)
  return GrpAbFinGenElem(domain(f), a.coeff * f.imap)
end

################################################################################
#
#  Morphisms from finite abelian groups onto units of orders
#
################################################################################

mutable struct AbToNfOrdMultGrp <: Map{GrpAbFinGen, NfOrd, SetMap, AbToNfOrdMultGrp}
  domain::GrpAbFinGen
  codomain::NfOrd
  generator::NfOrdElem

  function AbToNfOrdMultGrp(O::NfOrd, order::Int, generator::NfOrdElem)
    G = DiagonalGroup([order])
    z = new()
    z.domain = G
    z.codomain = O
    z.generator = generator
    return z
  end
end

function (f::AbToNfOrdMultGrp)(a::GrpAbFinGenElem)
  return f.generator^a[1]
end

mutable struct GrpAbFinGenToNfAbsOrdMap <: Map{GrpAbFinGen, NfOrd, HeckeMap, GrpAbFinGenToNfAbsOrdMap}
  header::MapHeader
  generators::Vector{NfAbsOrdElem}
  discrete_logarithm::Function
  modulus::fmpz # if defined (and not zero), then the discrete exponentiation is done modulo this

  function GrpAbFinGenToNfAbsOrdMap(G::GrpAbFinGen, O::NfAbsOrd, generators::Vector{T}, disc_log::Function, modulus::fmpz = fmpz(0)) where T <: NfAbsOrdElem
    @assert ngens(G) == length(generators)

    function _image(a::GrpAbFinGenElem)
      @assert parent(a) == G
      y = one(O)
      for i in 1:length(generators)
        a[i] == 0 && continue
        if iszero(modulus)
          y *= generators[i]^a[i]
        else
          y *= powermod(generators[i], a[i], modulus)
        end
      end
      return y
    end

    function _preimage(a::NfAbsOrdElem)
      @assert parent(a) == O
      return G(disc_log(a))
    end

    z = new()
    z.header = MapHeader(G, O, _image, _preimage)
    z.generators = generators
    z.discrete_logarithm = disc_log
    if !iszero(modulus)
      z.modulus = modulus
    end
    return z
  end

  function GrpAbFinGenToNfAbsOrdMap(O::NfAbsOrd, generators::Vector{T}, snf_structure::Vector{fmpz}, disc_log::Function, modulus::fmpz = fmpz(0)) where T <: NfAbsOrdElem
    @assert length(generators) == length(snf_structure)

    G = DiagonalGroup(snf_structure)

    return GrpAbFinGenToNfAbsOrdMap(G, O, generators, disc_log, modulus)
  end

  function GrpAbFinGenToNfAbsOrdMap(O::NfAbsOrd, generators::Vector{T}, relation_matrix::fmpz_mat, disc_log::Function, modulus::fmpz = fmpz(0)) where T <: NfAbsOrdElem
    @assert length(generators) == rows(relation_matrix)

    G = GrpAbFinGen(relation_matrix)

    return GrpAbFinGenToNfAbsOrdMap(G, O, generators, disc_log, modulus)
  end
end

################################################################################
#
#  Isomorphisms from abelian groups onto multliplicative groups of residue
#  rings of orders
#
################################################################################

mutable struct GrpAbFinGenToNfOrdQuoRingMultMap <: Map{GrpAbFinGen, NfOrdQuoRing, HeckeMap, GrpAbFinGenToNfOrdQuoRingMultMap}
  header::MapHeader{GrpAbFinGen, NfOrdQuoRing}
  generators::Vector{NfOrdQuoRingElem}
  discrete_logarithm::Function

  # Multiplicative group, tame part
  tame::Dict{NfOrdIdl, GrpAbFinGenToNfAbsOrdMap}

  # Multiplicative group, wild part
  wild::Dict{NfOrdIdl, GrpAbFinGenToNfAbsOrdMap}

  function GrpAbFinGenToNfOrdQuoRingMultMap(G::GrpAbFinGen, Q::NfOrdQuoRing, generators::Vector{NfOrdQuoRingElem}, disc_log::Function)
    @assert ngens(G) == length(generators)

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
    z.header = MapHeader(G, Q, _image, _preimage)
    z.generators = generators
    z.discrete_logarithm = disc_log
    return z
  end

  function GrpAbFinGenToNfOrdQuoRingMultMap(Q::NfOrdQuoRing, generators::Vector{NfOrdQuoRingElem}, snf_structure::Vector{fmpz}, disc_log::Function)
    @assert length(generators) == length(snf_structure)

    G = DiagonalGroup(snf_structure)

    return GrpAbFinGenToNfOrdQuoRingMultMap(G, Q, generators, disc_log)
  end

  function GrpAbFinGenToNfOrdQuoRingMultMap(Q::NfOrdQuoRing, generators::Vector{NfOrdQuoRingElem}, relation_matrix::fmpz_mat, disc_log::Function)
    @assert length(generators) == rows(relation_matrix)

    G = GrpAbFinGen(relation_matrix)

    return GrpAbFinGenToNfOrdQuoRingMultMap(G, Q, generators, disc_log)
  end

  function GrpAbFinGenToNfOrdQuoRingMultMap(G::GrpAbFinGen, Q::NfOrdQuoRing, exp::Function, disc_log::Function)
    z = new()
    z.header = MapHeader(G, Q, exp, disc_log)
    return z
  end
end
