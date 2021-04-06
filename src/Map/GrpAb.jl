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
  parent(a) == domain(f) || error("not in the domain")
  if !isdefined(f, :map)
    return hasimage(f, a)[2]
  end
  return GrpAbFinGenElem(codomain(f), a.coeff * f.map)
end

function image(phi::GrpAbFinGenMap, U::GrpAbFinGen, add_to_lattice::Bool = !false)
  G = domain(phi)
  fl, inj = issubgroup(U, G)
  fl || error("subgroup is not in the domain")
  return sub(codomain(phi), [phi(inj(U[i])) for i=1:ngens(U)], add_to_lattice)
end

function preimage(f::Map(GrpAbFinGenMap), a::GrpAbFinGenElem)
  if !isdefined(f, :imap)
    fl, r = haspreimage(f, a)
    fl || error("element is not in the image")
    return r
  end
  return GrpAbFinGenElem(domain(f), a.coeff * f.imap)
end

################################################################################
#
#  Morphisms from finite abelian groups into finite fields
#
################################################################################

mutable struct FiniteFieldMultGrpMap{S, T} <: Map{GrpAbFinGen, S, HeckeMap, FiniteFieldMultGrpMap{S, T}}
  header::MapHeader{GrpAbFinGen, S}
  domain::GrpAbFinGen
  codomain::S
  generator::T
  @declare_other

  function FiniteFieldMultGrpMap{S, T}(G::GrpAbFinGen, F::S, generator::T, disc_log::Function) where {S, T}
    z = new{S, T}()
    z.header = MapHeader(G, F)
    z.domain = G
    z.codomain = F
    z.header.preimage = disc_log
    z.generator = generator
    return z
  end
end

function image(f::FiniteFieldMultGrpMap, x::GrpAbFinGenElem)
  return f.generator^x[1]
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
  @declare_other

  function AbToNfOrdMultGrp(O::NfOrd, order::Int, generator::NfOrdElem)
    G = abelian_group([order])
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

mutable struct AbToNfMultGrp <: Map{GrpAbFinGen, AnticNumberField, SetMap, AbToNfMultGrp}
  domain::GrpAbFinGen
  codomain::AnticNumberField
  generator::nf_elem
  @declare_other

  function AbToNfMultGrp(K::AnticNumberField, order::Int, generator::nf_elem)
    G = abelian_group(Int[order])
    z = new()
    z.domain = G
    z.codomain = K
    z.generator = generator
    return z
  end

end

function (f::AbToNfMultGrp)(a::GrpAbFinGenElem)
  return f.generator^a[1]
end



################################################################################
#
#  Morphisms from finite abelian groups to orders
#
################################################################################

# S is the type of the order (the codomain) and T is the elem_type of the order
mutable struct GrpAbFinGenToAbsOrdMap{S, T} <: Map{GrpAbFinGen, S, HeckeMap, GrpAbFinGenToAbsOrdMap}
  header::MapHeader{GrpAbFinGen, S}
  generators::Vector{T}
  discrete_logarithm::Function
  modulus # this can be anything, for which powermod(::T, ::fmpz, modulus) is defined
  
  disc_log::GrpAbFinGenElem #Needed in the conductor computation

  function GrpAbFinGenToAbsOrdMap{S, T}(G::GrpAbFinGen, O::S, generators::Vector{T}, disc_log::Function, modulus...) where {S, T}
    @assert ngens(G) == length(generators)

    z = new{S, T}()
    modulo = false
    if length(modulus) == 1
      modulo = true
      z.modulus = modulus[1]
    end

    function _image(a::GrpAbFinGenElem)
      @assert parent(a) === G
      y = one(O)
      for i in 1:length(generators)
        a[i] == 0 && continue
        if modulo
          y *= powermod(generators[i], a[i], z.modulus)
        else
          y *= generators[i]^a[i]
        end
      end
      return y
    end

    function _preimage(a::T)
      @assert parent(a) === O
      return G(disc_log(a))
    end

    z.header = MapHeader(G, O, _image, _preimage)
    z.generators = generators
    z.discrete_logarithm = disc_log
    return z
  end

  function GrpAbFinGenToAbsOrdMap{S, T}(O::S, generators::Vector{T}, snf_structure::Vector{fmpz}, disc_log::Function, modulus...) where {S, T}
    @assert length(generators) == length(snf_structure)

    G = abelian_group(snf_structure)

    return GrpAbFinGenToAbsOrdMap{S, T}(G, O, generators, disc_log, modulus...)
  end

  function GrpAbFinGenToAbsOrdMap{S, T}(O::S, generators::Vector{T}, relation_matrix::fmpz_mat, disc_log::Function, modulus...) where {S, T}
    @assert length(generators) == nrows(relation_matrix)

    G = GrpAbFinGen(relation_matrix)

    return GrpAbFinGenToAbsOrdMap{S, T}(G, O, generators, disc_log, modulus...)
  end
end

function GrpAbFinGenToAbsOrdMap(G::GrpAbFinGen, O::S, generators::Vector{T}, disc_log::Function, modulus...) where {S, T}
  return GrpAbFinGenToAbsOrdMap{S, T}(G, O, generators, disc_log, modulus...)
end

function GrpAbFinGenToAbsOrdMap(O::S, generators::Vector{T}, snf_structure::Vector{fmpz}, disc_log::Function, modulus...) where {S, T}
  return GrpAbFinGenToAbsOrdMap{S, T}(O, generators, snf_structure, disc_log, modulus...)
end

function GrpAbFinGenToAbsOrdMap(O::S, generators::Vector{T}, relation_matrix::fmpz_mat, disc_log::Function, modulus...) where {S, T}
  return GrpAbFinGenToAbsOrdMap{S, T}(O, generators, relation_matrix, disc_log, modulus...)
end

const GrpAbFinGenToNfAbsOrdMap = GrpAbFinGenToAbsOrdMap{NfOrd, NfOrdElem}

################################################################################
#
#  Isomorphisms from abelian groups onto multliplicative groups of residue
#  rings of orders
#
################################################################################

mutable struct GrpAbFinGenToAbsOrdQuoRingMultMap{S, T, U} <: Map{GrpAbFinGen, AbsOrdQuoRing{S, T}, HeckeMap, GrpAbFinGenToAbsOrdQuoRingMultMap}
  header::MapHeader{GrpAbFinGen, AbsOrdQuoRing{S, T}}
  generators::Vector{AbsOrdQuoRingElem{S, T, U}}
  discrete_logarithm::Function

  # Multiplicative group, tame part
  tame::Dict{T, GrpAbFinGenToAbsOrdMap{S, U}}

  # Multiplicative group, wild part
  wild::Dict{T, GrpAbFinGenToAbsOrdMap{S, U}}

  

  function GrpAbFinGenToAbsOrdQuoRingMultMap{S, T, U}(G::GrpAbFinGen, Q::AbsOrdQuoRing{S, T}, generators::Vector{AbsOrdQuoRingElem{S, T, U}}, disc_log::Function) where {S, T, U}
    @assert ngens(G) == length(generators)

    function _image(a::GrpAbFinGenElem)
      @assert parent(a) == G
      y = one(Q)
      for i in 1:length(generators)
        a[i] == 0 && continue
        mul!(y, y, generators[i]^a[i])
      end
      return y
    end

    function _preimage(a::AbsOrdQuoRingElem)
      @assert parent(a) === Q
      return G(disc_log(a))
    end

    z = new{S, T, U}()
    z.header = MapHeader(G, Q, _image, _preimage)
    z.generators = generators
    z.discrete_logarithm = disc_log
    return z
  end

  function GrpAbFinGenToAbsOrdQuoRingMultMap{S, T, U}(Q::AbsOrdQuoRing{S, T}, generators::Vector{AbsOrdQuoRingElem{S, T, U}}, snf_structure::Vector{fmpz}, disc_log::Function) where {S, T, U}
    @assert length(generators) == length(snf_structure)

    G = abelian_group(snf_structure)

    return GrpAbFinGenToAbsOrdQuoRingMultMap{S, T, U}(G, Q, generators, disc_log)
  end

  function GrpAbFinGenToAbsOrdQuoRingMultMap{S, T, U}(Q::AbsOrdQuoRing{S, T}, generators::Vector{AbsOrdQuoRingElem{S, T, U}}, relation_matrix::fmpz_mat, disc_log::Function) where {S, T, U}
    @assert length(generators) == nrows(relation_matrix)

    G = GrpAbFinGen(relation_matrix)

    return GrpAbFinGenToAbsOrdQuoRingMultMap{S, T, U}(G, Q, generators, disc_log)
  end

  function GrpAbFinGenToAbsOrdQuoRingMultMap{S, T, U}(G::GrpAbFinGen, Q::AbsOrdQuoRing{S, T}, exp::Function, disc_log::Function) where {S, T, U}
    z = new{S, T, U}()
    z.header = MapHeader(G, Q, exp, disc_log)
    return z
  end
end

const GrpAbFinGenToNfOrdQuoRingMultMap = GrpAbFinGenToAbsOrdQuoRingMultMap{NfOrd, NfOrdIdl, NfOrdElem}

function GrpAbFinGenToAbsOrdQuoRingMultMap(G::GrpAbFinGen, Q::AbsOrdQuoRing{S, T}, generators::Vector{AbsOrdQuoRingElem{S, T, U}}, disc_log::Function) where {S, T, U}
  return GrpAbFinGenToAbsOrdQuoRingMultMap{S, T, U}(G, Q, generators, disc_log)
end

function GrpAbFinGenToAbsOrdQuoRingMultMap(Q::AbsOrdQuoRing{S, T}, generators::Vector{AbsOrdQuoRingElem{S, T, U}}, snf_structure::Vector{fmpz}, disc_log::Function) where {S, T, U}
  return GrpAbFinGenToAbsOrdQuoRingMultMap{S, T, U}(Q, generators, snf_structure, disc_log)
end

function GrpAbFinGenToAbsOrdQuoRingMultMap(Q::AbsOrdQuoRing{S, T}, generators::Vector{AbsOrdQuoRingElem{S, T, U}}, relation_matrix::fmpz_mat, disc_log::Function) where {S, T, U}
  return GrpAbFinGenToAbsOrdQuoRingMultMap{S, T, U}(Q, generators, relation_matrix, disc_log)
end

function GrpAbFinGenToAbsOrdQuoRingMultMap(G::GrpAbFinGen, Q::AbsOrdQuoRing{S, T}, exp::Function, disc_log::Function) where {S, T}
  U = elem_type(base_ring(Q))
  return GrpAbFinGenToAbsOrdQuoRingMultMap{S, T, U}(G, Q, exp, disc_log)
end
