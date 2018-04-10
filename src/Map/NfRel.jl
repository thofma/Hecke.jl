################################################################################
#
#  Map/NfRel.jl : Types for maps with domains of type NfRel
#
# This file is part of Hecke.
#
# Copyright (c) 2015, 2016, 2017: Claus Fieker, Tommy Hofmann
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
#  Copyright (C) 2017 Tommy Hofmann, Claus Fieker
#
################################################################################

#why only simple relative?

mutable struct NfRelToNf <: Map{NfRel{nf_elem}, AnticNumberField}
  header::MapHeader{NfRel{nf_elem}, AnticNumberField}

  function NfRelToNf(K::NfRel{nf_elem}, L::AnticNumberField, a::nf_elem, b::nf_elem, c::NfRelElem{nf_elem})
    # let K/k, k absolute number field
    # k -> L, gen(k) -> a
    # K -> L, gen(K) -> b
    # L -> K, gen(L) -> c

    k = K.base_ring
    Ly, y = PolynomialRing(L, cached = false)
    R = parent(k.pol)
    S = parent(L.pol)

    function image(x::NfRelElem{nf_elem})
      # x is an element of K
      f = data(x)
      # First evaluate the coefficients of f at a to get a polynomial over L
      # Then evaluate at b
      r = [ evaluate(R(coeff(f, i)), a) for i in 0:degree(f)]
      return evaluate(Ly(r), b)
    end

    function preimage(x::nf_elem)
      # x is an element of L
      f = S(x)
      return evaluate(f, c)
    end

    z = new()
    z.header = MapHeader(K, L, image, preimage)
    return z
  end
end

function show(io::IO, h::NfRelToNf)
  println(io, "Isomorphism between ", domain(h), "\nand ", codomain(h))
end

mutable struct NfRelRelToNfRel{T} <: Map{NfRel{NfRelElem{T}}, NfRel{T}} 
  header::MapHeader{NfRel{NfRelElem{T}}, NfRel{T}}

  function NfRelRelToNfRel(K::NfRel{NfRelElem{T}}, L::NfRel{T}, a::NfRelElem{T}, b::NfRelElem{T}, c::NfRelElem{NfRelElem{T}}) where T
    # let K/k, k absolute number field
    # k -> L, gen(k) -> a
    # K -> L, gen(K) -> b
    # L -> K, gen(L) -> c

    k = K.base_ring
    Ly, y = PolynomialRing(L, cached = false)
    R = parent(k.pol)
    S = parent(L.pol)

    function image(x::NfRelElem{NfRelElem{T}}) where T
      # x is an element of K
      f = data(x)
      # First evaluate the coefficients of f at a to get a polynomial over L
      # Then evaluate at b
      r = [ R(coeff(f, i))( a) for i in 0:degree(f)]
      return Ly(r)(b)
    end

    function preimage(x::NfRelElem{T}) where T
      # x is an element of L
      f = S(x)
      return f(c)
    end

    z = new{T}()
    z.header = MapHeader(K, L, image, preimage)
    return z
  end
end

function show(io::IO, h::NfRelRelToNfRel)
  println(io, "Isomorphism between ", domain(h), "\nand ", codomain(h))
end


mutable struct NfRelToNfRelMor{T, S} <: Map{NfRel{T}, NfRel{S}}
  header::MapHeader{NfRel{T}, NfRel{S}}
  prim_img ::NfRelElem{S}
  coeff_aut::NfToNfMor

  function NfRelToNfRelMor{T, S}() where {T, S}
    z = new{T, S}()
    return z
  end

  function NfRelToNfRelMor{T, S}(K::NfRel{T}, L::NfRel{S}, a::NfRelElem{S}) where {T, S}
    function image(x::NfRelElem{S})
      # x is an element of K
      f = data(x)
      # First evaluate the coefficients of f at a to get a polynomial over L
      # Then evaluate at b
      return f(a)
    end

    z = new{T, S}()
    z.prim_img = a
    z.header = MapHeader(K, L, image)
    return z
  end  
end

  #so far, only for single relative.
function NfRelToNfRelMor(K::NfRel{nf_elem}, L::NfRel{nf_elem}, A::NfToNfMor, a::NfRelElem{nf_elem})
  function image(x::NfRelElem{nf_elem})
    # x is an element of K
    f = data(x)
    g = zero(f)
    for i=0:degree(f)
      setcoeff!(g, i, A(coeff(f, i)))
    end
    # First evaluate the coefficients of f at a to get a polynomial over L
    # Then evaluate at b
    return g(a)
  end

  z = NfRelToNfRelMor{nf_elem, nf_elem}()
  z.prim_img = a
  z.coeff_aut = A
  z.header = MapHeader(K, L, image)
  return z
end

function NfRelToNfRelMor(K::NfRel{nf_elem}, L::NfRel{nf_elem}, a::NfRelElem{nf_elem})
  function image(x::NfRelElem{nf_elem})
    # x is an element of K
    f = data(x)
    g = zero(f)
    for i=0:degree(f)
      setcoeff!(g, i, coeff(f, i))
    end
    return g(a)
  end

  z = NfRelToNfRelMor{nf_elem, nf_elem}()
  z.prim_img = a
  z.header = MapHeader(K, L, image)
  return z
end


function show(io::IO, h::NfRelToNfRelMor)
  if domain(h) == codomain(h)
    println(io, "Automorphism of ", domain(h))
  else
    println(io, "Injection of ", domain(h), " into ", codomain(h))
  end
  println(io, "defined by ", gen(domain(h)), " -> ", h.prim_img)
  if isdefined(h, :coeff_aut)
    println(io, "using coefficient map: ", h.coeff_aut)
  end
end

mutable struct NfRelToFqMor{T} <: Map{NfRel{T}, FqFiniteField}
  header::MapHeader{NfRel{T}, FqFiniteField}

  function NfRelToFqMor{T}() where {T}
    z = new{T}()
    z.header = MapHeader{NfRel{T}, FqFiniteField}()
    return z
  end
end
