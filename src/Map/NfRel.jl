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

type NfRelToNf <: Map{NfRel{nf_elem}, AnticNumberField}
  header::MapHeader{NfRel{nf_elem}, AnticNumberField}

  function NfRelToNf(K::NfRel{nf_elem}, L::AnticNumberField, a::nf_elem, b::nf_elem, c::NfRelElem{nf_elem})
    # let K/k, k absolute number field
    # k -> L, gen(k) -> a
    # K -> L, gen(K) -> b
    # L -> K, gen(L) -> c

    k = K.base_ring
    Ly, y = PolynomialRing(L)
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

type NfRelToNfRel <: Map{NfRel{nf_elem}, NfRel{nf_elem}}
  header::MapHeader{NfRel{nf_elem}, NfRel{nf_elem}}

  function NfRelToNfRel(K::NfRel{nf_elem}, L::NfRel{nf_elem}, a::NfRelElem{nf_elem})
    function image(x::NfRelElem{nf_elem})
      # x is an element of K
      f = data(x)
      # First evaluate the coefficients of f at a to get a polynomial over L
      # Then evaluate at b
      return evaluate(f, a)
    end

    z = new()
    z.header = MapHeader(K, L, image)
    return z
  end
end

