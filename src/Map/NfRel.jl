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
mutable struct NfRelToNf <: Map{NfRel{nf_elem}, AnticNumberField, HeckeMap, NfRelToNf}
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
      r = Vector{nf_elem}(undef, degree(f)+1)
      for  i = 0:degree(f)
        r[i+1] = evaluate(R(coeff(f, i)), a)
      end
      return evaluate(Ly(r), b)
    end

    function preimage(x::nf_elem)
      # x is an element of L
      f = S(x)
      res = evaluate(f, c)
      return res
    end

    z = new()
    z.header = MapHeader(K, L, image, preimage)
    return z
  end
end

function show(io::IO, h::NfRelToNf)
  println(io, "Isomorphism between ", domain(h), "\nand ", codomain(h))
end

mutable struct NfRelRelToNfRel{T} <: Map{NfRel{NfRelElem{T}}, NfRel{T}, HeckeMap, NfRelRelToNfRel} 
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

function hom(K::NfRel, L::NfRel, a::NfRelElem; check::Bool = false)
   if base_field(K) != base_field(L)
     error("The base fields do not coincide!")
   end
   if check 
     if !iszero(evaluate(K.pol, a))
       error("Data does not define a homomorphism")
     end
   end
   return NfRelToNfRelMor(K, L, a)
end


mutable struct NfRelToNfRelMor{T, S} <: Map{NfRel{T}, NfRel{S}, HeckeMap, NfRelToNfRelMor}
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
    # First evaluate the coefficients of f at a to get a polynomial over L
    f = data(x)
    g = Vector{nf_elem}(undef, degree(f)+1)
    for i=0:degree(f)
      g[i+1] = A(coeff(f, i))
    end
    Sx = PolynomialRing(base_field(L), "x")[1]
    g1 = Sx(g)
    # Then evaluate at b
    return g1(a)
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
#  z.coeff_aut = _identity(base_ring(K))
  z.header = MapHeader(K, L, image)
  return z
end

id_hom(K::NfRel) = NfRelToNfRelMor(K, K, gen(K))

morphism_type(::Type{NfRel{T}}) where {T} = NfRelToNfRel{T}

function ^(f::NfRelToNfRelMor, b::Int)
  K = domain(f)
  @assert K == codomain(f)
  d = absolute_degree(K)
  b = mod(b, d)
  if b == 0
    return id_hom(K)
  elseif b == 1
    return f
  else
    bit = ~((~UInt(0)) >> 1)
    while (UInt(bit) & b) == 0
      bit >>= 1
    end
    z = f
    bit >>= 1
    while bit != 0
      z = z * z
      if (UInt(bit) & b) != 0
        z = z * f
      end
      bit >>= 1
    end
    return z
  end
end

function ==(x::NfRelToNfRelMor{T}, y::NfRelToNfRelMor{T}) where T
  if base_field(domain(x)) == base_field(domain(y))
    return x.prim_img == y.prim_img
  end
  return (x.coeff_aut == y.coeff_aut) && (x.prim_img == y.prim_img) 
end

function *(x::NfRelToNfRelMor{T}, y::NfRelToNfRelMor{T}) where T
  @assert domain(y) == codomain(x)
  #global _D
  #_s = Base.stacktrace()[2:3]
  #if !(_s in keys(_D))
  #  _D[_s] = true
  #  println("Relative called ...")
  #  Base.show_backtrace(stdout, Base.stacktrace()[2:3])
  #end

  new_prim_img = y(x.prim_img)
  
  if isdefined(y, :coeff_aut)
    if !isdefined(x, :coeff_aut)
      new_coeff_aut = y.coeff_aut
    else
      new_coeff_aut = x.coeff_aut * y.coeff_aut
    end
    return NfRelToNfRelMor(domain(y), codomain(x), new_coeff_aut, new_prim_img)
  else
    if isdefined(x, :coeff_aut)
      new_coeff_aut = x.coeff_aut
      return NfRelToNfRelMor(domain(x), codomain(y), new_coeff_aut, new_prim_img)
    else
      return NfRelToNfRelMor(domain(x), codomain(y), new_prim_img)
    end
  end
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

mutable struct NfRelToFqMor{T} <: Map{NfRel{T}, FqFiniteField, HeckeMap, NfRelToFqMor}
  header::MapHeader{NfRel{T}, FqFiniteField}

  function NfRelToFqMor{T}() where {T}
    z = new{T}()
    z.header = MapHeader{NfRel{T}, FqFiniteField}()
    return z
  end
end

function _automorphisms(L::NfRel)
  if degree(L) == 1
    auts = NfRelToNfRelMor[hom(K, K, one(K))]
  else
    f = L.pol
    Lt, t = PolynomialRing(L, "t", cached = false)
    f1 = change_ring(f, Lt)
    divpol = Lt([ -gen(L), L(1) ])
    f1 = divexact(f1, divpol)
    lr = roots(f1)
    Aut1 = Vector{NfRelToNfRelMor}(undef, length(lr) + 1)
    for i = 1:length(lr)
      Aut1[i] = hom(L, L, lr[i], check = false)
    end
    Aut1[end] = id_hom(L)
    auts = closure(Aut1, *, id_hom(L)) # One could probably do this modular as in the absolute case
  end
  return auts
end

function automorphisms(L::NfRel; copy::Bool = true)
  try
    Aut = _get_automorphisms_nf_rel(L)::Vector{ <: NfRelToNfRelMor}
    if copy
      return deepcopy(Aut)
    else
      return Aut
    end
  catch e
    if !isa(e, AccessorNotSetError)
      rethrow(e)
    end
  end
  auts = _automorphisms(L)
  _set_automorphisms_nf_rel(L, auts)
  if copy
    return deepcopy(auts)
  else
    return auts
  end
end
