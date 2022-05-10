################################################################################
#
#       GrpAb/Elem.jl : Elements in finitely generated abelian groups
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
#  Copyright (C) 2015, 2016, 2017 Tommy Hofmann, Claus Fieker
#
################################################################################

export GrpAbFinGen, GrpAbFinGenElem, parent, isfinite, is_infinite, rank,
       getindex, show, +, *, ngens, snf_with_transform, nrels,
       -, ==, order, exponent,
       quo, sub, rels, has_image, haspreimage, is_snf, is_cyclic, hom, kernel,
       psylow_subgroup

import Base.+, Nemo.snf, Nemo.parent, Base.rand, Nemo.is_snf

function Base.deepcopy_internal(x::GrpAbFinGenElem, dict::IdDict)
  return GrpAbFinGenElem(parent(x), Base.deepcopy_internal(x.coeff, dict))
end

################################################################################
#
#  Constructors
#
################################################################################

# This destroy's the input. If you don't want this, use A(::fmpz_mat)

function GrpAbFinGenElem(A::GrpAbFinGen, a::fmpz_mat)
  if is_snf(A)
    return elem_snf(A, a)
  else
    return elem_gen(A, a)
  end
end

function elem_gen(A::GrpAbFinGen, a::fmpz_mat)
  assure_has_hnf(A)
  reduce_mod_hnf_ur!(a, A.hnf)
  z = GrpAbFinGenElem()
  z.parent = A
  z.coeff = a
  return z
end

function reduce_mod_snf!(a::fmpz_mat, v::Vector{fmpz})
  GC.@preserve a begin
    for i = 1:length(v)
      d = v[i]
      if !iszero(d)
        for j = 1:nrows(a)
          t = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, j - 1, i - 1)
          ccall((:fmpz_mod, libflint), Nothing, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), t, t, d)
        end
        #a[1, i] = mod(a[1, i], A.snf[i])
      end
    end
  end
end

function elem_snf(A::GrpAbFinGen, a::fmpz_mat)
  reduce_mod_snf!(a, A.snf)
  z = GrpAbFinGenElem()
  z.parent = A
  z.coeff = a
  return z
end

################################################################################
#
#  Generators
#
################################################################################

@doc Markdown.doc"""
    gens(G::GrpAbFinGen) -> Vector{GrpAbFinGenElem}

The sequence of generators of $G$.
"""
gens(G::GrpAbFinGen) = GrpAbFinGenElem[G[i] for i = 1:ngens(G)]

@doc Markdown.doc"""
    gen(G::GrpAbFinGen, i::Int) -> Vector{GrpAbFinGenElem}

The $i$-th generator of $G$.
"""
gen(G::GrpAbFinGen, i::Int) = G[i]


################################################################################
#
#  Parent
#
################################################################################

@doc Markdown.doc"""
    parent(x::GrpAbFinGenElem) -> GrpAbFinGen

Returns the parent of $x$.
"""
function parent(x::GrpAbFinGenElem)
  return x.parent
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::GrpAbFinGenElem)
  @show_special_elem(io, a)

  if get(io, :compact, false)
    print(io, a.coeff)
  else
    s = get_attribute(parent(a), :name)
    s === nothing
    if s === nothing
      print(io, "Element of\n")
      print(io, parent(a))
      print(io, "\nwith components ", a.coeff)
    else
      print(io, "Element of ", s, " with components ", a.coeff)
    end
  end
end

################################################################################
#
#  Hashing
#
################################################################################

function Base.hash(a::GrpAbFinGenElem, s::UInt)
  return hash(a.coeff, s)
end

################################################################################
#
#  Indexing
#
################################################################################

@doc Markdown.doc"""
    getindex(x::GrpAbFinGenElem, i::Int) -> fmpz

Returns the $i$-th component of the element $x$.
"""
function getindex(x::GrpAbFinGenElem, i::Int)
  return x.coeff[1, i]
end

################################################################################
#
#  Comparison
#
################################################################################

function ==(a::GrpAbFinGenElem, b::GrpAbFinGenElem)
  a.parent == b.parent || error("Elements must belong to the same group")
  return a.coeff == b.coeff
end

################################################################################
#
#  Arithmetic
#
################################################################################

function +(x::GrpAbFinGenElem, y::GrpAbFinGenElem, L::GrpAbLattice = GroupLattice)
  if x.parent === y.parent
    n = GrpAbFinGenElem(x.parent, x.coeff + y.coeff)
    return n
  end

  b, m = can_map_into(L, x.parent, y.parent)
  if b
    return GrpAbFinGenElem(y.parent, x.coeff*m) + y
  end

  b, m = can_map_into(L, y.parent, x.parent)
  if b
    return x + GrpAbFinGenElem(x.parent, y.coeff*m)
  end

  b, G, m1, m2 = can_map_into_overstructure(L, x.parent, y.parent)
  if b
    return GrpAbFinGenElem(G, x.coeff * m1 + y.coeff * m2)
  end

  error("Cannot coerce elements into common structure")
end

op(x::GrpAbFinGenElem, y::GrpAbFinGenElem, L::GrpAbLattice = GroupLattice) = +(x, y, L)

function -(x::GrpAbFinGenElem, y::GrpAbFinGenElem)
  x.parent == y.parent || error("Elements must belong to the same group")
  n = GrpAbFinGenElem(x.parent, x.coeff - y.coeff)
  return n
end

function -(x::GrpAbFinGenElem)
  n = GrpAbFinGenElem(x.parent, -x.coeff)
  return n
end

function *(x::fmpz, y::GrpAbFinGenElem)
  n = x*y.coeff
  return GrpAbFinGenElem(y.parent, n)
end

function *(x::Integer, y::GrpAbFinGenElem)
  n = x*y.coeff
  return GrpAbFinGenElem(y.parent, n)
end

*(x::GrpAbFinGenElem, y::fmpz) = y*x

*(x::GrpAbFinGenElem, y::Integer) = y*x

################################################################################
#
#  Neutral element
#
################################################################################

iszero(a::GrpAbFinGenElem) = iszero(a.coeff)

isone(a::GrpAbFinGenElem) = iszero(a.coeff)

is_identity(a::GrpAbFinGenElem) = iszero(a.coeff)

################################################################################
#
#  Parent object overloading
#
################################################################################

@doc Markdown.doc"""
    (A::GrpAbFinGen)(x::Vector{fmpz}) -> GrpAbFinGenElem

Given an array `x` of elements of type `fmpz` of the same length as ngens($A$),
this function returns the element of $A$ with components `x`.
"""
function (A::GrpAbFinGen)(x::Vector{fmpz})
  ngens(A) != length(x) && error("Lengths do not coincide")
  y = matrix(FlintZZ, 1, ngens(A), x)
  z = GrpAbFinGenElem(A, y)
  return z
end

@doc Markdown.doc"""
    (A::GrpAbFinGen)(x::Vector{Integer}) -> GrpAbFinGenElem

Given an array `x` of elements of type `Integer` of the same length as
ngens($A$), this function returns the element of $A$ with components `x`.
"""
function (A::GrpAbFinGen)(x::AbstractVector{T}) where T <: Integer
  ngens(A) != length(x) && error("Lengths do not coincide")
  z = A(map(fmpz, x))
  return z
end

@doc Markdown.doc"""
    (A::GrpAbFinGen)(x::fmpz_mat) -> GrpAbFinGenElem

Given a matrix over the integers with $1$ row and `ngens(A)` columns,
this function returns the element of $A$ with components `x`.
"""
function (A::GrpAbFinGen)(x::fmpz_mat)
  ngens(A) != ncols(x) && error("Lengths do not coincide")
  nrows(x) != 1 && error("Matrix should have only one row")
  z = GrpAbFinGenElem(A, Base.deepcopy(x))
  return z
end

function (A::GrpAbFinGen)()
  y = zero_matrix(FlintZZ, 1, ngens(A))
  z = GrpAbFinGenElem(A, y)
  return z
end

@doc Markdown.doc"""
    getindex(A::GrpAbFinGen, i::Int) -> GrpAbFinGenElem

Returns the element of $A$ with components $(0,\dotsc,0,1,0,\dotsc,0)$,
where the $1$ is at the $i$-th position.
"""
function getindex(A::GrpAbFinGen, i::Int)
  (i < 0 || i > ngens(A)) && error("Index ($i) out of range (1:$(ngens(A)))")
  if i==0
    return GrpAbFinGenElem(A, zero_matrix(FlintZZ, 1, ngens(A)))
  end
  z = zero_matrix(FlintZZ, 1, ngens(A))
  for j in 1:ngens(A)
    z[1, j] = fmpz()
  end
  z[1, i] = fmpz(1)
  return GrpAbFinGenElem(A, z)
end

################################################################################
#
#  Order
#
################################################################################

@doc Markdown.doc"""
    order(A::GrpAbFinGenElem) -> fmpz

Returns the order of $A$. It is assumed that the order is finite.
"""
function order(a::GrpAbFinGenElem)
  G, m = snf(a.parent)
  b = m\a
  o = fmpz(1)
  for i=1:ngens(G)
    if iszero(G.snf[i])
      if !iszero(b[i])
        error("Element has infinite order")
      else
        continue
      end
    end
    o = lcm(o, divexact(G.snf[i], gcd(G.snf[i], b[i])))
  end
  return o
end

##############################################################################
#
#  Random elements
#
##############################################################################

#this allows some more complicated rand(G, (2,2)) and similar.
#TODO: figure out how this SHOULD be done

rand(rng::AbstractRNG, a::Random.SamplerTrivial{GrpAbFinGen, GrpAbFinGenElem}) = rand(a.self)

@doc Markdown.doc"""
    rand(G::GrpAbFinGen) -> GrpAbFinGenElem

Returns an element of $G$ chosen uniformly at random.
"""
rand(A::GrpAbFinGen) = is_snf(A) ? rand_snf(A) : rand_gen(A)

function rand_snf(G::GrpAbFinGen)
  if !isfinite(G)
    error("Group is not finite")
  end
  return G([rand(1:G.snf[i]) for i in 1:ngens(G)])
end

function rand_gen(G::GrpAbFinGen)
  S, mS = snf(G)
  return image(mS, rand(S))
end

@doc Markdown.doc"""
    rand(G::GrpAbFinGen, B::fmpz) -> GrpAbFinGenElem

For a (potentially infinite) abelian group $G$, return an element
chosen uniformly at random with coefficients bounded by $B$.
"""
rand(G::GrpAbFinGen, B::fmpz) = is_snf(G) ? rand_snf(G, B) : rand_gen(G, B)

@doc Markdown.doc"""
    rand(G::GrpAbFinGen, B::Integer) -> GrpAbFinGenElem

For a (potentially infinite) abelian group $G$, return an element
chosen uniformly at random with coefficients bounded by $B$.
"""
rand(G::GrpAbFinGen, B::Integer) = is_snf(G) ? rand_snf(G, B) : rand_gen(G, B)

function rand_snf(G::GrpAbFinGen, B::fmpz)
  z = G([rand(1:(iszero(G.snf[i]) ? B : min(B, G.snf[i]))) for i in 1:ngens(G)])
  return z
end

function rand_snf(G::GrpAbFinGen, B::Integer)
  return rand(G, fmpz(B))
end

function rand_gen(G::GrpAbFinGen, B::fmpz)
  S, mS = snf(G)
  return image(mS, rand(S, fmpz(B)))
end

function rand_gen(G::GrpAbFinGen, B::Integer)
  return rand(G, fmpz(B))
end

################################################################################
#
#  Iterator
#
################################################################################

function Base.iterate(G::GrpAbFinGen)
  if order(G) > typemax(UInt)
    error("Group too large for iterator")
  end

  return _elem_from_enum(G, UInt(0)), UInt(1)
end

function Base.iterate(G::GrpAbFinGen, st::UInt)
  if st >= order(G)
    return nothing
  end

  a = _elem_from_enum(G, st)
  return a, st + 1
end

function _elem_from_enum(G::GrpAbFinGen, st::UInt)
  if G.is_snf
    el = fmpz[]
    s = fmpz(st)
    for i = 1:ngens(G)
      push!(el, s % G.snf[i])
      s = div(s - el[end], G.snf[i])
    end
    return G(el)
  end

  S, mS = snf(G)
  return image(mS, _elem_from_enum(S, st))
end

Base.IteratorSize(::Type{GrpAbFinGen}) = Base.HasLength()

Base.length(G::GrpAbFinGen) = Int(order(G))

Base.eltype(::Type{GrpAbFinGen}) = GrpAbFinGenElem
