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

import Base.+, Nemo.snf, Nemo.parent, Base.rand, Nemo.is_snf

function Base.deepcopy_internal(x::FinGenAbGroupElem, dict::IdDict)
  return FinGenAbGroupElem(parent(x), Base.deepcopy_internal(x.coeff, dict))
end

################################################################################
#
#  Constructors
#
################################################################################

function reduce_mod_snf!(a::ZZMatrix, v::Vector{ZZRingElem})
  GC.@preserve a begin
    for i = 1:length(v)
      d = v[i]
      if !iszero(d)
        for j = 1:nrows(a)
          t = mat_entry_ptr(a, j, i)
          ccall((:fmpz_mod, libflint), Nothing, (Ptr{ZZRingElem}, Ptr{ZZRingElem}, Ref{ZZRingElem}), t, t, d)
        end
        #a[1, i] = mod(a[1, i], A.snf[i])
      end
    end
  end
end

function assure_reduced!(A::FinGenAbGroup, a::ZZMatrix)
  if is_snf(A)
    reduce_mod_snf!(a, A.snf)
  else
    assure_has_hnf(A)
    reduce_mod_hnf_ur!(a, A.hnf)
  end
end

################################################################################
#
#  Generators
#
################################################################################

@doc raw"""
    gens(G::FinGenAbGroup) -> Vector{FinGenAbGroupElem}

The sequence of generators of $G$.
"""
gens(G::FinGenAbGroup) = FinGenAbGroupElem[G[i] for i = 1:ngens(G)]

@doc raw"""
    gen(G::FinGenAbGroup, i::Int) -> Vector{FinGenAbGroupElem}

The $i$-th generator of $G$.
"""
gen(G::FinGenAbGroup, i::Int) = G[i]


################################################################################
#
#  Parent
#
################################################################################

@doc raw"""
    parent(x::FinGenAbGroupElem) -> FinGenAbGroup

Returns the parent of $x$.
"""
function parent(x::FinGenAbGroupElem)
  return x.parent
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::FinGenAbGroupElem)
  @show_special_elem(io, a)

  if get(io, :compact, false) || is_terse(io) || (get(io, :typeinfo, Any)) == typeof(a)
    print(io, "[", join(a.coeff, ", "), "]")
    return
  end

  print(io, "Abelian group element [", join(a.coeff, ", "), "]")
end

################################################################################
#
#  Hashing
#
################################################################################

function Base.hash(a::FinGenAbGroupElem, s::UInt)
  return hash(a.coeff, s)
end

################################################################################
#
#  Indexing
#
################################################################################

@doc raw"""
    getindex(x::FinGenAbGroupElem, i::Int) -> ZZRingElem

Returns the $i$-th component of the element $x$.
"""
function getindex(x::FinGenAbGroupElem, i::Int)
  return x.coeff[1, i]
end

################################################################################
#
#  Comparison
#
################################################################################

function ==(a::FinGenAbGroupElem, b::FinGenAbGroupElem)
  a.parent == b.parent || error("Elements must belong to the same group")
  return a.coeff == b.coeff
end

################################################################################
#
#  Arithmetic
#
################################################################################

function +(x::FinGenAbGroupElem, y::FinGenAbGroupElem, L::GrpAbLattice = GroupLattice)
  if x.parent === y.parent
    n = FinGenAbGroupElem(x.parent, x.coeff + y.coeff)
    return n
  end

  b, m = can_map_into(L, x.parent, y.parent)
  if b
    return FinGenAbGroupElem(y.parent, x.coeff*m) + y
  end

  b, m = can_map_into(L, y.parent, x.parent)
  if b
    return x + FinGenAbGroupElem(x.parent, y.coeff*m)
  end

  b, G, m1, m2 = can_map_into_overstructure(L, x.parent, y.parent)
  if b
    return FinGenAbGroupElem(G, x.coeff * m1 + y.coeff * m2)
  end

  error("Cannot coerce elements into common structure")
end

op(x::FinGenAbGroupElem, y::FinGenAbGroupElem, L::GrpAbLattice = GroupLattice) = +(x, y, L)

function -(x::FinGenAbGroupElem, y::FinGenAbGroupElem)
  x.parent == y.parent || error("Elements must belong to the same group")
  n = FinGenAbGroupElem(x.parent, x.coeff - y.coeff)
  return n
end

function -(x::FinGenAbGroupElem)
  n = FinGenAbGroupElem(x.parent, -x.coeff)
  return n
end

function *(x::ZZRingElem, y::FinGenAbGroupElem)
  n = x*y.coeff
  return FinGenAbGroupElem(y.parent, n)
end

function *(x::Integer, y::FinGenAbGroupElem)
  n = x*y.coeff
  return FinGenAbGroupElem(y.parent, n)
end

*(x::FinGenAbGroupElem, y::ZZRingElem) = y*x

*(x::FinGenAbGroupElem, y::Integer) = y*x

###############################################################################
#
#   Unsafe operators
#
###############################################################################

function reduce!(x::FinGenAbGroupElem)
  assure_reduced!(parent(x), x.coeff)
  return x
end

function zero!(x::FinGenAbGroupElem)
  zero!(x.coeff)
  # no reduction necessary
  return x
end

function neg!(x::FinGenAbGroupElem)
  neg!(x.coeff)
  return reduce!(x)
end

# TODO: set! for ZZMatrix not yet implemented, hence this is not yet implemented
#function set!(x::FinGenAbGroupElem, y::FinGenAbGroupElem)
#  set!(x.coeff, y.coeff)
#  # no reduction necessary
#  return x
#end

function add!(x::FinGenAbGroupElem, y::FinGenAbGroupElem, z::FinGenAbGroupElem)
  add!(x.coeff, y.coeff, z.coeff)
  return reduce!(x)
end

function sub!(x::FinGenAbGroupElem, y::FinGenAbGroupElem, z::FinGenAbGroupElem)
  sub!(x.coeff, y.coeff, z.coeff)
  return reduce!(x)
end

function mul!(x::FinGenAbGroupElem, y::FinGenAbGroupElem, z::Union{Int,ZZRingElem})
  mul!(x.coeff, y.coeff, z)
  return reduce!(x)
end

function addmul!(x::FinGenAbGroupElem, y::FinGenAbGroupElem, z::Union{Int,ZZRingElem})
  addmul!(x.coeff, y.coeff, z)
  return reduce!(x)
end

function addmul_delayed_reduction!(x::FinGenAbGroupElem, y::FinGenAbGroupElem, z::Union{Int,ZZRingElem})
  addmul!(x.coeff, y.coeff, z)
  return x
end

################################################################################
#
#  Neutral element
#
################################################################################

iszero(a::FinGenAbGroupElem) = iszero(a.coeff)

isone(a::FinGenAbGroupElem) = iszero(a.coeff)

is_identity(a::FinGenAbGroupElem) = iszero(a.coeff)

################################################################################
#
#  Parent object overloading
#
################################################################################

@doc raw"""
    (A::FinGenAbGroup)(x::Vector{ZZRingElem}) -> FinGenAbGroupElem

Given an array `x` of elements of type `ZZRingElem` of the same length as ngens($A$),
this function returns the element of $A$ with components `x`.
"""
function (A::FinGenAbGroup)(x::Vector{ZZRingElem})
  ngens(A) != length(x) && error("Lengths do not coincide")
  y = matrix(FlintZZ, 1, ngens(A), x)
  z = FinGenAbGroupElem(A, y)
  return z
end

@doc raw"""
    (A::FinGenAbGroup)(x::Vector{Integer}) -> FinGenAbGroupElem

Given an array `x` of elements of type `Integer` of the same length as
ngens($A$), this function returns the element of $A$ with components `x`.
"""
function (A::FinGenAbGroup)(x::AbstractVector{T}) where T <: Integer
  ngens(A) != length(x) && error("Lengths do not coincide")
  z = A(map(ZZRingElem, x))
  return z
end

@doc raw"""
    (A::FinGenAbGroup)(x::ZZMatrix) -> FinGenAbGroupElem

Given a matrix over the integers with either $1$ row and `ngens(A)` columns
or `ngens(A)` rows and $1$ column, this function returns the element of $A$
with components `x`.
"""
function (A::FinGenAbGroup)(x::ZZMatrix)
  if nrows(x) != 1
    ncols(x) != 1 && error("Matrix should either have only one row or one column")
    ngens(A) != nrows(x) && error("Lengths do not coincide")
    x = transpose(x)
  end
  ngens(A) != ncols(x) && error("Lengths do not coincide")
  z = FinGenAbGroupElem(A, Base.deepcopy(x))
  return z
end

function (A::FinGenAbGroup)()
  y = zero_matrix(FlintZZ, 1, ngens(A))
  z = FinGenAbGroupElem(A, y)
  return z
end

zero(A::FinGenAbGroup) = A()

@doc raw"""
    getindex(A::FinGenAbGroup, i::Int) -> FinGenAbGroupElem

Returns the element of $A$ with components $(0,\dotsc,0,1,0,\dotsc,0)$,
where the $1$ is at the $i$-th position.
"""
function getindex(A::FinGenAbGroup, i::Int)
  (i < 0 || i > ngens(A)) && error("Index ($i) out of range (1:$(ngens(A)))")
  if i==0
    return FinGenAbGroupElem(A, zero_matrix(FlintZZ, 1, ngens(A)))
  end
  z = zero_matrix(FlintZZ, 1, ngens(A))
  for j in 1:ngens(A)
    z[1, j] = ZZRingElem()
  end
  z[1, i] = ZZRingElem(1)
  return FinGenAbGroupElem(A, z)
end

################################################################################
#
#  Order
#
################################################################################

@doc raw"""
    order(A::FinGenAbGroupElem) -> ZZRingElem

Returns the order of $A$. It is assumed that the order is finite.
"""
function order(a::FinGenAbGroupElem)
  G, m = snf(a.parent)
  b = m\a
  o = ZZRingElem(1)
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

rand(rng::AbstractRNG, a::Random.SamplerTrivial{FinGenAbGroup, FinGenAbGroupElem}) = rand(a.self)

@doc raw"""
    rand(G::FinGenAbGroup) -> FinGenAbGroupElem

Returns an element of $G$ chosen uniformly at random.
"""
rand(A::FinGenAbGroup) = is_snf(A) ? rand_snf(A) : rand_gen(A)

function rand_snf(G::FinGenAbGroup)
  if !isfinite(G)
    error("Group is not finite")
  end
  return G([rand(1:G.snf[i]) for i in 1:ngens(G)])
end

function rand_gen(G::FinGenAbGroup)
  S, mS = snf(G)
  return image(mS, rand(S))
end

@doc raw"""
    rand(G::FinGenAbGroup, B::ZZRingElem) -> FinGenAbGroupElem

For a (potentially infinite) abelian group $G$, return an element
chosen uniformly at random with coefficients bounded by $B$.
"""
rand(G::FinGenAbGroup, B::ZZRingElem) = is_snf(G) ? rand_snf(G, B) : rand_gen(G, B)

@doc raw"""
    rand(G::FinGenAbGroup, B::Integer) -> FinGenAbGroupElem

For a (potentially infinite) abelian group $G$, return an element
chosen uniformly at random with coefficients bounded by $B$.
"""
rand(G::FinGenAbGroup, B::Integer) = is_snf(G) ? rand_snf(G, B) : rand_gen(G, B)

function rand_snf(G::FinGenAbGroup, B::ZZRingElem)
  z = G([rand(1:(iszero(G.snf[i]) ? B : min(B, G.snf[i]))) for i in 1:ngens(G)])
  return z
end

function rand_snf(G::FinGenAbGroup, B::Integer)
  return rand(G, ZZRingElem(B))
end

function rand_gen(G::FinGenAbGroup, B::ZZRingElem)
  S, mS = snf(G)
  return image(mS, rand(S, ZZRingElem(B)))
end

function rand_gen(G::FinGenAbGroup, B::Integer)
  return rand(G, ZZRingElem(B))
end

################################################################################
#
#  Iterator
#
################################################################################

function Base.iterate(G::FinGenAbGroup)
  if order(G) > typemax(UInt)
    error("Group too large for iterator")
  end

  return _elem_from_enum(G, UInt(0)), UInt(1)
end

function Base.iterate(G::FinGenAbGroup, st::UInt)
  if st >= order(G)
    return nothing
  end

  a = _elem_from_enum(G, st)
  return a, st + 1
end

function _elem_from_enum(G::FinGenAbGroup, st::UInt)
  if G.is_snf
    el = ZZRingElem[]
    s = ZZRingElem(st)
    for i = 1:ngens(G)
      push!(el, s % G.snf[i])
      s = div(s - el[end], G.snf[i])
    end
    return G(el)
  end

  S, mS = snf(G)
  return image(mS, _elem_from_enum(S, st))
end

Base.IteratorSize(::Type{FinGenAbGroup}) = Base.HasLength()

Base.length(G::FinGenAbGroup) = Int(order(G))

Base.eltype(::Type{FinGenAbGroup}) = FinGenAbGroupElem
