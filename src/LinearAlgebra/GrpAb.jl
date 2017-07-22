################################################################################
#
#             GrpAb.jl : Finitely generated abelian groups
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
#  Copyright (C) 2015, 2016, 2017 Tommy Hofmann, Claus Fieker
#
################################################################################

export GrpAbFinGen, GrpAbFinGenElem, parent, isfinite, isinfinite, rank,
       getindex, show, +, *, ngens, snf_with_transform, nrels,
       -, ==, istrivial, order, exponent, AbelianGroup, DiagonalGroup,
       quo, sub, rels, hasimage, haspreimage, issnf, iscyclic, hom, kernel

import Base.+, Nemo.snf, Nemo.parent, Base.rand, Nemo.issnf

################################################################################
#
#  Functions for some abstract interfaces
#
################################################################################

elem_type(G::GrpAbFinGen) = GrpAbFinGenElem

elem_type(::Type{GrpAbFinGen}) = GrpAbFinGenElem

parent_type(::Type{GrpAbFinGenElem}) = GrpAbFinGen

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, A::GrpAbFinGen)
  if issnf(A)
    show_snf(io, A)
  else
    show_gen(io, A)
  end
end

function show_gen(io::IO, A::GrpAbFinGen)
  print(io, "(General) abelian group with relation matrix\n$(A.rels)")
  if isdefined(A, :snf_map)
    println(io, "\nwith structure of ", codomain(A.snf_map))
  end
end

function show_snf(io::IO, A::GrpAbFinGen)
  len = length(A.snf)

  println(io, "Abelian group")

  if len == 0
    print(io, "Z/1")
    return
  end

  if A.snf[1] == 0
    if len == 1
      print(io, "Z")
    else
      print(io, "Z^$(len)")
    end
    return
  end

  i = 1
  while i <= len
    inv = A.snf[i]
    j = 1
    while i + j <= len && inv == A.snf[i + j] 
      j += 1
    end
    if iszero(inv)
      print(io, "Z")
    else
      print(io, "Z/$(inv)")
    end
    if j > 1
      print(io, "^$(j)")
    end
    if i + j - 1 < len
      print(io, " x ")
    end
    i += j
  end  
end

function show(io::IO, a::GrpAbFinGenElem)
  print(io, "Element of\n$(a.parent)\n with components\n$(a.coeff)")
end

################################################################################
#
#  Constructors for GrpAbFinGenElem
#
################################################################################

# Helper function
function reduce_mod_hnf!(a::fmpz_mat, H::fmpz_mat)
  j = 1
  for i=1:min(rows(H), cols(H))
    while j <= cols(H) && H[i,j] == 0
      j+=1
    end
    if j > cols(H)
      return
    end
    q = fdiv(a[1, j], H[i,j])
    for k=j:cols(a)
      a[1,k] =  a[1, k] - q*H[i,k]
    end
  end
end

# TH: This destroys the input a. Do we want this?
function GrpAbFinGenElem(A::GrpAbFinGen, a::fmpz_mat)
  if issnf(A)
    return elem_snf(A, a)
  else
    return elem_gen(A, a)
  end
end

function elem_gen(A::GrpAbFinGen, a::fmpz_mat)
  assert_hnf(A)
  reduce_mod_hnf!(a, A.hnf)
  z = GrpAbFinGenElem()
  z.parent = A
  z.coeff = a
  return z
end

function elem_snf(A::GrpAbFinGen, a::fmpz_mat)
  for i=1:ngens(A)
    if A.snf[i] != 0
      a[1,i] = mod(a[1,i], A.snf[i])
    end
  end
  z = GrpAbFinGenElem()
  z.parent = A
  z.coeff = a
  return z
end

function Base.hash(a::GrpAbFinGenElem, s::UInt)
  return hash(a.coeff, s)
end
################################################################################
#
#  Field access
#
################################################################################

doc"""
***
    issnf(G::GrpAbFinGen) -> Bool

> Returns whether the current relation matrix of the group $G$ is in Smith
> normal form.
"""
issnf(A::GrpAbFinGen) = A.issnf

doc"""
***
    parent(x::GrpAbFinGenElem) -> GrpAbFinGen

> Returns the parent of $x$.
"""
function parent(x::GrpAbFinGenElem)
  return x.parent
end

doc"""
***
    ngens(G::GrpAbFinGen) -> Int

> Returns the number of generators of $G$ in the current representation.
"""
function ngens(A::GrpAbFinGen)
  if issnf(A)
    return length(A.snf)
  else
    return cols(A.rels)
  end
end

doc"""
***
    nrels(G::GrpAbFinGen) -> Int

> Returns the number of relations of $G$ in the current representation.
"""
function nrels(A::GrpAbFinGen)
  if issnf(A)
    return length(A.snf)
  else
    return rows(A.rels)
  end
end

doc"""
***
    getindex(x::GrpAbFinGenElem, i::Int) -> fmpz

> Returns the $i$-th component of the element $x$.
"""
function getindex(x::GrpAbFinGenElem, i::Int)
  return x.coeff[1, i]
end

doc"""
***
    rels(A::GrpAbFinGen) -> fmpz_mat

> Returns the currently used relations of $G$ as a single matrix.
"""
function rels(A::GrpAbFinGen)
  if issnf(A)
    return rels_snf(A)
  else
    return rels_gen(A)
  end
end

function rels_gen(A::GrpAbFinGen)
  return A.rels
end

function rels_snf(A::GrpAbFinGen)
  M = MatrixSpace(FlintZZ, ngens(A), ngens(A))()
  for i=1:ngens(A)
    M[i,i] = A.snf[i]
  end
  return M
end

function assert_hnf(A::GrpAbFinGen)
  isdefined(A, :hnf) && return
  A.hnf = hnf(A.rels)
end

################################################################################
#
#  Some functionality for maps between abelian groups
#
################################################################################

doc"""
***
    haspreimage(M::GrpAbFinGenMap, a::GrpAbFinGenElem) -> Bool, GrpAbFinGenElem

> Returns whether $a$ is in the image of $M$. If so, the second return value is
> an element $b$ with $M(b) = a$.
"""
function haspreimage(M::GrpAbFinGenMap, a::GrpAbFinGenElem)
  if isdefined(M, :imap)
    return preimage(M, a)
  end

  m = vcat(M.map, rels(codomain(M)))
  fl, p = cansolve(m', a.coeff')
  if fl
    return true, domain(M)(sub(p', 1:1, 1:ngens(domain(M))))
  else
    return false, domain(M)[1]
  end
end

# I don't know what this function is doing mathematically
# Everything has an image?
# No, it does not. Suppose
# s, ms = sub(...) so ms: s -> G
# h = inv(ms)      so  h: G -> s
# then hasimage(h, ..) would check if x in s
function hasimage(M::GrpAbFinGenMap, a::GrpAbFinGenElem)
  if isdefined(M, :map)
    return image(M, a)
  end

  m = vcat(M.imap, rels(domain(M)))
  fl, p = cansolve(m, a.coeff)
  if fl
    return true, codomain(M)(sub(p, 1:1, 1:ngens(codomain(M))))
  else
    return false, codomain(M)[1]
  end
end


################################################################################
#
#  Arithmetic
#
################################################################################

doc"""
***
    ==(a::GrpFinGenElem, b::GrpAbFinGenElem) -> Bool

> Returns whether $a$ and $b$ are equal.
"""
function ==(a::GrpAbFinGenElem, b::GrpAbFinGenElem)
  a.parent == b.parent || error("Elements must belong to the same group")
  return a.coeff == b.coeff
end

doc"""
***
    +(x::GrpAbFinGenElem, y::GrpAbFinGenElem) -> GrpAbFinGenElem

> Returns $x + y$.
"""
function +(x::GrpAbFinGenElem, y::GrpAbFinGenElem)
  x.parent == y.parent || error("Elements must belong to the same group")
  n = GrpAbFinGenElem(x.parent, x.coeff + y.coeff)
  return n
end

doc"""
***
    -(x::GrpAbFinGenElem, y::GrpAbFinGenElem) -> GrpAbFinGenElem

> Returns  $x - y$.
"""
function -(x::GrpAbFinGenElem, y::GrpAbFinGenElem)
  x.parent == y.parent || error("Elements must belong to the same group")
  n = GrpAbFinGenElem(x.parent, x.coeff - y.coeff)
  return n
end

doc"""
***
    -(x::GrpAbFinGenElem) -> GrpAbFinGenElem

> Computes $-x$.
"""
function -(x::GrpAbFinGenElem)
  n = GrpAbFinGenElem(x.parent, -x.coeff)
  return n
end

doc"""
***
    *(x::fmpz, y::GrpAbFinGenElem) -> GrpAbFinGenElem

> Returns $x \cdot y$.
"""
function *(x::fmpz, y::GrpAbFinGenElem)
  n = x*y.coeff
  return GrpAbFinGenElem(y.parent, n)
end

doc"""
***
    *(x::Integer, y::GrpAbFinGenElem) -> GrpAbFinGenElem

> Computes $x \cdot y$.
"""
function *(x::Integer, y::GrpAbFinGenElem)
  n = x*y.coeff
  return GrpAbFinGenElem(y.parent, n)
end

*(x::GrpAbFinGenElem, y::fmpz) = y*x

*(x::GrpAbFinGenElem, y::Integer) = y*x

iszero(a::GrpAbFinGenElem) = iszero(a.coeff)
isone(a::GrpAbFinGenElem) = iszero(a.coeff)

################################################################################
#
#  Parent object overloading
#
################################################################################

doc"""
***
    (A::GrpAbFinGen)(x::Array{fmpz, 1}) -> GrpAbFinGenElem

> Given an array `x` of elements of type `fmpz` of the same length as ngens($A$),
> this function returns the element of $A$ with components `x`.
"""
function (A::GrpAbFinGen)(x::Array{fmpz, 1})
  ngens(A) != length(x) && error("Lengths do not coincide")
  y = Matrix(FlintZZ, 1, ngens(A), x)
  z = GrpAbFinGenElem(A, y)
  return z
end

doc"""
***
    (A::GrpAbFinGen)(x::Array{Integer, 1}) -> GrpAbFinGenElem

> Given an array `x` of elements of type `Integer` of the same length as
> ngens($A$), this function returns the element of $A$ with components `x`.
"""
function (A::GrpAbFinGen){T <: Integer}(x::Array{T, 1})
  ngens(A) != length(x) && error("Lengths do not coincide")
  z = A(map(fmpz, x))
  return z
end

doc"""
***
    (A::GrpAbFinGen)(x::fmpz_mat) -> GrpAbFinGenElem

> Given a matrix over the integers with $1$ row and `ngens(A)` columns,
> this function returns the element of $A$ with components `x`.
"""
function (A::GrpAbFinGen)(x::fmpz_mat)
  ngens(A) != cols(x) && error("Lengths do not coincide")
  rows(x) != 1 && error("Matrix should have only one row")
  z = GrpAbFinGenElem(A, x)
  return z
end

doc"""
***
    getindex(A::GrpAbFinGen, i::Int) -> GrpAbFinGenElem

> Returns the element of $A$ with components $(0,\dotsc,0,1,0,\dotsc,0)$,
> where the $1$ is at the $i$-th position.
"""
function getindex(A::GrpAbFinGen, i::Int)
  (i<1 || i > ngens(A)) && error("Index out of range")
  z = MatrixSpace(FlintZZ, 1, ngens(A))()
  for j in 1:ngens(A)
    z[1,j] = fmpz()
  end
  z[1,i] = fmpz(1)
  return A(z)
end

doc"""
***
  isdiag(A::fmpz_mat)

> Tests if A is diagonal.
"""
function isdiag(A::fmpz_mat)
  for i = 1:cols(A)
    for j= 1:rows(A)
      if i != j && A[j,i]!=0
        return false
      end
    end
  end
  return true
end

################################################################################
#
#  Smith normal form
#
################################################################################

doc"""
***
    snf(A::GrpAbFinGen) -> GrpAbFinGen, Map

> Returns a pair $(G, f)$, where $G$ is an abelian group in canonical Smith
> normal form isomorphic to $G$ and an isomorphism $f : G \to A$.
"""
function snf(G::GrpAbFinGen)
  if isdefined(G, :snf_map)
    return codomain(G.snf_map)::GrpAbFinGen, G.snf_map
  end

  if issnf(G)
    G.snf_map = IdentityMap(G)
    return G, G.snf_map
  end

  S, _, T = snf_with_transform(G.rels, false, true)
  d = fmpz[S[i,i] for i=1:min(rows(S), cols(S))]

  while length(d) < ngens(G)
    push!(d, 0)
  end

  #s = Array{fmpz, 1}()
  s = fmpz[ d[i] for i in 1:length(d) if d[i] !=  1]
  #for i=1:length(d)
  #  if d[i] != 1
  #    push!(s, d[i])
  #  end
  #end
  TT = MatrixSpace(FlintZZ, rows(T), length(s))()
  j = 1
  for i=1:length(d)
    if d[i] != 1
      for k=1:rows(T)
        TT[k, j] = T[k, i]
      end
      j += 1
    end
  end

  TTi = MatrixSpace(FlintZZ, length(s), rows(T))()
  Ti = inv(T)

  j = 1
  for i=1:length(d)
    if d[i] != 1
      for k=1:rows(T)
        TTi[j, k] = Ti[i, k]
      end
      j += 1
    end
  end

  H = GrpAbFinGen(s)
  mp = GrpAbFinGenMap(G, H, TT, TTi)
  G.snf_map = mp
  return H, mp
end

################################################################################
#
#  Predicates and basic invariants
#
################################################################################

doc"""
***
    isfinite(A::GrpAbFinGen) -> Bool

> Returns whether $A$ is finite.
"""
isfinite(A::GrpAbFinGen) = issnf(A) ? isfinite_snf(A) : isfinite_gen(A)

isfinite_snf(A::GrpAbFinGen) = length(A.snf) == 0 || A.snf[end] != 0

isfinite_gen(A::GrpAbFinGen) = isfinite(snf(A)[1])

doc"""
***
    isinfinite(A::GrpAbFinGen) -> Bool

> Returns whether $A$ is infinite.
"""
isinfinite(A::GrpAbFinGen) = !isfinite(A)

doc"""
***
    rank(A::GrpAbFinGenGen) -> Int

> Returns the rank of $A$, that is, the dimension of the
> $\mathbf{Q}$-vectorspace $A \otimes_{\mathbf Z} \mathbf Q$.
"""
rank(A::GrpAbFinGen) = issnf(A) ? rank_snf(A) : rank_gen(A)

rank_snf(A::GrpAbFinGen) = length(find(x -> x == 0, A.snf))

rank_gen(A::GrpAbFinGen) = rank(snf(A)[1])

################################################################################
#
#  Order functions
#
################################################################################

doc"""
***
    order(A::GrpAbFinGenElem, i::Int) -> fmpz

> Returns the order of $A$. It is assumed that the order is finite.
"""
function order(a::GrpAbFinGenElem)
  G, m = snf(a.parent)
  b = m(a)
  o = fmpz(1)
  for i=1:ngens(G)
    if G.snf[i] == 0 && b[i] != 0
      error("Element has infinite order")
    end
    o = lcm(o, divexact(G.snf[i], gcd(G.snf[i], b[i])))
  end
  return o
end

doc"""
***
    order(A::GrpAbFinGen) -> fmpz

> Returns the order of $A$. It is assumed that $A$ is finite.
"""
order(A::GrpAbFinGen) = issnf(A) ? order_snf(A) : order_gen(A)

function order_snf(A::GrpAbFinGen)
  isinfinite(A) && error("Group must be finite")
  return prod(A.snf)
end

order_gen(A::GrpAbFinGen) = order(snf(A)[1])

doc"""
***
    exponent(A::GrpAbFinGen) -> fmpz

> Returns the exponent of $A$. It is assumed that $A$ is finite.
"""
exponent(A::GrpAbFinGen) = issnf(A) ? exponent_snf(A) : exponent_gen(A)

function exponent_snf(A::GrpAbFinGen)
  isinfinite(A) && error("Group must be finite")
  return A.snf[end]
end

exponent_gen(A::GrpAbFinGen) = exponent(snf(A)[1])

doc"""
***
    istrivial(A::GrpAbFinGen) -> Bool

> Checks if $A$ is the trivial group.
"""
istrivial(A::GrpAbFinGen) = isfinite(A) && order(A) == 1

doc"""
***
    isisomorphic(G::GrpAbFinGen, H::GrpAbFinGen) -> bool

> Checks if $G$ and $H$ are isomorphic.
"""
function isisomorphic(G::GrpAbFinGen, H::GrpAbFinGen)
  b = filter(x -> x != 1, snf(G)[1].snf) == filter(x -> x != 1, snf(H)[1].snf)
  return b
end

##############################################################################
#
#  Creation
#
##############################################################################

# We do we have AbelianGroup and DiagonalGroup?
doc"""
***
    AbelianGroup(M::fmpz_mat) -> GrpAbFinGen
    AbelianGroup(M::Array{fmpz, 2}) -> GrpAbFinGen
    AbelianGroup(M::Array{Integer, 2}) -> GrpAbFinGen
    AbelianGroup(M::Array{fmpz, 1}) -> GrpAbFinGen
    AbelianGroup(M::Array{Integer, 1}) -> GrpAbFinGen

> Creates the abelian group with relation matrix `M`. That is, the group will
> have `cols(M)` generators and each row of `M` describes one relation.
"""
function AbelianGroup(M::fmpz_mat)
  return GrpAbFinGen(M)
end

function AbelianGroup(M::Array{fmpz, 2})
  return AbelianGroup(MatrixSpace(FlintZZ, size(M)[1], size(M)[2])(M))
end

function AbelianGroup{T <: Integer}(M::Array{T, 2})
  return AbelianGroup(MatrixSpace(FlintZZ, size(M)[1], size(M)[2])(M))
end

function AbelianGroup(M::Array{fmpz, 1})
  return AbelianGroup(MatrixSpace(FlintZZ, 1, length(M))(M'))
end

function AbelianGroup{T <: Integer}(M::Array{T, 1})
  return AbelianGroup(MatrixSpace(FlintZZ, 1, length(M))(M'))
end

doc"""
***
    DiagonalGroup(M::fmpz_mat) -> GrpAbFinGen
    DiagonalGroup(M::Array{fmpz, 1}) -> GrpAbFinGen
    DiagonalGroup(M::Array{Integer, 1}) -> GrpAbFinGen

> Creates the abelian group as the product of cyclic groups Z/M[i].
"""
function DiagonalGroup(M::fmpz_mat)
  if rows(M) != 1
    error("The argument must have only one row")
  end

  N = MatrixSpace(FlintZZ, cols(M), cols(M))()
  for i=1:cols(M)
    N[i,i] = M[1,i]
  end
  if issnf(N)
    return GrpAbFinGen(fmpz[M[1,i] for i=1:cols(M)])
  else
    return GrpAbFinGen(N)
  end
end

function DiagonalGroup{T <: Union{Integer, fmpz}}(M::Array{T, 1})
  N = MatrixSpace(FlintZZ, length(M), length(M))()
  for i=1:length(M)
    N[i,i] = M[i]
  end
  if issnf(N)
    return GrpAbFinGen(M)
  else
    return GrpAbFinGen(N)
  end
end

# missing:
# is_torsion, torsion_subgroup, subgroups, ...

##############################################################################
#
#  Random elements
#
##############################################################################

doc"""
***
    rand(G::GrpAbFinGen) -> GrpAbFinGenElem

> Returns an element of $G$ chosen uniformly at random.
"""
rand(A::GrpAbFinGen) = issnf(A) ? rand_snf(A) : rand_gen(A)

function rand_snf(G::GrpAbFinGen)
  if !isfinite(G)
    error("Group is not finite")
  end
  return G([rand(1:G.snf[i]) for i in 1:ngens(G)])
end

function rand_gen(G::GrpAbFinGen)
  S, mS = snf(G)
  return preimage(mS, rand(S))
end

doc"""
***
    rand(G::GrpAbFinGen, B::fmpz) -> GrpAbFinGenElem
    rand(G::GrpAbFinGen, B::Integer) -> GrpAbFinGenElem

> For a (potentially infinite) abelian group $G$, return an element
> chosen uniformly at random with coefficients bounded by B.
"""
rand(G::GrpAbFinGen, B::fmpz) = issnf(G) ? rand_snf(G, B) : rand_gen(G, B)
rand(G::GrpAbFinGen, B::Integer) = issnf(G) ? rand_snf(G, B) : rand_gen(G, B)

function rand_snf(G::GrpAbFinGen, B::fmpz)
  return G([rand(1:(G.snf[i]==0 ? B : min(B, G.snf[i]))) for i in 1:ngens(G)])
end

function rand_snf(G::GrpAbFinGen, B::Integer)
  return rand(G, fmpz(B))
end

function rand_gen(G::GrpAbFinGen, B::fmpz)
  S, mS = snf(G)
  return preimage(mS, rand(S, fmpz(B)))
end

function rand_gen(G::GrpAbFinGen, B::Integer)
  return rand(G, fmpz(B))
end

##############################################################################
#
#  Subgroups
#
##############################################################################

doc"""
***
    sub(G::GrpAbFinGen, s::Array{GrpAbFinGenElem, 1}) -> GrpAbFinGen, Map

> Assume that `s` contains elements of an abelian group $G$. This functions
> returns the subgroup $H$ of $G$ generated by the elements in `s` together
> with the injection $\iota : H \to G$.
"""
function sub(s::Array{GrpAbFinGenElem, 1})
  return sub(parent(s[1]), s)
end

doc"""
***
    sub(G::GrpAbFinGen, s::Array{GrpAbFinGenElem, 1}) -> GrpAbFinGen, Map

> Create the subgroup $H$ of $G$ generated by the elements in `s` together
> with the injection $\iota : H \to G$.
"""
function sub(G::GrpAbFinGen, s::Array{GrpAbFinGenElem, 1})

  if length(s) == 0
    S = GrpAbFinGen(fmpz[1])
    I = MatrixSpace(FlintZZ, ngens(S), ngens(G))()
    m = GrpAbFinGenMap(S, G, I)
    return S, m
  end

  p = s[1].parent
  @assert G == p
  m = MatrixSpace(FlintZZ, length(s)+nrels(p), ngens(p)+length(s))()
  for i=1:length(s)
    for j=1:ngens(p)
      m[i + nrels(p),j] = s[i][j]
    end
    m[i + nrels(p), i+ngens(p)] = 1
  end
  if issnf(p)
    for i=1:ngens(p)
      m[i, i] = p.snf[i]
    end
  else
    for i=1:nrels(p)
      for j=1:ngens(p)
        m[i, j] = p.rels[i,j]
      end
    end
  end
  h = hnf(m)
  fstWithoutOldGens = 1
  for i in rows(h):-1:1, j in ngens(p):-1:1
    if h[i,j] != 0
      fstWithoutOldGens = i+1
      break
    end
  end
  r = sub(h, fstWithoutOldGens:rows(h), ngens(p)+1:cols(h))
  S = AbelianGroup(r)
  return S, GrpAbFinGenMap(S, p, sub(m, nrels(p)+1:rows(h), 1:ngens(p)))
end

################################################################################
#
#  Quotients
#
################################################################################

doc"""
***
  quo(G::GrpAbFinGen, s::Array{GrpAbFinGenElem, 1}) -> GrpAbFinGen, Map

> Create the quotient $H$ of $G$ by the subgroup generated by the elements in
> $s$, together with the projection $p : G \to H$.
"""
function quo(G::GrpAbFinGen, s::Array{GrpAbFinGenElem, 1})
  if length(s) == 0
    I = MatrixSpace(FlintZZ, ngens(G), ngens(G))(1)
    m = GrpAbFinGenMap(G, G, I, I)
    return G, m
  end

  p = s[1].parent
  @assert G == p
  m = MatrixSpace(FlintZZ, length(s)+nrels(p), ngens(p))()
  for i=1:length(s)
    for j=1:ngens(p)
      m[i + nrels(p),j] = s[i][j]
    end
  end
  if issnf(p)
    for i=1:ngens(p)
      m[i, i] = p.snf[i]
    end
  else
    for i=1:nrels(p)
      for j=1:ngens(p)
        m[i, j] = p.rels[i,j]
      end
    end
  end

  Q = AbelianGroup(m)
  I = MatrixSpace(FlintZZ, ngens(p), ngens(p))(1)
  m = GrpAbFinGenMap(p, Q, I, I)
  return Q, m
end

doc"""
***
    quo(G::GrpAbFinGen, n::Integer}) -> GrpAbFinGen, Map
    quo(G::GrpAbFinGen, n::fmpz}) -> GrpAbFinGen, Map

> Returns the quotient $H = G/nG$ together with the projection $p : G \to H$.
"""
quo(G::GrpAbFinGen, n::Union{fmpz, Integer}) = issnf(G) ? quo_snf(G, n) : quo_gen(G, n)

function quo_snf(G::GrpAbFinGen, n::Union{fmpz, Integer})
  r = [gcd(x, n) for x = G.snf]
  I = MatrixSpace(FlintZZ, ngens(G), ngens(G))(1)
  Q = DiagonalGroup(r)
  m = GrpAbFinGenMap(G, Q, I, I)
  return Q, m
end

function quo_gen(G::GrpAbFinGen, n::Union{fmpz, Integer})
  m = vcat(G.rels, MatrixSpace(FlintZZ, ngens(G), ngens(G))(n))
  Q = AbelianGroup(m)
  I = MatrixSpace(FlintZZ, ngens(G), ngens(G))(1)
  m = GrpAbFinGenMap(G, Q, I, I)
  return Q, m
end

############################################################
# iterator
############################################################
function Base.start(G::GrpAbFinGen)
  if order(G) > typemax(UInt)
    error(" Group too large for iterator")
  end
  
  return UInt(0)
end

function Base.next(G::GrpAbFinGen, st::UInt)
  a = _elem_from_enum(G, st)
  return a, st+1
end

function Base.done(G::GrpAbFinGen, st::UInt)
  return st >= order(G)
end

function _elem_from_enum(G::GrpAbFinGen, st::UInt)
  if G.issnf
    el = fmpz[]
    s = fmpz(st)
    for i=1:ngens(G)
      push!(el, s % G.snf[i])
      s = div(s - el[end], G.snf[i])
    end
    return G(el)
  end
    
  S, mS = snf(G)
  return preimage(mS, _elem_from_enum(S, st))
end

Base.length(G::GrpAbFinGen) = UInt(order(G))

############################################################
# trivia
############################################################
doc"""
    gens(G::GrpAbFinGen) -> Array{GrpAbFinGenElem, 1}
> The sequence of generators of $G$
"""
gens(G::GrpAbFinGen) = GrpAbFinGenElem[G[i] for i=1:ngens(G)]


function make_snf{T}(m::Map{GrpAbFinGen, T})
  G = domain(m)
  if G.issnf
    return m
  end
  S, mS = snf(G)
  return m*inv(mS)
end

doc"""
    iscyclic(G::GrpAbFinGen) -> Bool
> Return {{{true}}} if $G$ is cyclic.
"""
function iscyclic(G::GrpAbFinGen)
  if !G.issnf
    G = snf(G)[1]
  end
  return ngens(G) == 1
end

############################################################
# homs from set of generators
############################################################

#TODO: compact printing of group elements
#TODO: should check consistency
doc"""
    hom(A::Array{GrpAbFinGenElem, 1}, B::Array{GrpAbFinGenElem, 1}) -> Map
> Creates the homomorphism $A[i] \mapsto B[i]$
"""
function hom(A::Array{GrpAbFinGenElem, 1}, B::Array{GrpAbFinGenElem, 1}; check::Bool= false)
  GA = parent(A[1])
  GB = parent(B[1])

 if (check)
    m = vcat([x.coeff for x=A])
    m = vcat(m, rels(parent(A[1])))
    T, i = nullspace(m')
    T = T'
    T = sub(T, 1:rows(T), 1:length(A))
    n = vcat([x.coeff for x = B])
    n = T*n
    if !cansolve(parent(B[1]).rels', n')[1]
      error("data does not define a homomorphism")
    end
  end


  M = vcat([hcat(A[i].coeff, B[i].coeff) for i=1:length(A)])
  RA = rels(GA)
  M = vcat(M, hcat(RA, MatrixSpace(FlintZZ, rows(RA), cols(B[1].coeff))()))
  H = hnf(M)
  H = sub(H, 1:ngens(GA), ngens(GA)+1:ngens(GA)+ngens(GB))
  h = GrpAbFinGenMap(GA, GB, H)
  return h
end

doc"""
    hom(G::GrpAbFinGen, B::Array{GrpAbFinGenElem, 1}) -> Map
> Creates the homomorphism $G[i] \mapsto B[i]$
"""
function hom(G::GrpAbFinGen, B::Array{GrpAbFinGenElem, 1})
  GB = parent(B[1])
  M = vcat([B[i].coeff for i=1:length(B)])
  h = GrpAbFinGenMap(G, GB, M)
  return h
end


#TODO: store and reuse on map. Maybe need to change map
function kernel(h::GrpAbFinGenMap)
  G = domain(h)
  H = codomain(h)
  hn, t = hnf_with_transform(vcat(h.map, rels(H))) 
  for i=1:rows(hn)
    if iszero_row(hn, i)
      k = elem_type(G)[]
      for j=i:rows(t)
        push!(k, G(sub(t, j:j, 1:ngens(G))))
      end
      return sub(G, k)
    end
  end
  error("JH")
end

function image(h::GrpAbFinGenMap)
  G = domain(h)
  H = codomain(h)
  hn = hnf(vcat(h.map, rels(H))) 
  im = GrpAbFinGenElem[]
  for i=1:rows(hn)
    if !iszero_row(hn, i)
      push!(im, H(sub(hn, i:i, 1:ngens(H))))
    else
      break
    end
  end
  return sub(H, im)  # too much, this is sub in hnf....
end


################################################################################
#
#  Some special abelian groups
#
################################################################################

# TH: Isn't this the same as UnitsModM.jl?
# TODO: remove this from here. It does not belong here

doc"""
***
    multgrp_of_cyclic_grp(n::fmpz) -> GrpAbFinGen

> Returns the multiplicative group of the cyclic group with $n$ elements.
"""
function multgrp_of_cyclic_grp(n::fmpz)
  composition = Array{fmpz,1}()
  for (p,mp) in factor(n)
    if (p == 2) && (mp >= 2)
      push!(composition,2)
      push!(composition,fmpz(2)^(mp-2))
    else
      push!(composition,(p-1)*p^(mp-1))
    end
  end
  return DiagonalGroup(composition)
end
multgrp_of_cyclic_grp(n::Integer) = multgrp_of_cyclic_grp(fmpz(n))


function issurjective(A::GrpAbFinGenMap)
  return order(codomain(A)) == order(image(A)[1])
end

function isinjective(A::GrpAbFinGenMap)
  return order(kernel(A)[1]) == 1
end

