################################################################################
#
#       GrpAb/GrpAbFinGen.jl : Finitely generated abelian groups
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

export AbelianGroup, DiagonalGroup, issnf, ngens, nrels, rels, snf, isfinite,
       isinfinite, rank, order, exponent, istrivial, isisomorphic,
       direct_product, istorsion, torsion_subgroup, sub, quo, iscyclic,
       psylow_subgroup

import Base.+, Nemo.snf, Nemo.parent, Base.rand, Nemo.issnf

################################################################################
#
#  Functions for some abstract interfaces
#
################################################################################

elem_type(G::GrpAbFinGen) = GrpAbFinGenElem

elem_type(::Type{GrpAbFinGen}) = GrpAbFinGenElem

parent_type(::Type{GrpAbFinGenElem}) = GrpAbFinGen

##############################################################################
#
#  Constructors
#
##############################################################################

# We do we have AbelianGroup and DiagonalGroup?
doc"""
***
    AbelianGroup(M::fmpz_mat) -> GrpAbFinGen

> Creates the abelian group with relation matrix `M`. That is, the group will
> have `cols(M)` generators and each row of `M` describes one relation.
"""
function AbelianGroup(M::fmpz_mat)
  return GrpAbFinGen(M)
end

doc"""
***
    AbelianGroup(M::Array{fmpz, 2}) -> GrpAbFinGen

> Creates the abelian group with relation matrix `M`. That is, the group will
> have `cols(M)` generators and each row of `M` describes one relation.
"""
function AbelianGroup(M::Array{fmpz, 2})
  return AbelianGroup(Matrix(FlintZZ, size(M)[1], size(M)[2], M))
end

doc"""
***
    AbelianGroup(M::Array{Integer, 2}) -> GrpAbFinGen

> Creates the abelian group with relation matrix `M`. That is, the group will
> have `cols(M)` generators and each row of `M` describes one relation.
"""
function AbelianGroup(M::Array{T, 2}) where T <: Integer
  return AbelianGroup(Matrix(FlintZZ, size(M)[1], size(M)[2], M))
end

doc"""
***
    AbelianGroup(M::Array{fmpz, 1}) -> GrpAbFinGen

> Creates the abelian group with relation matrix `M`. That is, the group will
> have `length(M)` generators and one relation.
"""
function AbelianGroup(M::Array{fmpz, 1})
  return AbelianGroup(Matrix(FlintZZ, 1, length(M), M))
end

doc"""
***
    AbelianGroup(M::Array{Integer, 1}) -> GrpAbFinGen

> Creates the abelian group with relation matrix `M`. That is, the group will
> have `length(M)` generators and one relation.
"""
function AbelianGroup(M::Array{T, 1}) where T <: Integer
  return AbelianGroup(Matrix(FlintZZ, 1, length(M), M))
end

doc"""
***
    DiagonalGroup(M::fmpz_mat) -> GrpAbFinGen

Assuming that $M$ has only one row, this function creates the direct product of
the cyclic groups $\mathbf{Z}/m_i$, where $m_i$ is the $i$th entry of `M`.
"""
function DiagonalGroup(M::fmpz_mat)
  if rows(M) != 1
    error("The argument must have only one row")
  end

  N = MatrixSpace(FlintZZ, cols(M), cols(M))()
  for i = 1:cols(M)
    N[i,i] = M[1, i]
  end
  if issnf(N)
    return GrpAbFinGen(fmpz[M[1, i] for i = 1:cols(M)])
  else
    return GrpAbFinGen(N)
  end
end

doc"""
***
    DiagonalGroup(M::Array{Union{fmpz, Integer}, 1}) -> GrpAbFinGen

Creates the direct product of the cyclic groups $\mathbf{Z}/m_i$,
where $m_i$ is the $i$th entry of `M`.
"""
function DiagonalGroup(M::Array{T, 1}) where T <: Union{Integer, fmpz}
  N = MatrixSpace(FlintZZ, length(M), length(M))()
  for i = 1:length(M)
    N[i,i] = M[i]
  end
  if issnf(N)
    return GrpAbFinGen(M)
  else
    return GrpAbFinGen(N)
  end
end

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
    println(io, "\nwith structure of ", domain(A.snf_map))
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
  for i = 1:ngens(A)
    M[i,i] = A.snf[i]
  end
  return M
end

################################################################################
#
#  Hermite normal form
#
################################################################################

function assure_has_hnf(A::GrpAbFinGen)
  isdefined(A, :hnf) && return
  A.hnf = hnf(A.rels)
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
    return domain(G.snf_map)::GrpAbFinGen, G.snf_map::GrpAbFinGenMap
  end

  if issnf(G)
    G.snf_map = GrpAbFinGenMap(G) # identity
    return G, G.snf_map::GrpAbFinGenMap
  end

  S, _, T = snf_with_transform(G.rels, false, true)
  d = fmpz[S[i,i] for i = 1:min(rows(S), cols(S))]

  while length(d) < ngens(G)
    push!(d, 0)
  end

  #s = Array{fmpz, 1}()
  s = fmpz[ d[i] for i in 1:length(d) if d[i] !=  1]
  #for i = 1:length(d)
  #  if d[i] != 1
  #    push!(s, d[i])
  #  end
  #end
  TT = MatrixSpace(FlintZZ, rows(T), length(s))()
  j = 1
  for i = 1:length(d)
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
  for i = 1:length(d)
    if d[i] != 1
      for k=1:rows(T)
        TTi[j, k] = Ti[i, k]
      end
      j += 1
    end
  end

  H = GrpAbFinGen(s)
  mp = GrpAbFinGenMap(H, G, TTi, TT)
  G.snf_map = mp
  return H, mp::GrpAbFinGenMap
end

################################################################################
#
#  Finiteness
#
################################################################################

doc"""
***
    isfinite(A::GrpAbFinGen) -> Bool

> Returns whether $A$ is finite.
"""
isfinite(A::GrpAbFinGen) = issnf(A) ? isfinite_snf(A) : isfinite_gen(A)

isfinite_snf(A::GrpAbFinGen) = length(A.snf) == 0 || !iszero(A.snf[end])

isfinite_gen(A::GrpAbFinGen) = isfinite(snf(A)[1])

doc"""
***
    isinfinite(A::GrpAbFinGen) -> Bool

> Returns whether $A$ is infinite.
"""
isinfinite(A::GrpAbFinGen) = !isfinite(A)

################################################################################
#
#  Rank
#
################################################################################

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
#  Order
#
################################################################################

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

################################################################################
#
#  Exponent
#
################################################################################

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

################################################################################
#
#  Trivial
#
################################################################################

doc"""
***
    istrivial(A::GrpAbFinGen) -> Bool

> Checks if $A$ is the trivial group.
"""
istrivial(A::GrpAbFinGen) = isfinite(A) && order(A) == 1

################################################################################
#
#  Isomorphism
#
################################################################################

doc"""
***
    isisomorphic(G::GrpAbFinGen, H::GrpAbFinGen) -> Bool

> Checks if $G$ and $H$ are isomorphic.
"""
function isisomorphic(G::GrpAbFinGen, H::GrpAbFinGen)
  b = filter(x -> x != 1, snf(G)[1].snf) == filter(x -> x != 1, snf(H)[1].snf)
  return b
end

################################################################################
#
#  Direct product
#
################################################################################

doc"""
***
    direct_product(G::GrpAbFinGen, H::GrpAbFinGen) -> GrpAbFinGen

> Returns the abelian group $G\times H$.
"""
function direct_product(G::GrpAbFinGen, H::GrpAbFinGen)
  A = vcat(rels(G), MatrixSpace(FlintZZ, rows(rels(H)), cols(rels(G)))())
  B = vcat(MatrixSpace(FlintZZ, rows(rels(G)), cols(rels(H)))(), rels(H))

  return AbelianGroup(hcat(A,B))
end

################################################################################
#
#  Torsion
#
################################################################################

istorsion(G::GrpAbFinGen) = isfinite(G)

function torsion_subgroup(G::GrpAbFinGen)
  S, mS = snf(G)
  subs = GrpAbFinGenElem[]
  for i in 1:ngens(S)
    if !iszero(S.snf[i])
      push!(subs, mS(S[i]))
    end
  end
  return sub(G, subs)
end

##############################################################################
#
#  Subgroups
#
##############################################################################

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
  m = MatrixSpace(FlintZZ, length(s) + nrels(p), ngens(p) + length(s))()
  for i = 1:length(s)
    for j = 1:ngens(p)
      m[i + nrels(p), j] = s[i][j]
    end
    m[i + nrels(p), i + ngens(p)] = 1
  end
  if issnf(p)
    for i = 1:ngens(p)
      m[i, i] = p.snf[i]
    end
  else
    for i = 1:nrels(p)
      for j = 1:ngens(p)
        m[i, j] = p.rels[i, j]
      end
    end
  end
  h = hnf(m)
  fstWithoutOldGens = 1
  for i in rows(h):-1:1, j in ngens(p):-1:1
    if !iszero(h[i,j])
      fstWithoutOldGens = i + 1
      break
    end
  end
  r = sub(h, fstWithoutOldGens:rows(h), ngens(p) + 1:cols(h))
  S = AbelianGroup(r)
  mS = GrpAbFinGenMap(S, p, sub(m, (nrels(p) + 1):rows(h), 1:ngens(p)))

  #append!(GroupLattice, mS)
  return S, mS
end

doc"""
***
    sub(s::Array{GrpAbFinGenElem, 1}) -> GrpAbFinGen, Map

> Assuming that the non-empty array `s` contains elements of an abelian group
$G$, this functions returns the subgroup $H$ of $G$ generated by the elements
> in `s` together with the injection $\iota : H \to G$.
"""
function sub(s::Array{GrpAbFinGenElem, 1})
  length(s) == 0 && error("Array must be non-empty")
  return sub(parent(s[1]), s)
end

#
#  Subgroup generated by the elements represented by the rows of the matrix
#

function sub(G::GrpAbFinGen, M::fmpz_mat)

  m = MatrixSpace(FlintZZ, rows(M) + nrels(G), ngens(G) + rows(M))()
  for i = 1:rows(M)
    for j = 1:ngens(p)
      m[i + nrels(G), j] = M[i,j]
    end
    m[i + nrels(G), i + ngens(p)] = 1
  end
  if issnf(p)
    for i = 1:ngens(G)
      m[i, i] = G.snf[i]
    end
  else
    for i = 1:nrels(G)
      for j = 1:ngens(G)
        m[i, j] = G.rels[i, j]
      end
    end
  end
  h = hnf(m)
  fstWithoutOldGens = 1
  for i in rows(h):-1:1, j in ngens(G):-1:1
    if !iszero(h[i,j])
      fstWithoutOldGens = i + 1
      break
    end
  end
  r = sub(h, fstWithoutOldGens:rows(h), ngens(G) + 1:cols(h))
  S = AbelianGroup(r)
  mS = GrpAbFinGenMap(S, G, sub(m, (nrels(G) + 1):rows(h), 1:ngens(G)))

  #append!(GroupLattice, mS)
  return S, mS
end

doc"""
***
    sub(G::GrpAbFinGen, n::fmpz) -> GrpAbFinGen, Map

> Create the subgroup $n \cdot G$ of $G$ together
> with the injection $\iota : n\cdot G \to G$.
"""
function sub(G::GrpAbFinGen, n::fmpz)
  sg = [ n*g for g in gens(G) if !iszero(n*g)]
  return sub(G,sg)
end

doc"""
***
    sub(G::GrpAbFinGen, n::fmpz) -> GrpAbFinGen, Map

> Create the subgroup $n \cdot G$ of $G$ together
> with the injection $\iota : n \cdot G \to G$.
"""
sub(G::GrpAbFinGen, n::Integer) = sub(G, fmpz(n))

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
  for i = 1:length(s)
    for j = 1:ngens(p)
      m[i + nrels(p),j] = s[i][j]
    end
  end
  if issnf(p)
    for i = 1:ngens(p)
      m[i, i] = p.snf[i]
    end
  else
    for i = 1:nrels(p)
      for j = 1:ngens(p)
        m[i, j] = p.rels[i, j]
      end
    end
  end

  Q = AbelianGroup(m)
  I = MatrixSpace(FlintZZ, ngens(p), ngens(p))(1)
  m = GrpAbFinGenMap(p, Q, I, I)
  return Q, m
end

#
#  Create the quotient of the group by the subgroup generated by 
#  the elements having coordinates the rows of M
#

function quo(G::GrpAbFinGen, M::fmpz_mat)

  m = vcat(rels(G),M)
  Q = AbelianGroup(m)
  I = MatrixSpace(FlintZZ, ngens(G), ngens(G))(1)
  m = GrpAbFinGenMap(G, Q, I, I)
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

################################################################################
#
#  Make Smith normal form
#
################################################################################

# TODO: This is type unstable
function make_snf(m::Map{GrpAbFinGen, T}) where T
  G = domain(m)
  if issnf(G)
    return m
  end
  S, mS = snf(G)
  return m*mS
end

################################################################################
#
#  Cyclic
#
################################################################################

doc"""
    iscyclic(G::GrpAbFinGen) -> Bool

> Returns whether $G$ is cyclic.
"""
function iscyclic(G::GrpAbFinGen)
  if !issnf(G)
    S = snf(G)[1]
    return ngens(S) == 1
  else
    return ngens(G) == 1
  end
end

################################################################################
#
#  p-Sylow subgroup
#
################################################################################

function _psylow_subgroup_gens(G::GrpAbFinGen, p::Union{fmpz, Integer})
  @assert issnf(G)
  z = GrpAbFinGenElem[]
  for i in 1:ngens(G)
    k, m = remove(G.snf[i], p)
    if k != 0
      push!(z, m*G[i])
    end
  end
  return z
end

function psylow_subgroup(G::GrpAbFinGen, p::Union{fmpz, Integer})
  S, mS = snf(G)
  z = _psylow_subgroup_gens(S, p)
  zz = [ image(mS, x) for x in z ]
  return sub(G, zz)
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
