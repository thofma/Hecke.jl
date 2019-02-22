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
       psylow_subgroup, issubgroup, abelian_groups

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
@doc Markdown.doc"""
***
    AbelianGroup(M::fmpz_mat) -> GrpAbFinGen

> Creates the abelian group with relation matrix `M`. That is, the group will
> have `ncols(M)` generators and each row of `M` describes one relation.
"""
function AbelianGroup(M::fmpz_mat)
  return GrpAbFinGen(M)
end

@doc Markdown.doc"""
***
    AbelianGroup(M::Array{fmpz, 2}) -> GrpAbFinGen

> Creates the abelian group with relation matrix `M`. That is, the group will
> have `ncols(M)` generators and each row of `M` describes one relation.
"""
function AbelianGroup(M::Array{fmpz, 2})
  return AbelianGroup(matrix(FlintZZ, M))
end

@doc Markdown.doc"""
***
    AbelianGroup(M::Array{Integer, 2}) -> GrpAbFinGen

> Creates the abelian group with relation matrix `M`. That is, the group will
> have `ncols(M)` generators and each row of `M` describes one relation.
"""
function AbelianGroup(M::Array{T, 2}) where T <: Integer
  return AbelianGroup(matrix(FlintZZ, M))
end

@doc Markdown.doc"""
***
    AbelianGroup(M::Array{fmpz, 1}) -> GrpAbFinGen

> Creates the abelian group with relation matrix `M`. That is, the group will
> have `length(M)` generators and one relation.
"""
function AbelianGroup(M::Array{fmpz, 1})
  return AbelianGroup(matrix(FlintZZ, 1, length(M), M))
end

@doc Markdown.doc"""
***
    AbelianGroup(M::Array{Integer, 1}) -> GrpAbFinGen

> Creates the abelian group with relation matrix `M`. That is, the group will
> have `length(M)` generators and one relation.
"""
function AbelianGroup(M::Array{T, 1}) where T <: Integer
  return AbelianGroup(matrix(FlintZZ, 1, length(M), M))
end

@doc Markdown.doc"""
***
    DiagonalGroup(M::fmpz_mat) -> GrpAbFinGen

Assuming that $M$ has only one row, this function creates the direct product of
the cyclic groups $\mathbf{Z}/m_i$, where $m_i$ is the $i$th entry of `M`.
"""
function DiagonalGroup(M::fmpz_mat)
  if nrows(M) != 1
    error("The argument must have only one row")
  end

  N = zero_matrix(FlintZZ, ncols(M), ncols(M))
  for i = 1:ncols(M)
    N[i,i] = M[1, i]
  end
  if issnf(N)
    return GrpAbFinGen(fmpz[M[1, i] for i = 1:ncols(M)])
  else
    return GrpAbFinGen(N)
  end
end

@doc Markdown.doc"""
***
    DiagonalGroup(M::Array{Union{fmpz, Integer}, 1}) -> GrpAbFinGen

Creates the direct product of the cyclic groups $\mathbf{Z}/m_i$,
where $m_i$ is the $i$th entry of `M`.
"""
function DiagonalGroup(M::Array{T, 1}) where T <: Union{Integer, fmpz}
  N = zero_matrix(FlintZZ, length(M), length(M))
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
  if get(io, :compact, false)
    print(io, "Abelian group with structure: ")
  else
    print(io, "GrpAb: ")
  end
  show_snf_structure(io, A)
end

function show_snf_structure(io::IO, A::GrpAbFinGen, mul = "x")
  @assert issnf(A)
  len = length(A.snf)
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
      print(io, " $mul ")
    end
    i += j
  end
end

################################################################################
#
#  Field access
#
################################################################################

@doc Markdown.doc"""
***
    issnf(G::GrpAbFinGen) -> Bool

> Returns whether the current relation matrix of the group $G$ is in Smith
> normal form.
"""
issnf(A::GrpAbFinGen) = A.issnf

@doc Markdown.doc"""
***
    ngens(G::GrpAbFinGen) -> Int

> Returns the number of generators of $G$ in the current representation.
"""
function ngens(A::GrpAbFinGen)
  if issnf(A)
    return length(A.snf)
  else
    return ncols(A.rels)
  end
end

@doc Markdown.doc"""
***
    nrels(G::GrpAbFinGen) -> Int

> Returns the number of relations of $G$ in the current representation.
"""
function nrels(A::GrpAbFinGen)
  if issnf(A)
    return length(A.snf)
  else
    return nrows(A.rels)
  end
end

@doc Markdown.doc"""
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
  M = zero_matrix(FlintZZ, ngens(A), ngens(A))
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

@doc Markdown.doc"""
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

  return _reduce_snf(G, S, T, inv(T))
end

# For S in SNF with G.rels = U*S*T and Ti = inv(T) this removes
# the ones at the diagonal of S and contructs the homomorphism.
function _reduce_snf(G::GrpAbFinGen, S::fmpz_mat, T::fmpz_mat, Ti::fmpz_mat)

  d = fmpz[S[i,i] for i = 1:min(nrows(S), ncols(S))]

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
  TT = zero_matrix(FlintZZ, nrows(T), length(s))
  j = 1
  for i = 1:length(d)
    if d[i] != 1
      for k=1:nrows(T)
        TT[k, j] = T[k, i]
      end
      j += 1
    end
  end

  TTi = zero_matrix(FlintZZ, length(s), nrows(T))

  j = 1
  for i = 1:length(d)
    if d[i] != 1
      for k=1:nrows(T)
        TTi[j, k] = Ti[i, k]
      end
      j += 1
    end
  end

  H = GrpAbFinGen(s)
  mp = hom(H, G, TTi, TT, false)
  G.snf_map = mp
  return H, mp::GrpAbFinGenMap
end

################################################################################
#
#  Finiteness
#
################################################################################

@doc Markdown.doc"""
***
    isfinite(A::GrpAbFinGen) -> Bool

> Returns whether $A$ is finite.
"""
isfinite(A::GrpAbFinGen) = issnf(A) ? isfinite_snf(A) : isfinite_gen(A)

isfinite_snf(A::GrpAbFinGen) = length(A.snf) == 0 || !iszero(A.snf[end])

isfinite_gen(A::GrpAbFinGen) = isfinite(snf(A)[1])

@doc Markdown.doc"""
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

@doc Markdown.doc"""
***
    rank(A::GrpAbFinGenGen) -> Int

> Returns the rank of $A$, that is, the dimension of the
> $\mathbf{Q}$-vectorspace $A \otimes_{\mathbf Z} \mathbf Q$.
"""
rank(A::GrpAbFinGen) = issnf(A) ? rank_snf(A) : rank_gen(A)

rank_snf(A::GrpAbFinGen) = length(findall(x -> x == 0, A.snf))

rank_gen(A::GrpAbFinGen) = rank(snf(A)[1])

################################################################################
#
#  Order
#
################################################################################

@doc Markdown.doc"""
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

@doc Markdown.doc"""
***
    exponent(A::GrpAbFinGen) -> fmpz

> Returns the exponent of $A$. It is assumed that $A$ is finite.
"""
exponent(A::GrpAbFinGen) = issnf(A) ? exponent_snf(A) : exponent_gen(A)

function exponent_snf(A::GrpAbFinGen)
  isinfinite(A) && error("Group must be finite")
  ngens(A)==0 && return fmpz(1)
  return A.snf[end]
end

exponent_gen(A::GrpAbFinGen) = exponent(snf(A)[1])

################################################################################
#
#  Trivial
#
################################################################################

@doc Markdown.doc"""
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

@doc Markdown.doc"""
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

@doc Markdown.doc"""
***
    direct_product(G::GrpAbFinGen, H::GrpAbFinGen) -> GrpAbFinGen, GrpAbFinGenMap, GrpAbFinGenMap

> Returns the abelian group $G\times H$ and the injections $G -> G\times \{0\}$, 
  $H -> \{0\} \times H$ .
"""
function direct_product(G::GrpAbFinGen, H::GrpAbFinGen)
  A = vcat(rels(G), zero_matrix(FlintZZ, nrows(rels(H)), ncols(rels(G))))
  B = vcat(zero_matrix(FlintZZ, nrows(rels(G)), ncols(rels(H))), rels(H))
  Dp = AbelianGroup(hcat(A,B))
  m1 = hom(G, Dp, [Dp[i] for i=1:ngens(G)])
  m2 = hom(H, Dp, [Dp[i+ngens(G)] for i = 1:ngens(H)])
  return Dp, m1, m2
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

@doc Markdown.doc"""
***
    sub(G::GrpAbFinGen, s::Array{GrpAbFinGenElem, 1}) -> GrpAbFinGen, Map

> Create the subgroup $H$ of $G$ generated by the elements in `s` together
> with the injection $\iota : H \to G$.
"""
function sub(G::GrpAbFinGen, s::Array{GrpAbFinGenElem, 1},
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)

  if length(s) == 0
    S = GrpAbFinGen(fmpz[1])
    I = zero_matrix(FlintZZ, ngens(S), ngens(G))
    m = hom(S, G, I, false)
    if add_to_lattice
      append!(L, m)
    end
    return S, m
  end

  p = s[1].parent
  @assert G == p
  @assert all(x->x.parent == G, s)
  m = zero_matrix(FlintZZ, length(s) + nrels(p), ngens(p) + length(s))
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
  for i in nrows(h):-1:1, j in ngens(p):-1:1
    if !iszero(h[i,j])
      fstWithoutOldGens = i + 1
      break
    end
  end
  r = sub(h, fstWithoutOldGens:nrows(h), ngens(p) + 1:ncols(h))
  S = AbelianGroup(r)

  mS = hom(S, p, sub(m, (nrels(p) + 1):nrows(h), 1:ngens(p)), false)

  if add_to_lattice
    append!(L, mS)
  end
  return S, mS
end

@doc Markdown.doc"""
***
    sub(s::Array{GrpAbFinGenElem, 1}) -> GrpAbFinGen, Map

> Assuming that the non-empty array `s` contains elements of an abelian group
$G$, this functions returns the subgroup $H$ of $G$ generated by the elements
> in `s` together with the injection $\iota : H \to G$.
"""
function sub(s::Array{GrpAbFinGenElem, 1},
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  length(s) == 0 && error("Array must be non-empty")
  return sub(parent(s[1]), s, add_to_lattice, L)
end

@doc Markdown.doc"""
***
    sub(G::GrpAbFinGen, M::fmpz_mat) -> GrpAbFinGen, Map

> Create the subgroup $H$ of $G$ generated by the elements corresponding to the
> rows of $M$ together with the injection $\iota : H \to G$.
"""
function sub(G::GrpAbFinGen, M::fmpz_mat,
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  m = zero_matrix(FlintZZ, nrows(M) + nrels(G), ngens(G) + nrows(M))
  for i = 1:nrows(M)
    for j = 1:ngens(G)
      m[i + nrels(G), j] = M[i,j]
    end
    m[i + nrels(G), i + ngens(G)] = 1
  end
  if issnf(G)
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

  for i in nrows(h):-1:1, j in ngens(G):-1:1
    if !iszero(h[i,j])
      fstWithoutOldGens = i + 1
      break
    end
  end
  r = sub(h, fstWithoutOldGens:nrows(h), ngens(G) + 1:ncols(h))
  S = AbelianGroup(r)
  mS = hom(S, G, sub(m, (nrels(G) + 1):nrows(h), 1:ngens(G)), false)

  if add_to_lattice
    append!(L, mS)
  end
  return S, mS
end

@doc Markdown.doc"""
***
    sub(G::GrpAbFinGen, n::fmpz) -> GrpAbFinGen, Map

> Create the subgroup $n \cdot G$ of $G$ together
> with the injection $\iota : n\cdot G \to G$.
"""
function sub(G::GrpAbFinGen, n::fmpz,
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  sg = [ n*g for g in gens(G) if !iszero(n*g)]
  return sub(G, sg, add_to_lattice, L)
end

@doc Markdown.doc"""
***
    sub(G::GrpAbFinGen, n::Integer) -> GrpAbFinGen, Map

> Create the subgroup $n \cdot G$ of $G$ together
> with the injection $\iota : n \cdot G \to G$.
"""
function sub(G::GrpAbFinGen, n::Integer,
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  return sub(G, fmpz(n), add_to_lattice, L)
end

################################################################################
#
#  Quotients
#
################################################################################

@doc Markdown.doc"""
***
  quo(G::GrpAbFinGen, s::Array{GrpAbFinGenElem, 1}) -> GrpAbFinGen, Map

> Create the quotient $H$ of $G$ by the subgroup generated by the elements in
> $s$, together with the projection $p : G \to H$.
"""
function quo(G::GrpAbFinGen, s::Array{GrpAbFinGenElem, 1},
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  if length(s) == 0
    I = identity_matrix(FlintZZ, ngens(G))
    m = hom(G, G, I, I, false)
    if add_to_lattice
      append!(L, m)
    end
    return G, m
  end

  p = s[1].parent
  @assert G == p
  m = zero_matrix(FlintZZ, length(s)+nrels(p), ngens(p))
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
  I = identity_matrix(FlintZZ, ngens(p))
  m = hom(p, Q, I, I, false)
  if add_to_lattice
    append!(L, m)
  end
  return Q, m
end

@doc Markdown.doc"""
***
  quo(G::GrpAbFinGen, M::fmpz_mat) -> GrpAbFinGen, Map

> Create the quotient $H$ of $G$ by the subgroup generated by the elements
> corresponding to the rows of $M$. together with the projection $p : G \to H$.
"""
function quo(G::GrpAbFinGen, M::fmpz_mat,
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  m = vcat(rels(G), M)
  Q = AbelianGroup(m)
  I = identity_matrix(FlintZZ, ngens(G))
  m = hom(G, Q, I, I, false)
  if add_to_lattice
    append!(L, m)
  end
  return Q, m
end

@doc Markdown.doc"""
***
    quo(G::GrpAbFinGen, n::Integer}) -> GrpAbFinGen, Map
    quo(G::GrpAbFinGen, n::fmpz}) -> GrpAbFinGen, Map

> Returns the quotient $H = G/nG$ together with the projection $p : G \to H$.
"""
function quo(G::GrpAbFinGen, n::Union{fmpz, Integer},
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  if issnf(G)
    return quo_snf(G, n, add_to_lattice, L)
  else
    quo_gen(G, n, add_to_lattice, L)
  end
end

function quo_snf(G::GrpAbFinGen, n::Union{fmpz, Integer},
                 add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  r = [gcd(x, n) for x = G.snf]
  I = identity_matrix(FlintZZ, ngens(G))
  Q = DiagonalGroup(r)
  m = hom(G, Q, I, I, false)
  if add_to_lattice
    append!(L, m)
  end
  return Q, m
end

function quo_gen(G::GrpAbFinGen, n::Union{fmpz, Integer},
                 add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  m = vcat(G.rels, n*identity_matrix(FlintZZ, ngens(G)))
  Q = AbelianGroup(m)
  I = identity_matrix(FlintZZ, ngens(G))
  m = hom(G, Q, I, I, false)
  if add_to_lattice
    append!(L, m)
  end
  return Q, m
end

################################################################################
#
#  use lattice...
#
################################################################################

function +(G::GrpAbFinGen, H::GrpAbFinGen, L::GrpAbLattice = GroupLattice)
  fl, GH, mG, mH = can_map_into_overstructure(L, G, H)
  if !fl
    error("no common overgroup known")
  end
  return sub(GH, vcat([GH(mG[i, :]) for i=1:nrows(mG)], [GH(mH[i, :]) for i=1:nrows(mH)]))[1]
end

function Base.intersect(G::GrpAbFinGen, H::GrpAbFinGen, L::GrpAbLattice = GroupLattice)
  fl, GH, mG, mH = can_map_into_overstructure(L, G, H)
  if !fl
    error("no common overgroup known")
  end
  #M = [ mG identity_matrix(FlintZZ, nrows(mG)); mH zero_matrix(FlintZZ, nrows(mH), nrows(mG)) ;
        #rels(GH) zero_matrix(FlintZZ, nrels(GH), nrows(mG))]
  M = vcat(vcat(hcat(mG, identity_matrix(FlintZZ, nrows(mG))), hcat(mH, zero_matrix(FlintZZ, nrows(mH), nrows(mG)))), hcat(rels(GH), zero_matrix(FlintZZ, nrels(GH), nrows(mG))))
  h = hnf(M)
  i = nrows(h)
  while i > 0 && iszero(sub(h, i:i, 1:ngens(GH)))
    i -= 1
  end
  return sub(G, [G(sub(h, j:j, ngens(GH)+1:ncols(h))) for j=i+1:nrows(h)])[1]
end

function Base.intersect(A::Array{GrpAbFinGen, 1})
  a = first(A)
  for b = A
    a = intersect(a, b, true)
  end
  return a
end


function Base.issubset(G::GrpAbFinGen, H::GrpAbFinGen, L::GrpAbLattice = GroupLattice)
  fl, GH, mG, mH = can_map_into_overstructure(L, G, H)
  if !fl
    error("no common overgroup known")
  end
  hH = hom(H, GH, mH)
  return all(x -> haspreimage(hH, GH(mG[x, :]))[1], 1:nrows(mG))
end

function issubgroup(G::GrpAbFinGen, H::GrpAbFinGen, L::GrpAbLattice = GroupLattice)
  fl, GH, mG, mH = can_map_into_overstructure(L, G, H)
  if !fl
    error("no common overgroup known")
  end
  hH = hom(H, GH, mH)
  n = matrix(FlintZZ, 0, ngens(H), fmpz[])
  for j=1:nrows(mG)
    fl, x = haspreimage(hH, GH(mG[j, :]))
    if !fl
      return false, hH
    end
    n = vcat(n, x.coeff)
  end
  return true, hom(G, H, n)
end

#cannot define == as this produces problems elsewhere... need some thought
function iseq(G::GrpAbFinGen, H::GrpAbFinGen, L::GrpAbLattice = GroupLattice)
  order(G) == order(H) || return false
  fl, GH, mG, mH = can_map_into_overstructure(L, G, H)
  if !fl
    return false
  end
  return order(G+H) == order(G)
end

function Base.isequal(G::GrpAbFinGen, H::GrpAbFinGen)
  return G === H
end

function quo(G::GrpAbFinGen, U::GrpAbFinGen)
  fl, m = issubgroup(U, G)
  fl || error("not a subgroup")
  return quo(G, m.map)
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
  return compose(mS, m)
end

################################################################################
#
#  Cyclic
#
################################################################################

@doc Markdown.doc"""
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

function psylow_subgroup(G::GrpAbFinGen, p::Union{fmpz, Integer},
                         to_lattice::Bool = true)
  S, mS = snf(G)
  z = _psylow_subgroup_gens(S, p)
  zz = [ image(mS, x) for x in z ]
  return sub(G, zz, to_lattice)
end

################################################################################
#
#  Some special abelian groups
#
################################################################################

# TH: Isn't this the same as UnitsModM.jl?
# TODO: remove this from here. It does not belong here
@doc Markdown.doc"""
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

################################################################################
#
#  Isomorphism to abelian groups
#
################################################################################

@doc Markdown.doc"""
    find_isomorphism(G, op, A::GrpAb) -> Dict, Dict

Given an abelian group $A$ and a collection $G$ which is an abelian group with
the operation `op`, this functions returns isomorphisms $G \to A$ and $A \to G$
encoded as dictionaries.

It is assumed that $G$ and $A$ are isomorphic.
"""
function find_isomorphism(G, op, A::GrpAb)
  H, GtoH, HtoG = find_isomorphism_with_abelian_group(G, op)
  @assert issnf(H)
  Asnf, AsnftoA = snf(A)
  s = length(H.snf)
  id = identity_matrix(FlintZZ, s)
  AsnftoH = hom(Asnf, H, id, id)
  GtoA = Dict{eltype(G), GrpAbFinGenElem}()
  AtoG = Dict{GrpAbFinGenElem, eltype(G)}()
  for g in G
    GtoA[g] = AsnftoA(AsnftoH\(GtoH[g]))
  end
  for a in A
    AtoG[a] = HtoG[AsnftoH(AsnftoA\a)]
  end

  #for g in G
  #  @assert AtoG[GtoA[g]] == g
  #end
  #for a in G
  #  @assert AtoG[GtoA[a]] == a
  #end
  return GtoA, AtoG
end

function find_isomorphism_with_abelian_group(G, op)
  id = find_identity(G, op)
  S = small_generating_set(G, op, id)
  list = push!(copy(S), id)
  n = length(G)
  elem_to_index = Dict{eltype(G), Int}()
  words = Dict{eltype(G), Array{Int}}()
  rels = Vector{Vector{Int}}()

  l = length(list)

  for i in 1:length(S)
    v = zeros(Int, length(S))
    v[i] = 1
    words[S[i]] = v
  end

  words[list[end]] = zeros(Int, length(S))

  for i in 1:length(G)
    elem_to_index[G[i]] = i
  end

  while length(list) != n
    for g in list
      for i in 1:length(S)
        s = S[i]
        m = op(g, s)

        if m in list
          w = words[S[i]] .+ words[g] .- words[m]
          if !iszero(w)
            push!(rels, w)
          end
        end

        if !(m in list)
          push!(list, m)
          words[m] = words[s] .+ words[g]
        end
      end
    end
  end

  rel_mat = zero_matrix(FlintZZ, length(rels), length(S))
  for i in 1:length(rels)
    for j in 1:length(S)
      rel_mat[i, j] = rels[i][j]
    end
  end

  A = AbelianGroup(rel_mat)
  Asnf, mAsnf = snf(A)
  GtoAsnf = Dict{eltype(G), GrpAbFinGenElem}()
  AsnftoG = Dict{GrpAbFinGenElem, eltype(G)}()
  for g in G
    w = words[g]
    GtoAsnf[g] = sum(w[i] * (mAsnf \ A[i]) for i in 1:length(S))
  end
  for a in Asnf
    x = id
    v = Int[mAsnf(a).coeff[1, i] for i in 1:length(S)]
    for i in 1:length(S)
      x = op(x, pow(S[i], op, v[i], id))
    end
    AsnftoG[a] = x
  end

  for g in G
    @assert AsnftoG[GtoAsnf[g]] == g
  end
  for a in Asnf
    @assert GtoAsnf[AsnftoG[a]] == a
  end

  return Asnf, GtoAsnf, AsnftoG
end

function pow(x, op, n, id)
  if n == 0
    return id
  end
  y = x
  for i in 1:(n-1)
    y = op(y, x)
  end
  return y
end

################################################################################
#
#  All abelian groups
#
################################################################################

@doc Markdown.doc"""
    abelian_groups(n::Int) -> Vector{GrpAbFinGen}

Given a positive integer $n$, return a list of all abelian groups of order $n$.
"""
function abelian_groups(n::Int)
  if n == 1
    return [DiagonalGroup(Int[])]
  end
  nn = fmpz(n)
  fac = factor(nn)
  sylow_lists = Vector{Vector{GrpAbFinGen}}()
  for (p, e) in fac
    push!(sylow_lists, GrpAbFinGen[DiagonalGroup(fmpz[p^i for i in reverse(t)]) for t in AllParts(e)])
  end
  C = Base.Iterators.product(sylow_lists...)
  grps = GrpAbFinGen[]
  for c in C
    G = c[1]
    for i in 2:length(fac)
      G = snf(direct_product(G, c[i])[1])[1]
    end
    push!(grps, G)
  end
  return grps
end
