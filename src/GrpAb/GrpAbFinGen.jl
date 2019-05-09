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
       psylow_subgroup, issubgroup, abelian_groups, flat, tensor_product,
       dual, chain_complex, isexact, homology, free_resolution

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
    AbelianGroup(M::fmpz_mat) -> GrpAbFinGen

Creates the abelian group with relation matrix `M`. That is, the group will
have `ncols(M)` generators and each row of `M` describes one relation.
"""
function AbelianGroup(M::fmpz_mat; name :: String = "")
  G = GrpAbFinGen(M)
  if name != ""
    set_name!(G, name)
  end
  return G
end

@doc Markdown.doc"""
    AbelianGroup(M::Array{fmpz, 2}) -> GrpAbFinGen

Creates the abelian group with relation matrix `M`. That is, the group will
have `ncols(M)` generators and each row of `M` describes one relation.
"""
function AbelianGroup(M::Array{fmpz, 2}; name :: String = "")
  G = AbelianGroup(matrix(FlintZZ, M))
  if name != ""
    set_name!(G, name)
  end
  return G
end

@doc Markdown.doc"""
    AbelianGroup(M::Array{Integer, 2}) -> GrpAbFinGen

Creates the abelian group with relation matrix `M`. That is, the group will
have `ncols(M)` generators and each row of `M` describes one relation.
"""
function AbelianGroup(M::Array{T, 2}; name :: String = "") where T <: Integer
  G = AbelianGroup(matrix(FlintZZ, M))
  if name != ""
    set_name!(G, name)
  end
  return G
end

@doc Markdown.doc"""
    AbelianGroup(M::Array{fmpz, 1}) -> GrpAbFinGen

Creates the abelian group with relation matrix `M`. That is, the group will
have `length(M)` generators and one relation.
"""
function AbelianGroup(M::Array{fmpz, 1}; name :: String = "")
  G = AbelianGroup(matrix(FlintZZ, 1, length(M), M))
  if name != ""
    set_name!(G, name)
  end
  return G
end

@doc Markdown.doc"""
    AbelianGroup(M::Array{Integer, 1}) -> GrpAbFinGen

Creates the abelian group with relation matrix `M`. That is, the group will
have `length(M)` generators and one relation.
"""
function AbelianGroup(M::Array{T, 1}; name :: String = "") where T <: Integer
  G = AbelianGroup(matrix(FlintZZ, 1, length(M), M))
  if name != ""
    set_name!(G, name)
  end
  return G
end

@doc Markdown.doc"""
    DiagonalGroup(M::fmpz_mat) -> GrpAbFinGen

Assuming that $M$ has only one row, this function creates the direct product of
the cyclic groups $\mathbf{Z}/m_i$, where $m_i$ is the $i$th entry of `M`.
"""
function DiagonalGroup(M::fmpz_mat; name :: String = "")
  if nrows(M) != 1
    error("The argument must have only one row")
  end

  N = zero_matrix(FlintZZ, ncols(M), ncols(M))
  for i = 1:ncols(M)
    N[i,i] = M[1, i]
  end
  if issnf(N)
    G = GrpAbFinGen(fmpz[M[1, i] for i = 1:ncols(M)])
  else
    G = GrpAbFinGen(N)
  end
  name == "" || set_name!(G, name)
  return G
end

@doc Markdown.doc"""
    DiagonalGroup(M::Array{Union{fmpz, Integer}, 1}) -> GrpAbFinGen

Creates the direct product of the cyclic groups $\mathbf{Z}/m_i$,
where $m_i$ is the $i$th entry of `M`.
"""
function DiagonalGroup(M::Array{T, 1}; name :: String = "") where T <: Union{Integer, fmpz}
  N = zero_matrix(FlintZZ, length(M), length(M))
  for i = 1:length(M)
    N[i,i] = M[i]
  end
  if issnf(N)
    G = GrpAbFinGen(M)
  else
    G = GrpAbFinGen(N)
  end
  name == "" || set_name!(G, name)
  return G
end

################################################################################
#
#  String I/O
#
################################################################################
function show(io::IO, A::GrpAbFinGen)
  @show_name(io, A)
  @show_special(io, A)

  if issnf(A)
    show_snf(io, A)
  else
    show_gen(io, A)
  end
end

function show_hom(io::IO, G::GrpAbFinGen)
  D = get_special(G, :hom)
  D === nothing && error("only for hom")
  print(io, "hom of ")
  print(IOContext(io, :compact => true), D)
end

function show_direct_product(io::IO, G::GrpAbFinGen)
  D = get_special(G, :direct_product)
  D === nothing && error("only for direct products")
  print(io, "direct product of ")
  show(IOContext(io, :compact => true), D)
end

function show_tensor_product(io::IO, G::GrpAbFinGen)
  D = get_special(G, :tensor_product)
  D === nothing && error("only for tensor products")
  print(io, "tensor product of ")
  show(IOContext(io, :compact => true), D)
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
    issnf(G::GrpAbFinGen) -> Bool

Returns whether the current relation matrix of the group $G$ is in Smith
normal form.
"""
issnf(A::GrpAbFinGen) = A.issnf

@doc Markdown.doc"""
    ngens(G::GrpAbFinGen) -> Int

Returns the number of generators of $G$ in the current representation.
"""
function ngens(A::GrpAbFinGen)
  if issnf(A)
    return length(A.snf)
  else
    return ncols(A.rels)
  end
end

@doc Markdown.doc"""
    nrels(G::GrpAbFinGen) -> Int

Returns the number of relations of $G$ in the current representation.
"""
function nrels(A::GrpAbFinGen)
  if issnf(A)
    return length(A.snf)
  else
    return nrows(A.rels)
  end
end

@doc Markdown.doc"""
    rels(A::GrpAbFinGen) -> fmpz_mat

Returns the currently used relations of $G$ as a single matrix.
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
    snf(A::GrpAbFinGen) -> GrpAbFinGen, Map

Returns a pair $(G, f)$, where $G$ is an abelian group in canonical Smith
normal form isomorphic to $G$ and an isomorphism $f : G \to A$.
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
  mp = hom(H, G, TTi, TT, check = false)
  G.snf_map = mp
  return H, mp::GrpAbFinGenMap
end

################################################################################
#
#  Finiteness
#
################################################################################

@doc Markdown.doc"""
    isfinite(A::GrpAbFinGen) -> Bool

Returns whether $A$ is finite.
"""
isfinite(A::GrpAbFinGen) = issnf(A) ? isfinite_snf(A) : isfinite_gen(A)

isfinite_snf(A::GrpAbFinGen) = length(A.snf) == 0 || !iszero(A.snf[end])

isfinite_gen(A::GrpAbFinGen) = isfinite(snf(A)[1])

@doc Markdown.doc"""
    isinfinite(A::GrpAbFinGen) -> Bool

Returns whether $A$ is infinite.
"""
isinfinite(A::GrpAbFinGen) = !isfinite(A)

################################################################################
#
#  Rank
#
################################################################################

@doc Markdown.doc"""
    rank(A::GrpAbFinGenGen) -> Int

Returns the rank of $A$, that is, the dimension of the
$\mathbf{Q}$-vectorspace $A \otimes_{\mathbf Z} \mathbf Q$.
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
    order(A::GrpAbFinGen) -> fmpz

Returns the order of $A$. It is assumed that $A$ is finite.
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
    exponent(A::GrpAbFinGen) -> fmpz

Returns the exponent of $A$. It is assumed that $A$ is finite.
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
    istrivial(A::GrpAbFinGen) -> Bool

Checks if $A$ is the trivial group.
"""
istrivial(A::GrpAbFinGen) = isfinite(A) && order(A) == 1

################################################################################
#
#  Isomorphism
#
################################################################################

@doc Markdown.doc"""
    isisomorphic(G::GrpAbFinGen, H::GrpAbFinGen) -> Bool

Checks if $G$ and $H$ are isomorphic.
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
#TODO: check the universal properties here!!!
@doc Markdown.doc"""
    direct_product(G::GrpAbFinGen...; task::Symbol = :sum) -> GrpAbFinGen, GrpAbFinGenMap, GrpAbFinGenMap

Returns the direct product $D$ of the abelian groups $G_i$. {{{task}}} can be
":sum", ":prod", ":both" or ":none" and determines which canonical maps
are computed as well: ":sum" for the injections, ":prod" for the 
   projections.
"""
function direct_product(G::GrpAbFinGen...
             ; add_to_lattice::Bool = false, L::GrpAbLattice = GroupLattice, task::Symbol = :sum)
  @assert task in [:prod, :sum, :both, :none]

  Dp = AbelianGroup(cat([rels(x) for x = G]..., dims = (1,2)))

  set_special(Dp, :direct_product =>G, :show => show_direct_product)
  inj = []
  pro = []
  j = 0
  for g = G
    if task in [:sum, :both]
      m = hom(g, Dp, GrpAbFinGenElem[Dp[j+i] for i = 1:ngens(g)])
      append!(L, m)
      push!(inj, m)
    end
    if task in [:prod, :both] 
      m = hom(Dp, g, vcat(GrpAbFinGenElem[g[0] for i = 1:j], gens(g), GrpAbFinGenElem[g[0] for i=j+ngens(g)+1:ngens(Dp)]))
      append!(L, m)
      push!(pro, m)
    end
    j += ngens(g)
  end
  if task == :none
    return Dp
  elseif task == :prod
    return Dp, pro
  elseif task == :sum
    return Dp, inj
  else
    return Dp, pro, inj
  end
end

⊕(A::GrpAbFinGen...) = direct_product(A..., task = :none)
export ⊕

@doc Markdown.doc"""
    canonical_injection(G::GrpAbFinGen, i::Int) -> Map
Given a group $G$ that was created as a direct product, return the 
injection from the $i$th component.
"""
function canonical_injection(G::GrpAbFinGen, i::Int)
  D = get_special(G, :direct_product)
  D === nothing && error("1st argument must be a direct product")
  s = sum(ngens(D[j]) for j = 1:i-1)
  h = hom(D[i], G, [G[s+j] for j = 1:ngens(D[i])])
  return h
end

@doc Markdown.doc"""
    canonical_projection(G::GrpAbFinGen, i::Int) -> Map
Given a group $G$ that was created as a direct product, return the 
projection onto the $i$th component.
"""
function canonical_projection(G::GrpAbFinGen, i::Int)
  D = get_special(G, :direct_product)
  D === nothing && error("1st argument must be a direct product")
  H = D[i]
  h = hom(G, H, vcat( [GrpAbFinGenElem[H[0] for j = 1:ngens(D[h])] for h = 1:i-1]...,
                         gens(H),
                      [GrpAbFinGenElem[H[0] for j = 1:ngens(D[h])] for h = i+1:length(D)]...))
  return h
end

function matrix(M::Map{GrpAbFinGen, GrpAbFinGen})
  if typeof(M) == GrpAbFinGenMap
    return M.map
  end
  G = domain(M)
  return vcat([M(g).coeff for g = gens(G)])
end

function matrix(M::Generic.IdentityMap{GrpAbFinGen})
  return identity_matrix(FlintZZ, ngens(domain(M)))
end

@doc Markdown.doc"""
    hom(G::GrpAbFinGen, H::GrpAbFinGen, A::Array{ <: Map{GrpAbFinGen, GrpAbFinGen}, 2}) -> Map
Given groups $G$ and $H$ that are created as direct products as well
as a matrix $A$ containing maps $A[i,j] : G_i \to H_j$, return
the induced homomorphism.
"""
function hom(G::GrpAbFinGen, H::GrpAbFinGen, A::Array{ <: Map{GrpAbFinGen, GrpAbFinGen}, 2})
  r, c = size(A)
  if c == 1
    dG = [G]
  else
    dG = get_special(G, :direct_product)
  end
  if r == 1
    dH = [H]
  else
    dH = get_special(H, :direct_product)
  end
  if dG === nothing || dH === nothing
    error("both groups need to be direct products")
  end
  @assert all(i -> domain(A[i[1], i[2]]) == dG[i[1]] && codomain(A[i[1], i[2]]) == dH[i[2]], Base.Iterators.ProductIterator((1:r, 1:c)))
  h = hom(G, H, vcat([hcat([matrix(A[i,j]) for j=1:c]) for i=1:r]))
  return h    
end

function _flat(G::GrpAbFinGen) 
  s = get_special(G, :direct_product)
  if s === nothing
    return [G]
  end
  return vcat([_flat(x) for x = s]...)
end

function _tensor_flat(G::GrpAbFinGen) 
  s = get_special(G, :tensor_product)
  if s === nothing
    return [G]
  end
  return vcat([_tensor_flat(x) for x = s]...)
end


@doc Markdown.doc"""
    flat(G::GrpAbFinGen) -> GrpAbFinGen, Map
Given a group $G$ that is created using (iterated) direct products, or
(iterated) tensor product, 
return a group that is a flat product: $(A \oplus B) \oplus C$
is returned as $A \oplus B \oplus C$, (resp. $\otimes$) 
together with the  isomorphism.
"""
function flat(G::GrpAbFinGen)
  s = get_special(G, :direct_product)
  if get_special(G, :direct_product) !== nothing
    H = direct_product(_flat(G)..., task = :none)
  elseif get_special(G, :tensor_product) !== nothing
    H = tensor_product(_tensor_flat(G)..., task = :none)
  else
    H = G
  end
  return hom(G, H, identity_matrix(FlintZZ, ngens(G)), identity_matrix(FlintZZ, ngens(G)))
end
######################################################################
# Lift of homomorphisms
######################################################################
#=
  G
  | phi
  V
  F <- H
    psi
 and Im(phi) subset Im(psi), then G -> H can be constructed   
=#

@doc Markdown.doc"""
    lift(phi::Map, psi::Map) -> Map
Given $\phi: G\to F$ and $\psi:H \to F$ s.th. $\Im(\phi) \subseteq \Im(\psi)$
return the map $G\to H$ to make the diagram commute.
"""
function lift(phi::Map, psi::Map)
  x = [haspreimage(psi, image(phi, g)) for g = gens(domain(phi))]
  @assert all(t -> t[1], x)
  return hom(domain(phi), domain(psi), [t[2] for t = x])
end

@doc Markdown.doc"""
    zero_map(G::GrpAbFinGen) -> Map
Create the map $G \to \{0\}$.
"""
function zero_map(G::GrpAbFinGen)
  Z = AbelianGroup([1])
  set_name!(Z, "Zero")
  return hom(G, Z, [Z[0] for i=1:ngens(G)])
end

######################################################################
# complex/ free resolution
######################################################################
function iszero(h::T) where {T <: Map{<:GrpAbFinGen, <:GrpAbFinGen}}
  return all(x -> iszero(h(x)), gens(domain(h)))
end

mutable struct ChainComplex{T}
  @declare_other
  maps::Array{<:Map{<:T, <:T}, 1}
  function ChainComplex(A::S; check::Bool = true) where {S <:Array{<:Map{<:T, <:T}, 1}} where {T}
    if check
      @assert all(i-> iszero(A[i]*A[i+1]), 1:length(A)-1)
    end
    r = new{T}()
    r.maps = A
    return r
  end
end

length(C::ChainComplex) = length(C.maps)
Base.map(C::ChainComplex, i::Int) = C.maps[i]
obj(C::ChainComplex, i::Int) = (i==0 ? domain(C.maps[1]) : codomain(C.maps[i]))

function show(io::IO, C::ChainComplex)
  @show_name(io, C)
  @show_special(io, C)

  Cn = get_special(C, :name)
  if Cn === nothing
    Cn = "C"
  end
  name_mod = String[]
  name_map = String[]
  mis_map = Tuple{Int, <:Map}[]
  mis_mod = Tuple{Int, <:Any}[]
  for i=1:length(C)
    phi = map(C, i)
    if get_special(phi, :name) !== nothing
      push!(name_map, get_special(phi, :name))
    else
      push!(name_map, "")
      push!(mis_map, (i, phi))
    end
  end
  for i=0:length(C)
    M = obj(C, i)
    if get_special(M, :name) !== nothing
      push!(name_mod, get_special(M, :name))
    else
      push!(name_mod, "$(Cn)_$i")
      push!(mis_mod, (i, M))
    end
  end

  io = IOContext(io, :compact => true)
  print(io, name_mod[1])
  for i=1:length(C)
    if name_map[i] != ""
      print(io, " -- $(name_map[i]) --> ", name_mod[i+1])
    else
      print(io, " ----> ", name_mod[i+1])
    end
  end
  if length(mis_mod) > 0 # || length(mis_map) > 0
    print(io, "\nwhere:\n")
    for (i, M) = mis_mod
      print(io, "\t$(Cn)_$i = ", M, "\n")
    end
#    for (i, phi) = mis_map
#      print(io, "\tphi_$i = ", phi, "\n")
#    end
  end
end

@doc Markdown.doc"""
    chain_complex(A::Map{GrpAbFinGen, GrpAbFinGen, <:Any, <:Any}...) -> ChainComplex{GrpAbFinGen}
Given maps $A_i$ s.th. $\Im(A_i) \subseteq \Kern(A_{i+1})$, this creates
the chain complex.
"""
function chain_complex(A::Map{GrpAbFinGen, GrpAbFinGen, <:Any, <:Any}...)
  return ChainComplex(collect(A))
end

function chain_complex(A::Array{<:Map{GrpAbFinGen, GrpAbFinGen, <:Any, <:Any}, 1})
  return ChainComplex(A)
end

lastindex(C::ChainComplex) = length(C)
getindex(C::ChainComplex, u::UnitRange) = ChainComplex(C.maps[u], check = false)

@doc Markdown.doc"""
    isexact(C::ChainComplex) -> Bool
Tests is the complex $A_i: G_i \to G_{i+1}$ 
is exact, ie. if $\Im(A_i) = \Kern(A_{i+1})$.
"""
function isexact(C::ChainComplex)
  return all(i->iseq(image(C.maps[i])[1], kernel(C.maps[i+1])[1]), 1:length(C)-1)
end

@doc Markdown.doc"""
    free_resolution(G::GrpAbFinGen) -> ChainComplex{GrpAbFinGen}
A free resultion for $G$, ie. a chain complex terminating in 
$G \to \{0\}$ that is exact.
"""
function free_resolution(G::GrpAbFinGen)
  A = DiagonalGroup(zeros(FlintZZ, ngens(G)))
  R = rels(G)
  B = DiagonalGroup(zeros(FlintZZ, nrows(R)))
  h_A_G = hom(A, G, gens(G))
  h_B_A = hom(B, A, [A(R[i, :]) for i=1:ngens(B)])
  Z = AbelianGroup(Int[1])
  set_name!(Z, "Zero")
  return chain_complex(hom(Z, B, [B[0]]), h_B_A, h_A_G, hom(G, Z, [Z[0] for i = 1:ngens(G)]))
end

mutable struct ChainComplexMap{T} <: Map{ChainComplex{T}, ChainComplex{T}, HeckeMap, ChainComplexMap}
  header::MapHeader{ChainComplex{T}, ChainComplex{T}}
  maps::Array{<:Map{<:T, <:T}, 1}
  function ChainComplexMap(C::ChainComplex{T}, D::ChainComplex{T}, A::S; check::Bool = !true) where {S <: Array{<:Map{<:T, <:T}, 1}} where {T}
    r = new{T}()
    r.header = MapHeader(C, D)
    r.maps = A
    return r
  end
end

@doc Markdown.doc"""
    hom(C::ChainComplex{T}, D::ChainComplex{T}, phi::Map{<:T, <:T}) where {T} -> ChainComplexMap
Given chain complexes $C_i: G_i \to G_{i+1}$ and $D_i: H_i \to H_{i+1}$
as well as a map $\phi = \phi_n: G_n \to H_n$, lift $\phi$ to
the entire complex: $\phi_i: G_i \to H_i$ s.th. all squares commute.
"""
function hom(C::ChainComplex{T}, D::ChainComplex{T}, phi::Map{<:T, <:T}) where {T}
  @assert length(C) == length(D)
  @assert domain(C.maps[end]) == domain(phi)
  @assert domain(D.maps[end]) == codomain(phi)

  h = [phi]
  for i=length(C)-1:-1:1
    push!(h, lift(C.maps[i]*h[end], D.maps[i]))
  end
  return ChainComplexMap(C, D, reverse(h))
end

@doc Markdown.doc"""
    hom(C::ChainComplex{T}, G::T) -> ChainComplex{T}
Given a complex $A_i: G_i \to G_{i+1}$ and a module $G$,
compute the derived complex $\hom(G_i, G)$.
"""
function hom(C::ChainComplex{GrpAbFinGen}, G::GrpAbFinGen)
  A = GrpAbFinGenMap[]
  H = [hom(domain(C.maps[1]), G)]
  H = vcat(H, [hom(codomain(f), G) for f = C.maps])

  R = GrpAbFinGenMap[]
  for i=1:length(C)
    A = H[i+1][1] # hom(C_i+1, G)
    B = H[i][1]   # hom(C_i  , G)
    #need map from A -> B
    #   C.maps[i] : E -> D
    D = codomain(C.maps[i])
    E = domain(C.maps[i])
    #  H[2][i+1]: A -> Hom(D, G)
    #  H[2][i]  : B -> hom(E, G)
    g = GrpAbFinGenElem[]
    for h = gens(A)
      phi = H[i+1][2](h) # D -> G
      psi = C.maps[i] * phi
      push!(g, preimage(H[i][2], psi))
    end
    push!(R, hom(A, B, g))
  end
  return ChainComplex(reverse(R))
end

@doc Markdown.doc"""
    hom(C::ChainComplex{T}, G::T) -> ChainComplex{T}
Given a complex $A_i: G_i \to G_{i+1}$ and a module $G$,
compute the derived complex $\hom(G, G_i)$.
"""
function hom(G::GrpAbFinGen, C::ChainComplex)
  A = GrpAbFinGenMap[]
  H = [hom(G, domain(C.maps[1]))]
  H = vcat(H, [hom(G, codomain(f)) for f = C.maps])

  R = GrpAbFinGenMap[]
  for i=1:length(C)
    A = H[i+1][1] # hom(G, C_i+1)
    B = H[i][1]   # hom(G, C_i)
    #need map from A -> B
    #   C.maps[i] : E -> D
    D = codomain(C.maps[i])
    E = domain(C.maps[i])
    #  H[2][i+1]: A -> Hom(G, D)
    #  H[2][i]  : B -> hom(G, E)
    g = GrpAbFinGenElem[]
    for h = gens(B)
      phi = H[i][2](h) # G -> E
      psi = phi * C.maps[i] 
      push!(g, preimage(H[i+1][2], psi))
    end
    push!(R, hom(B, A, g))
  end
  return ChainComplex(R)
end

@doc Markdown.doc"""
    homology(C::ChainComplex{GrpAbFinGen}) -> Array{GrpAbFinGen, 1}
Given a complex $A_i: G_i \to G_{i+1}$, 
compute the homology, ie. the modules $H_i = \Kern A_{i+1}/\Im A_i$
"""
function homology(C::ChainComplex{GrpAbFinGen})
  H = GrpAbFinGen[]
  for i=1:length(C)-1
    push!(H, snf(quo(kernel(C.maps[i+1])[1], image(C.maps[i])[1])[1])[1])
  end
  return H
end

function snake_lemma(C::ChainComplex{T}, D::ChainComplex{T}, A::Array{<:Map{T, T}, 1}) where {T}
  @assert length(C) == length(D) == 3
  @assert length(A) == 3
  @assert domain(A[1]) == obj(C,0) && codomain(A[1]) == obj(D, 1)
  @assert domain(A[2]) == obj(C,1) && codomain(A[2]) == obj(D, 2)
  @assert domain(A[3]) == obj(C,2) && codomain(A[3]) == obj(D, 3)

  ka, mka = kernel(A[1])
  kb, mkb = kernel(A[2])
  kc, mkc = kernel(A[3])
  ca, mca = cokernel(A[1])
  cb, mcb = cokernel(A[2])
  cc, mcc = cokernel(A[3])

  res = GrpAbFinGenMap[]
  push!(res, GrpAbFinGenMap(mka * map(C, 1) * inv(mkb)))
  push!(res, GrpAbFinGenMap(mkb * map(C, 2) * inv(mkc)))
  #now the snake
  push!(res, GrpAbFinGenMap(mkc * inv(map(C, 2)) * A[2] * inv(map(D, 2)) * mca))
  #and the boring rest
  push!(res, GrpAbFinGenMap(inv(mca) * map(D, 2) * mcb))
  push!(res, GrpAbFinGenMap(inv(mcb) * map(D, 3) * mcc))
  return chain_complex(res...)
end

################################################################################
#Tensor product
################################################################################

function tensor_product2(G::GrpAbFinGen, H::GrpAbFinGen)
  RG = rels(G)
  RH = rels(H)
  R = vcat(kronecker_product(RG', identity_matrix(FlintZZ, ngens(H)))', 
           kronecker_product(identity_matrix(FlintZZ, ngens(G)), RH')')
  G = AbelianGroup(R)
end

struct TupleParent{T <: Tuple}
  function TupleParent(t::T) where {T}
    return new{T}()
  end
end

function show(io::IO, P::TupleParent{T}) where {T}
  print(io, "parent of tuples of type $T")
end

elem_type(::Type{TupleParent{T}}) where {T} = T
elem_type(::TupleParent{T}) where {T} = T

parent(t::Tuple) = TupleParent(t)

@doc Markdown.doc"""
    tensor_product(G::GrpAbFinGen...; task::Symbol = :map) -> GrpAbFinGen, Map
Given groups $G_i$ compute the tensor product $G_1\otimes \cdots \otimes G_n$.
If {{{task}}} is set to ":map", a map $\phi$ is returned that
maps tuples in $G_1 \times \cdots \times G_n$ to pure tensors
$g_1 \otimes \cdots \otimes g_n$. The map admits a preimage as well.
"""
function tensor_product(G::GrpAbFinGen...; task::Symbol = :map)
  @assert task in [:map, :none]
  local T
  if length(G) == 1
    T = G[1]
  else
    T = tensor_product2(G[2], G[1])
    for i = 3:length(G)
      T = tensor_product2(G[i], T)
    end
  end
  set_special(T, :tensor_product => G, :show => show_tensor_product)
  if task == :none
    return T
  end

  g = vec(collect(Base.Iterators.ProductIterator(Tuple(gens(g) for g = reverse(G)))))

  function pure(g::GrpAbFinGenElem...)
    @assert length(g) == length(G)
    @assert all(i-> parent(g[i]) == G[i], 1:length(G))

    return T(vec(collect(prod(x) for x = Base.Iterators.product([h.coeff for h = reverse(g)]...))))
  end
  function pure(T::Tuple)
    return pure(T...)
  end
  function inv_pure(t::GrpAbFinGenElem)
    p = Base.findall(i -> !iszero(t[i]), 1:ngens(T))
    if length(p) == 0
      return Tuple(collect(g[0] for g = G))
    end
    @assert length(p) == 1
    @assert t[p[1]] == 1
    return reverse(g[p[1]])
  end

  return T, MapFromFunc(pure, inv_pure, TupleParent(Tuple([g[0] for g = G])), T)
end

⊗(G::GrpAbFinGen...) = tensor_product(G..., task = :none)
export ⊗

@doc Markdown.doc"""
    hom(G::GrpAbFinGen, H::GrpAbFinGen, A::Array{ <: Map{GrpAbFinGen, GrpAbFinGen}, 1}) -> Map
Given groups $G = G_1 \otimes \cdots \otimes G_n$ and
$H = H_1 \otimes \cdot \otimes H_n$ as well as maps
$\phi_i: G_i\to H_i$, compute the tensor product of the maps.
"""
function hom(G::GrpAbFinGen, H::GrpAbFinGen, A::Array{ <: Map{GrpAbFinGen, GrpAbFinGen}, 1})
  tG = get_special(G, :tensor_product)
  tG === nothing && error("both groups must be tensor products")
  tH = get_special(H, :tensor_product)
  tH === nothing && error("both groups must be tensor products")
  @assert length(tG) == length(tH) == length(A)
  @assert all(i-> domain(A[i]) == tG[i] && codomain(A[i]) == tH[i], 1:length(A))
  M = matrix(A[1])'
  for i=2:length(A)
    M = kronecker_product(matrix(A[i])', M)
  end
  return hom(G, H, M')
end

@doc Markdown.doc"""
    tensor_product(C::ChainComplex{T}, G::T) -> ChainComplex{T}
Given a complex $A_i: G_i \to G_{i+1}$ and a module $G$,
compute the derived complex $G_i \otimes G$.
"""
function tensor_product(C::ChainComplex, G::GrpAbFinGen)
  A = GrpAbFinGenMap[]
  H = [tensor_product(domain(C.maps[1]), G, task  = :none)]
  H = vcat(H, [tensor_product(codomain(f), G, task = :none) for f = C.maps])

  R = GrpAbFinGenMap[]
  I = identity_map(G)
  for i = 1:length(C)
    push!(R, hom(H[i], H[i+1], [C.maps[i], I]))
  end
  return chain_complex(R)
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
    sub(G::GrpAbFinGen, s::Array{GrpAbFinGenElem, 1}) -> GrpAbFinGen, Map

Create the subgroup $H$ of $G$ generated by the elements in `s` together
with the injection $\iota : H \to G$.
"""
function sub(G::GrpAbFinGen, s::Array{GrpAbFinGenElem, 1},
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)

  if length(s) == 0
    S = GrpAbFinGen(fmpz[1])
    I = zero_matrix(FlintZZ, ngens(S), ngens(G))
    mp = hom(S, G, I, check = false)
    if add_to_lattice
      append!(L, mp)
    end
    return S, mp
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

  mS = hom(S, p, sub(m, (nrels(p) + 1):nrows(h), 1:ngens(p)), check = false)

  if add_to_lattice
    append!(L, mS)
  end
  return S, mS
end

@doc Markdown.doc"""
    sub(s::Array{GrpAbFinGenElem, 1}) -> GrpAbFinGen, Map

Assuming that the non-empty array `s` contains elements of an abelian group
$G$, this functions returns the subgroup $H$ of $G$ generated by the elements
in `s` together with the injection $\iota : H \to G$.
"""
function sub(s::Array{GrpAbFinGenElem, 1},
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  length(s) == 0 && error("Array must be non-empty")
  return sub(parent(s[1]), s, add_to_lattice, L)
end

@doc Markdown.doc"""
    sub(G::GrpAbFinGen, M::fmpz_mat) -> GrpAbFinGen, Map

Create the subgroup $H$ of $G$ generated by the elements corresponding to the
rows of $M$ together with the injection $\iota : H \to G$.
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
  mS = hom(S, G, sub(m, (nrels(G) + 1):nrows(h), 1:ngens(G)), check = false)

  if add_to_lattice
    append!(L, mS)
  end
  return S, mS
end

@doc Markdown.doc"""
    sub(G::GrpAbFinGen, n::fmpz) -> GrpAbFinGen, Map

Create the subgroup $n \cdot G$ of $G$ together
with the injection $\iota : n\cdot G \to G$.
"""
function sub(G::GrpAbFinGen, n::fmpz,
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  sg = [ n*g for g in gens(G) if !iszero(n*g)]
  return sub(G, sg, add_to_lattice, L)
end

@doc Markdown.doc"""
    sub(G::GrpAbFinGen, n::Integer) -> GrpAbFinGen, Map

Create the subgroup $n \cdot G$ of $G$ together
with the injection $\iota : n \cdot G \to G$.
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
  quo(G::GrpAbFinGen, s::Array{GrpAbFinGenElem, 1}) -> GrpAbFinGen, Map

Create the quotient $H$ of $G$ by the subgroup generated by the elements in
$s$, together with the projection $p : G \to H$.
"""
function quo(G::GrpAbFinGen, s::Array{GrpAbFinGenElem, 1},
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  if length(s) == 0
    I = identity_matrix(FlintZZ, ngens(G))
    m = hom(G, G, I, I, check = false)
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
  m = hom(p, Q, I, I, check = false)
  if add_to_lattice
    append!(L, m)
  end
  return Q, m
end

@doc Markdown.doc"""
  quo(G::GrpAbFinGen, M::fmpz_mat) -> GrpAbFinGen, Map

Create the quotient $H$ of $G$ by the subgroup generated by the elements
corresponding to the rows of $M$. together with the projection $p : G \to H$.
"""
function quo(G::GrpAbFinGen, M::fmpz_mat,
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  m = vcat(rels(G), M)
  Q = AbelianGroup(m)
  I = identity_matrix(FlintZZ, ngens(G))
  m = hom(G, Q, I, I, check = false)
  if add_to_lattice
    append!(L, m)
  end
  return Q, m
end

@doc Markdown.doc"""
    quo(G::GrpAbFinGen, n::Integer}) -> GrpAbFinGen, Map
    quo(G::GrpAbFinGen, n::fmpz}) -> GrpAbFinGen, Map

Returns the quotient $H = G/nG$ together with the projection $p : G \to H$.
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
  m = hom(G, Q, I, I, check = false)
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
  m = hom(G, Q, I, I, check = false)
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
  isfinite(G) && (order(G) == order(H) || return false)
  return issubgroup(G, H)[1] && issubgroup(H, G)[1]
  #TODO: this is crap
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

function make_domain_snf(m::Map{GrpAbFinGen, T}) where T
  G = domain(m)
  S, mS = snf(G)
  return mS*m
end

################################################################################
#
#  Cyclic
#
################################################################################

@doc Markdown.doc"""
    iscyclic(G::GrpAbFinGen) -> Bool

Returns whether $G$ is cyclic.
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
    multgrp_of_cyclic_grp(n::fmpz) -> GrpAbFinGen

Returns the multiplicative group of the cyclic group with $n$ elements.
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
      G = snf(direct_product(G, c[i], task = :none))[1]
    end
    push!(grps, G)
  end
  return grps
end

################################################################################
#
#  Identity
#
################################################################################

id(G::GrpAbFinGen) = G(zeros(fmpz, ngens(G)))
