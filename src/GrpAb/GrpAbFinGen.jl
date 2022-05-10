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

import AbstractAlgebra.GroupsCore: istrivial

export abelian_group, free_abelian_group, is_snf, ngens, nrels, rels, snf, isfinite,
       is_infinite, rank, order, exponent, istrivial, is_isomorphic,
       direct_product, is_torsion, torsion_subgroup, sub, quo, is_cyclic,
       psylow_subgroup, is_subgroup, abelian_groups, flat, tensor_product,
       dual, chain_complex, is_exact, free_resolution, obj, map,
       primary_part, is_free

import Base.+, Nemo.snf, Nemo.parent, Base.rand, Nemo.is_snf

################################################################################
#
#  Functions for some abstract interfaces
#
################################################################################

elem_type(G::GrpAbFinGen) = GrpAbFinGenElem

elem_type(::Type{GrpAbFinGen}) = GrpAbFinGenElem

parent_type(::Type{GrpAbFinGenElem}) = GrpAbFinGen

is_abelian(::GrpAbFinGen) = true

##############################################################################
#
#  Constructors
#
##############################################################################

@doc Markdown.doc"""
    abelian_group(::Type{T} = GrpAbFinGen, M::fmpz_mat) -> GrpAbFinGen

Creates the abelian group with relation matrix `M`. That is, the group will
have `ncols(M)` generators and each row of `M` describes one relation.
"""
abelian_group(M::fmpz_mat; name::String = "") = abelian_group(GrpAbFinGen, M, name=name)

function abelian_group(::Type{GrpAbFinGen}, M::fmpz_mat; name::String = "")
   if is_snf(M) && nrows(M) > 0  && ncols(M) > 0 && !isone(M[1, 1])
    N = fmpz[M[i, i] for i = 1:min(nrows(M), ncols(M))]
    if ncols(M) > nrows(M)
      N = vcat(N, fmpz[0 for i = 1:ncols(M)-nrows(M)])
    end
    G = GrpAbFinGen(N)
  else
    G = GrpAbFinGen(M)
  end
  name == "" || set_name!(G, name)
  return G
end

@doc Markdown.doc"""
    abelian_group(::Type{T} = GrpAbFinGen, M::AbstractMatrix{<:IntegerUnion})

Creates the abelian group with relation matrix `M`. That is, the group will
have `ncols(M)` generators and each row of `M` describes one relation.
"""
function abelian_group(M::AbstractMatrix{<:IntegerUnion}; name::String = "")
  return abelian_group(GrpAbFinGen, M, name=name)
end

function abelian_group(::Type{GrpAbFinGen}, M::AbstractMatrix{<:IntegerUnion}; name::String = "")
  return abelian_group(matrix(FlintZZ, M), name=name)
end

function _issnf(N::Vector{T}) where T <: IntegerUnion
  if isone(length(N)) && isone(N[1])
    return false
  end
  for i = 1:length(N)-1
    if isone(abs(N[i]))
      return false
    end
    if iszero(N[i])
      if !iszero(N[i+1])
        return false
      end
    elseif !iszero(mod(N[i+1], N[i]))
      return false
    end
  end
  return true
end

@doc Markdown.doc"""
    abelian_group(::Type{T} = GrpAbFinGen, M::AbstractVector{<:IntegerUnion}) -> GrpAbFinGen
    abelian_group(::Type{T} = GrpAbFinGen, M::IntegerUnion...) -> GrpAbFinGen

Creates the direct product of the cyclic groups $\mathbf{Z}/m_i$,
where $m_i$ is the $i$th entry of `M`.
"""
function abelian_group(M::AbstractVector{<:IntegerUnion}; name::String = "")
  return abelian_group(GrpAbFinGen, M, name=name)
end

function abelian_group(::Type{GrpAbFinGen}, M::AbstractVector{<:IntegerUnion}; name::String = "")
  if _issnf(M)
    G = GrpAbFinGen(M)
  else
	N = zero_matrix(FlintZZ, length(M), length(M))
    for i = 1:length(M)
      N[i,i] = M[i]
    end
    G = GrpAbFinGen(N)
  end
  if !isempty(M)
    res = lcm(M)
    if !iszero(res)
      G.exponent = res
    end
  end
  name == "" || set_name!(G, name)
  return G
end

function abelian_group(M::IntegerUnion...; name::String = "")
  return abelian_group(collect(M), name=name)
end

@doc Markdown.doc"""
    free_abelian_group(::Type{T} = GrpAbFinGen, n::Int) -> GrpAbFinGen

Creates the free abelian group of rank `n`.
"""
free_abelian_group(n::Int) = free_abelian_group(GrpAbFinGen, n)

function free_abelian_group(::Type{GrpAbFinGen}, n::Int)
  return abelian_group(GrpAbFinGen, zeros(Int, n))
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, A::GrpAbFinGen)
  @show_name(io, A)
  @show_special(io, A)

  if is_snf(A)
    show_snf(io, A)
  else
    show_gen(io, A)
  end
end

function show_hom(io::IO, G)#::GrpAbFinGen)
  D = get_attribute(G, :hom)
  D === nothing && error("only for hom")
  print(io, "hom of ")
  print(IOContext(io, :compact => true), D)
end

function show_direct_product(io::IO, G)#::GrpAbFinGen)
  D = get_attribute(G, :direct_product)
  D === nothing && error("only for direct products")
  print(io, "direct product of ")
  show(IOContext(io, :compact => true), D)
end

function show_direct_sum(io::IO, G)#::GrpAbFinGen)
  D = get_attribute(G, :direct_product)
  D === nothing && error("only for direct sums")
  print(io, "direct sum of ")
  show(IOContext(io, :compact => true), D)
end


function show_tensor_product(io::IO, G)#::GrpAbFinGen)
  D = get_attribute(G, :tensor_product)
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
  @assert is_snf(A)
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
      if j > 1
        print(io, "^($j)")
      end
    else
      if j > 1
        print(io, "(Z/$(inv))^$(j)")
      else
        print(io, "Z/$(inv)")
      end
    end
    if i + j - 1 < len
      print(io, " $mul ")
    end
    i += j
  end
end

################################################################################
#
#  Hash function
#
################################################################################

# We use the default hash, since we use === as == for abelian groups

################################################################################
#
#  Field access
#
################################################################################

@doc Markdown.doc"""
    is_snf(G::GrpAbFinGen) -> Bool

Returns whether the current relation matrix of the group $G$ is in Smith
normal form.
"""
is_snf(A::GrpAbFinGen) = A.is_snf

@doc Markdown.doc"""
    ngens(G::GrpAbFinGen) -> Int

Returns the number of generators of $G$ in the current representation.
"""
function ngens(A::GrpAbFinGen)
  if is_snf(A)
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
  if is_snf(A)
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
  if is_snf(A)
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
  if isdefined(A, :hnf)
    return nothing
  end
  R = rels(A)
  if isdefined(A, :exponent) && nrows(R) >= ncols(R)
    A.hnf = hnf_modular_eldiv(R, A.exponent)
  else
    A.hnf = hnf(R)
  end

  i = nrows(A.hnf)

  while i>0 && is_zero_row(A.hnf, i)
    i -= 1
  end

  if i < nrows(A.hnf)
    A.hnf = A.hnf[1:i, :]
  end

  return nothing
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

  if is_snf(G)
    G.snf_map = GrpAbFinGenMap(G) # identity
    return G, G.snf_map::GrpAbFinGenMap
  end
  if isdefined(G, :exponent)
    if isdefined(G, :hnf)
      S, T = snf_for_groups(G.hnf, G.exponent)
    else
      S, T = snf_for_groups(G.rels, G.exponent)
    end
  else
    S, _, T = snf_with_transform(G.rels, false, true)
  end

  m = min(nrows(S), ncols(S))
  if m > 0 && nrows(S) >= ncols(S)
    e = S[m, m]
    if e > 1
      if fits(Int, e) && is_prime(e)
        F = GF(Int(e), cached = false)
        TF = map_entries(F, T)
        iT = lift(inv(TF))
      else
        iT = invmod(T, e)
      end
    else
      iT = inv(T)
    end
  else
    iT = inv(T)
  end
  return _reduce_snf(G, S, T, iT)
end

# For S in SNF with G.rels = U*S*T and Ti = inv(T) this removes
# the ones at the diagonal of S and constructs the homomorphism.
function _reduce_snf(G::GrpAbFinGen, S::fmpz_mat, T::fmpz_mat, Ti::fmpz_mat)

  d = fmpz[S[i,i] for i = 1:min(nrows(S), ncols(S))]

  while length(d) < ngens(G)
    push!(d, 0)
  end

  pos = Int[i for i = 1:length(d) if !isone(d[i])]
  r = Int[i for i = 1:nrows(T)]
  s = fmpz[ d[i] for i in pos]
  TT = sub(T, r, pos)
  TTi = sub(Ti, pos, r)

  H = GrpAbFinGen(s)
  if !isempty(s) && !iszero(s[end])
    H.exponent = s[end]
    G.exponent = s[end]
  end
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
isfinite(A::GrpAbFinGen) = is_snf(A) ? is_finite_snf(A) : is_finite_gen(A)

is_finite_snf(A::GrpAbFinGen) = length(A.snf) == 0 || !iszero(A.snf[end])

is_finite_gen(A::GrpAbFinGen) = isfinite(snf(A)[1])

@doc Markdown.doc"""
    is_infinite(A::GrpAbFinGen) -> Bool

Returns whether $A$ is infinite.
"""
is_infinite(A::GrpAbFinGen) = !isfinite(A)

################################################################################
#
#  Rank
#
################################################################################

@doc Markdown.doc"""
    rank(A::GrpAbFinGen) -> Int

Returns the rank of $A$, that is, the dimension of the
$\mathbf{Q}$-vectorspace $A \otimes_{\mathbf Z} \mathbf Q$.
"""
rank(A::GrpAbFinGen) = is_snf(A) ? rank_snf(A) : rank_gen(A)

rank_snf(A::GrpAbFinGen) = length(findall(x -> iszero(x), A.snf))

rank_gen(A::GrpAbFinGen) = rank(snf(A)[1])

rank(A::GrpAbFinGen, p::Union{Int, fmpz}) = is_snf(A) ? rank_snf(A, p) : rank_snf(snf(A)[1], p)

function rank_snf(A::GrpAbFinGen, p::Union{Int, fmpz})
  if isempty(A.snf)
    return 0
  end
  if !iszero(mod(A.snf[end], p))
    return 0
  end
  i = findfirst(x -> iszero(mod(x, p)), A.snf)
  return length(A.snf)-i+1
end


################################################################################
#
#  Order
#
################################################################################

@doc Markdown.doc"""
    order(A::GrpAbFinGen) -> fmpz

Returns the order of $A$. It is assumed that $A$ is finite.
"""
order(A::GrpAbFinGen) = is_snf(A) ? order_snf(A) : order_gen(A)

function order_snf(A::GrpAbFinGen)
  is_infinite(A) && error("Group must be finite")
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
function exponent(A::GrpAbFinGen)
  if is_snf(A)
    res = exponent_snf(A)
    if !iszero(res)
      A.exponent = res
    end
    return res
  else
    res = exponent_gen(A)
    if !iszero(res)
      A.exponent = res
    end
    return res
  end
end

function exponent_snf(A::GrpAbFinGen)
  is_infinite(A) && error("Group must be finite")
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
istrivial(A::GrpAbFinGen) = isfinite(A) && isone(order(A))

################################################################################
#
#  Isomorphism
#
################################################################################

@doc Markdown.doc"""
    is_isomorphic(G::GrpAbFinGen, H::GrpAbFinGen) -> Bool

Checks if $G$ and $H$ are isomorphic.
"""
function is_isomorphic(G::GrpAbFinGen, H::GrpAbFinGen)
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
    direct_product(G::GrpAbFinGen...; task::Symbol = :prod) -> GrpAbFinGen, GrpAbFinGenMap, GrpAbFinGenMap

Returns the direct product $D$ of the abelian groups $G_i$. `task` can be
":sum", ":prod", ":both" or ":none" and determines which canonical maps
are computed as well: ":sum" for the injections, ":prod" for the
projections.
"""
function direct_product(G::GrpAbFinGen...  ; task::Symbol = :prod, kwargs...)
  @assert task in [:prod, :sum, :both, :none]
  return _direct_product(:prod, G...; task = task, kwargs...)
end

@doc Markdown.doc"""
    direct_sum(G::GrpAbFinGen...; task::Symbol = :sum) -> GrpAbFinGen, GrpAbFinGenMap, GrpAbFinGenMap

Returns the direct sum $D$ of the abelian groups $G_i$. `task` can be
":sum", ":prod", ":both" or ":none" and determines which canonical maps
are computed as well: ":sum" for the injections, ":prod" for the
projections.
"""
function direct_sum(G::GrpAbFinGen...  ; task::Symbol = :sum, kwargs...)
  @assert task in [:prod, :sum, :both, :none]
  return _direct_product(:sum, G...; task = task, kwargs...)
end

function _direct_product(t::Symbol, G::GrpAbFinGen...
             ; add_to_lattice::Bool = false, L::GrpAbLattice = GroupLattice, task::Symbol = :sum)
  @assert task in [:prod, :sum, :both, :none]

  Dp = abelian_group(cat([rels(x) for x = G]..., dims = (1,2)))
  for x = G
    assure_has_hnf(x)
  end
  #works iff hnf is stripping the zero rows
  Dp.hnf = cat([x.hnf for x = G]..., dims = (1,2))

  if t === :prod
    set_attribute!(Dp, :direct_product =>G, :show => show_direct_product)
  elseif t === :sum
    set_attribute!(Dp, :direct_product =>G, :show => show_direct_sum)
  else
    error("illegal symbol passed in")
  end
  inj = GrpAbFinGenMap[]
  pro = GrpAbFinGenMap[]
  j = 0
  for g = G
    if task in [:sum, :both]
      m = hom(g, Dp, GrpAbFinGenElem[Dp[j+i] for i = 1:ngens(g)], check = false)
      add_to_lattice && append!(L, m)
      push!(inj, m)
    end
    if task in [:prod, :both]
      m = hom(Dp, g, vcat(GrpAbFinGenElem[g[0] for i = 1:j], gens(g), GrpAbFinGenElem[g[0] for i=j+ngens(g)+1:ngens(Dp)]), check = false)
      add_to_lattice && append!(L, m)
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

⊕(A::GrpAbFinGen...) = direct_sum(A..., task = :none)
export ⊕

@doc Markdown.doc"""
    canonical_injection(G::GrpAbFinGen, i::Int) -> Map

Given a group $G$ that was created as a direct product, return the
injection from the $i$th component.
"""
function canonical_injection(G::GrpAbFinGen, i::Int)
  D = get_attribute(G, :direct_product)
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
  D = get_attribute(G, :direct_product)
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
    hom(G::GrpAbFinGen, H::GrpAbFinGen, A::Matrix{ <: Map{GrpAbFinGen, GrpAbFinGen}}) -> Map

Given groups $G$ and $H$ that are created as direct products as well
as a matrix $A$ containing maps $A[i,j] : G_i \to H_j$, return
the induced homomorphism.
"""
function hom(G::GrpAbFinGen, H::GrpAbFinGen, A::Matrix{ <: Map{GrpAbFinGen, GrpAbFinGen}})
  r, c = size(A)
  if c == 1
    dG = [G]
  else
    dG = get_attribute(G, :direct_product)
  end
  if r == 1
    dH = [H]
  else
    dH = get_attribute(H, :direct_product)
  end
  if dG === nothing || dH === nothing
    error("both groups need to be direct products")
  end
  @assert all(i -> domain(A[i[1], i[2]]) == dG[i[1]] && codomain(A[i[1], i[2]]) == dH[i[2]], Base.Iterators.ProductIterator((1:r, 1:c)))
  h = hom(G, H, vcat([hcat([matrix(A[i,j]) for j=1:c]) for i=1:r]))
  return h
end

function _flat(G::GrpAbFinGen)
  s = get_attribute(G, :direct_product)
  if s === nothing
    return [G]
  end
  return vcat([_flat(x) for x = s]...)
end

function _tensor_flat(G::GrpAbFinGen)
  s = get_attribute(G, :tensor_product)
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
  s = get_attribute(G, :direct_product)
  if get_attribute(G, :direct_product) !== nothing
    H = direct_product(_flat(G)..., task = :none)
  elseif get_attribute(G, :tensor_product) !== nothing
    H = tensor_product(_tensor_flat(G)..., task = :none)
  else
    H = G
  end
  return hom(G, H, identity_matrix(FlintZZ, ngens(G)), identity_matrix(FlintZZ, ngens(G)))
end


################################################################################
#Tensor product
################################################################################

function tensor_product2(G::GrpAbFinGen, H::GrpAbFinGen)
  RG = rels(G)
  RH = rels(H)
  R = vcat(transpose(kronecker_product(transpose(RG), identity_matrix(FlintZZ, ngens(H)))),
           transpose(kronecker_product(identity_matrix(FlintZZ, ngens(G)), transpose(RH))))
  G = abelian_group(R)
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

Given groups $G_i$, compute the tensor product $G_1\otimes \cdots \otimes G_n$.
If `task` is set to ":map", a map $\phi$ is returned that
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
  set_attribute!(T, :tensor_product => G, :show => show_tensor_product)
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
    hom(G::GrpAbFinGen, H::GrpAbFinGen, A::Vector{ <: Map{GrpAbFinGen, GrpAbFinGen}}) -> Map

Given groups $G = G_1 \otimes \cdots \otimes G_n$ and
$H = H_1 \otimes \cdot \otimes H_n$ as well as maps
$\phi_i: G_i\to H_i$, compute the tensor product of the maps.
"""
function hom(G::GrpAbFinGen, H::GrpAbFinGen, A::Vector{ <: Map{GrpAbFinGen, GrpAbFinGen}})
  tG = get_attribute(G, :tensor_product)
  tG === nothing && error("both groups must be tensor products")
  tH = get_attribute(H, :tensor_product)
  tH === nothing && error("both groups must be tensor products")
  @assert length(tG) == length(tH) == length(A)
  @assert all(i-> domain(A[i]) == tG[i] && codomain(A[i]) == tH[i], 1:length(A))
  M = transpose(matrix(A[1]))
  for i=2:length(A)
    M = kronecker_product(transpose(matrix(A[i])), M)
  end
  return hom(G, H, transpose(M))
end

################################################################################
#
#  Torsion
#
################################################################################

@doc Markdown.doc"""
    is_torsion(G::GrpAbFinGen) -> Bool

Returns true if and only if `G` is a torsion group.
"""
is_torsion(G::GrpAbFinGen) = isfinite(G)

@doc Markdown.doc"""
    torsion_subgroup(G::GrpAbFinGen) -> GrpAbFinGen, Map

Returns the torsion subgroup of `G`.
"""
function torsion_subgroup(G::GrpAbFinGen, add_to_lattice::Bool = true,
                                          L::GrpAbLattice = GroupLattice)
  S, mS = snf(G)
  subs = GrpAbFinGenElem[]
  for i in 1:ngens(S)
    if !iszero(S.snf[i])
      push!(subs, mS(S[i]))
    end
  end
  return sub(G, subs, add_to_lattice, L)
end

################################################################################
#
#  Is free
#
################################################################################

@doc Markdown.doc"""
    is_free(G::GrpAbFinGen) -> Bool

Returns whether `G` is free or not.
"""
function is_free(G::GrpAbFinGen)
  T, = torsion_subgroup(G, false)
  return isone(order(T))
end

##############################################################################
#
#  Subgroups
#
##############################################################################

@doc Markdown.doc"""
    sub(G::GrpAbFinGen, s::Vector{GrpAbFinGenElem}) -> GrpAbFinGen, Map

Create the subgroup $H$ of $G$ generated by the elements in `s` together
with the injection $\iota : H \to G$.
"""
function sub(G::GrpAbFinGen, s::Vector{GrpAbFinGenElem},
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
  if is_snf(p)
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
  if isdefined(G, :exponent)
    h = hnf_modular_eldiv(m, G.exponent)
  else
    h = hnf(m)
  end
  fstWithoutOldGens = 1
  for i in nrows(h):-1:1, j in ngens(p):-1:1
    if !iszero(h[i,j])
      fstWithoutOldGens = i + 1
      break
    end
  end
  r = view(h, fstWithoutOldGens:nrows(h), ngens(p) + 1:ncols(h))
  S = abelian_group(r)
  if isdefined(G, :exponent)
    S.exponent = G.exponent
  end
  mS = hom(S, p, view(m, (nrels(p) + 1):nrows(h), 1:ngens(p)), check = false)

  if add_to_lattice
    append!(L, mS)
  end
  return S, mS
end

@doc Markdown.doc"""
    sub(s::Vector{GrpAbFinGenElem}) -> GrpAbFinGen, Map

Assuming that the non-empty array `s` contains elements of an abelian group
$G$, this functions returns the subgroup $H$ of $G$ generated by the elements
in `s` together with the injection $\iota : H \to G$.
"""
function sub(s::Vector{GrpAbFinGenElem},
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
  if is_snf(G)
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

  if isdefined(G, :exponent) && !iszero(G.exponent)
    h = hnf_modular_eldiv(m, G.exponent)
  else
    h = hnf(m)
  end
  fstWithoutOldGens = 1

  for i in nrows(h):-1:1, j in ngens(G):-1:1
    if !iszero(h[i,j])
      fstWithoutOldGens = i + 1
      break
    end
  end
  r = view(h, fstWithoutOldGens:nrows(h), ngens(G) + 1:ncols(h))
  S = abelian_group(r)
  mS = hom(S, G, view(m, (nrels(G) + 1):nrows(h), 1:ngens(G)), check = false)
  if isdefined(G, :exponent)
    S.exponent = G.exponent
  end
  if add_to_lattice
    append!(L, mS)
  end
  return S, mS
end

function _sub_integer_snf(G::GrpAbFinGen, n::fmpz, add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  ind = 1
  while ind <= ngens(G) && gcd(n, G.snf[ind]) == G.snf[ind]
    ind += 1
  end
  if ind == ngens(G) && gcd(n, G.snf[ind]) == G.snf[ind]
    Gnew = GrpAbFinGenElem(Int[])
    mp = hom(Gnew, G, GrpAbFinGenElem[])
    if add_to_lattice
      append!(L, mp)
    end
    return Gnew, mp
  end
  invariants = Vector{fmpz}(undef, ngens(G)-ind+1)
  for_map = Vector{fmpz}(undef, ngens(G)-ind+1)
  for i = ind:length(G.snf)
    if iszero(G.snf[i])
      invariants[i-ind+1] = 0
    else
      res = gcd(n, G.snf[i])
      invariants[i-ind+1] = divexact(G.snf[i], res)
    end
  end
  Gnew = abelian_group(invariants)
  mat_map = zero_matrix(FlintZZ, length(invariants), ngens(G))
  for i = 1:ngens(Gnew)
    mat_map[i, ind+i-1] = n
  end
  if isdefined(G, :exponent)
    Gnew.exponent = G.exponent
  end
  mp = hom(Gnew, G, mat_map)
  if add_to_lattice
    append!(L, mp)
  end
  return Gnew, mp
end

@doc Markdown.doc"""
    sub(G::GrpAbFinGen, n::fmpz) -> GrpAbFinGen, Map

Create the subgroup $n \cdot G$ of $G$ together
with the injection $\iota : n\cdot G \to G$.
"""
function sub(G::GrpAbFinGen, n::fmpz,
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  if is_snf(G)
    return _sub_integer_snf(G, n, add_to_lattice, L)
  end
  H, mH = sub(G, scalar_matrix(FlintZZ, ngens(G), deepcopy(n)), add_to_lattice, L)
  if isdefined(G, :exponent)
    res = divexact(G.exponent, gcd(n, G.exponent))
    if !iszero(res)
      H.exponent = res
    end
  end
  return H, mH
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
    quo(G::GrpAbFinGen, s::Vector{GrpAbFinGenElem}) -> GrpAbFinGen, Map

Create the quotient $H$ of $G$ by the subgroup generated by the elements in
$s$, together with the projection $p : G \to H$.
"""
function quo(G::GrpAbFinGen, s::Vector{GrpAbFinGenElem},
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
  if is_snf(p)
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

  Q = abelian_group(m)
  if isdefined(G, :exponent)
    Q.exponent = G.exponent
  end
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
corresponding to the rows of $M$, together with the projection $p : G \to H$.
"""
function quo(G::GrpAbFinGen, M::fmpz_mat,
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  m = vcat(rels(G), M)
  Q = abelian_group(m)
  if isdefined(G, :exponent)
    Q.exponent = G.exponent
  end
  I = identity_matrix(FlintZZ, ngens(G))
  m = hom(G, Q, I, I, check = false)
  if add_to_lattice
    append!(L, m)
  end
  return Q, m
end

function quo(G::GrpAbFinGen, f::GrpAbFinGenMap,
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  M = f.map
  return quo(G, M, add_to_lattice, L)
end

@doc Markdown.doc"""
    quo(G::GrpAbFinGen, n::Integer}) -> GrpAbFinGen, Map
    quo(G::GrpAbFinGen, n::fmpz}) -> GrpAbFinGen, Map

Returns the quotient $H = G/nG$ together with the projection $p : G \to H$.
"""
function quo(G::GrpAbFinGen, n::IntegerUnion,
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  if is_snf(G)
    return quo_snf(G, n, add_to_lattice, L)
  else
    return quo_gen(G, n, add_to_lattice, L)
  end
end

function quo_snf(G::GrpAbFinGen, n::IntegerUnion,
                 add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  r = [gcd(x, n) for x = G.snf]
  I = identity_matrix(FlintZZ, ngens(G))
  Q = abelian_group(r)
  if isdefined(G, :exponent)
    Q.exponent = gcd(G.exponent, n)
  else
    Q.exponent = n
  end
  m = hom(G, Q, I, I, check = false)
  if add_to_lattice
    append!(L, m)
  end
  return Q, m
end

function quo_gen(G::GrpAbFinGen, n::IntegerUnion,
                 add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  m = vcat(G.rels, n*identity_matrix(FlintZZ, ngens(G)))
  Q = abelian_group(m)
  if isdefined(G, :exponent)
    Q.exponent = gcd(n, G.exponent)
  end
  I = identity_matrix(FlintZZ, ngens(G))
  m = hom(G, Q, I, I, check = false)
  if add_to_lattice
    append!(L, m)
  end
  return Q, m
end

################################################################################
#
#  Intersection
#
################################################################################

@doc Markdown.doc"""
    intersect(mG::GrpAbFinGenMap, mH::GrpAbFinGenMap) -> GrpAbFinGen, Map

Given two injective maps of abelian groups with the same codomain $G$,
return the intersection of the images as a subgroup of $G$.
"""
function Base.intersect(mG::GrpAbFinGenMap, mH::GrpAbFinGenMap,
                                            add_to_lattice::Bool = true,
                                            L::GrpAbLattice = GroupLattice)
  G = domain(mG)
  GH = codomain(mG)
  @assert GH == codomain(mH)
  M = zero_matrix(FlintZZ, nrows(mG.map)+ nrows(mH.map) + nrels(GH), ncols(mG.map)+ nrows(mG.map))
  _copy_matrix_into_matrix(M, 1, 1, mG.map)
  for i = 1:nrows(mG.map)
    M[i, i+ncols(mG.map)] = 1
  end
  _copy_matrix_into_matrix(M, nrows(mG.map)+1, 1, mH.map)
  if isdefined(GH, :hnf)
    _copy_matrix_into_matrix(M, nrows(mG.map)+ nrows(mH.map)+1, 1, GH.hnf)
  else
    _copy_matrix_into_matrix(M, nrows(mG.map)+ nrows(mH.map)+1, 1, rels(GH))
  end
  #=
  M2 = hcat(mG.map, identity_matrix(FlintZZ, nrows(mG.map)))
  M3 = vcat(vcat(M2, hcat(mH.map, zero_matrix(FlintZZ, nrows(mH.map), nrows(mG.map)))), hcat(rels(GH), zero_matrix(FlintZZ, nrels(GH), nrows(mG.map))))
  @assert M3 == M
  =#
  h = hnf!(M)
  i = nrows(h)
  while i > 0 && iszero(sub(h, i:i, 1:ngens(GH)))
    i -= 1
  end
   return sub(GH, [mG(GrpAbFinGenElem(G, view(h, j:j, ngens(GH)+1:ncols(h)))) for j=i+1:nrows(h)], add_to_lattice, L)
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

function Base.intersect(A::Vector{GrpAbFinGen})
  a = first(A)
  for b = A
    a = intersect(a, b, true)
  end
  return a
end

@doc Markdown.doc"""
  issubset(G::GrpAbFinGen, H::GrpAbFinGen) -> Bool

Return true if G is contained in H, false otherwise.
"""
function Base.issubset(G::GrpAbFinGen, H::GrpAbFinGen, L::GrpAbLattice = GroupLattice)
  fl, GH, mG, mH = can_map_into_overstructure(L, G, H)
  if !fl
    error("no common overgroup known")
  end
  hH = hom(H, GH, mH)
  hG = hom(G, GH, mG)
  return _issubset(hG, hH)
end

#checks if the image of mH is contained in the image of mG
function _issubset(mH::GrpAbFinGenMap, mG::GrpAbFinGenMap)
  k, mk = cokernel(mG, false)
  return iszero(mH*mk)
end

function is_subgroup(G::GrpAbFinGen, H::GrpAbFinGen, L::GrpAbLattice = GroupLattice)
  fl, GH, mG, mH = can_map_into_overstructure(L, G, H)
  if !fl
    error("no common overgroup known")
  end
  hH = hom(H, GH, mH)
  els = [GrpAbFinGenElem(GH, mG[j, :]) for j = 1:nrows(mG)]
  fl, imgs = haspreimage(hH, els)
  if !fl
    return false, hH
  else
    return true, hom(G, H, imgs, check = false)
  end
end

#checks if the image of mG contains the image of mH


#cannot define == as this produces problems elsewhere... need some thought
function is_eq(G::GrpAbFinGen, H::GrpAbFinGen, L::GrpAbLattice = GroupLattice)
  isfinite(G) && (order(G) == order(H) || return false)
  return is_subgroup(G, H)[1] && is_subgroup(H, G)[1]
end

function Base.isequal(G::GrpAbFinGen, H::GrpAbFinGen)
  return G === H
end

@doc Markdown.doc"""
    quo(G::GrpAbFinGen, U::GrpAbFinGen) -> GrpAbFinGen, Map

Create the quotient $H$ of $G$ by $U$, together with the projection
$p : G \to H$.
"""
function quo(G::GrpAbFinGen, U::GrpAbFinGen)
  fl, m = is_subgroup(U, G)
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
    is_cyclic(G::GrpAbFinGen) -> Bool

Returns whether $G$ is cyclic.
"""
function is_cyclic(G::GrpAbFinGen)
  if !is_snf(G)
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

function _psylow_subgroup_gens(G::GrpAbFinGen, p::IntegerUnion)
  @assert is_snf(G)
  z = GrpAbFinGenElem[]
  for i in 1:ngens(G)
    k, m = remove(G.snf[i], p)
    if k != 0
      push!(z, m*G[i])
    end
  end
  return z
end

@doc Markdown.doc"""
    psylow_subgroup(G::GrpAbFinGen, p::IntegerUnion) -> GrpAbFinGen, Map

Returns the $p$-Sylow subgroup of `G`.
"""
function psylow_subgroup(G::GrpAbFinGen, p::IntegerUnion,
                         to_lattice::Bool = true)
  @req is_prime(p) "Number ($p) must be prime"
  S, mS = snf(G)
  z = _psylow_subgroup_gens(S, p)
  zz = [ image(mS, x) for x in z ]
  return sub(G, zz, to_lattice)
end

@doc Markdown.doc"""
    primary_part(G::GrpAbFinGen, m::IntegerUnion) -> GrpAbFinGen, Map

Returns the $m$-primary part of `G`.
"""
function primary_part(G::GrpAbFinGen, m::IntegerUnion,
                      to_lattice::Bool = true)
  S, mS = snf(G)
  zz = elem_type(G)[]
  for (p, _) in factor(m)
    z = _psylow_subgroup_gens(S, p)
    append!(zz, (image(mS, x) for x in z))
  end
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
  composition = Vector{fmpz}()
  for (p,mp) in factor(n)
    if (p == 2) && (mp >= 2)
      push!(composition,2)
      push!(composition,fmpz(2)^(mp-2))
    else
      push!(composition,(p-1)*p^(mp-1))
    end
  end
  return abelian_group(composition)
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
  @assert is_snf(H)
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

function find_isomorphism_with_abelian_group(G::Vector{NfToNfMor})
	id = id_hom(domain(G[1]))
	S = small_generating_set(G)
  p = 2
  R = GF(p, cached = false)
  K = domain(G[1])
  Rx = PolynomialRing(R, "x", cached = false)[1]
  while iszero(discriminant(Rx(K.pol)))
    p = next_prime(p)
		R = GF(p, cached = false)
	  Rx = PolynomialRing(R, "x", cached = false)[1]
	end
  list = gfp_poly[Rx(x.prim_img) for x in S]
  push!(list, gen(Rx))
  n = length(G)
  elem_to_index = Dict{NfToNfMor, Int}()
  words = Dict{gfp_poly, Array{Int}}()
  rels = Vector{Vector{Int}}()

  l = length(list)

  for i in 1:length(S)
    v = zeros(Int, length(S))
    v[i] = 1
    words[Rx(S[i].prim_img)] = v
  end

  words[list[end]] = zeros(Int, length(S))

  for i in 1:length(G)
    elem_to_index[G[i]] = i
  end

  first_round = true # One has to do this once even if length(list) == n
  while first_round || length(list) != n
    first_round = false
    for g in list
      for i in 1:length(S)
        s = S[i]
 				sRx = Rx(s.prim_img)
        m = compose_mod(g, sRx, Rx(K.pol))

        if m in list
          w = words[sRx] .+ words[g] .- words[m]
          if !iszero(w)
            push!(rels, w)
          end
        end

        if !(m in list)
          push!(list, m)
          words[m] = words[sRx] .+ words[g]
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

  A = abelian_group(rel_mat)
  Asnf, mAsnf = snf(A)
  GtoAsnf = Dict{eltype(G), GrpAbFinGenElem}()
  AsnftoG = Dict{GrpAbFinGenElem, eltype(G)}()
  for g in G
    w = words[Rx(g.prim_img)]
    GtoAsnf[g] = sum(w[i] * (mAsnf \ A[i]) for i in 1:length(S))
  end
  for a in Asnf
    el = gen(Rx)
    v = Int[mAsnf(a).coeff[1, i] for i in 1:length(S)]
    for i in 1:length(S)
      el = compose_mod(el, pow(Rx(S[i].prim_img), (x, y) -> Hecke.compose_mod(x, y, Rx(K.pol)), v[i], gen(Rx)), Rx(K.pol))
    end
		ind = findfirst(x -> Rx(x.prim_img) == el, G)
		@assert ind != nothing
    AsnftoG[a] = G[ind]
  end

  for g in G
    @assert AsnftoG[GtoAsnf[g]] == g
  end
  for a in Asnf
    @assert GtoAsnf[AsnftoG[a]] == a
  end

  return Asnf, GtoAsnf, AsnftoG
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

  first_round = true # One has to do this once even if length(list) == n
  while first_round || length(list) != n
    first_round = false
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

  A = abelian_group(rel_mat)
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
    return GrpAbFinGen[abelian_group(Int[])]
  end
  nn = fmpz(n)
  fac = factor(nn)
  sylow_lists = Vector{Vector{GrpAbFinGen}}()
  for (p, e) in fac
    push!(sylow_lists, GrpAbFinGen[abelian_group(fmpz[p^i for i in reverse(t)]) for t in AllParts(e)])
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
#  Sum of maps
#
################################################################################

function +(f::GrpAbFinGenMap, g::GrpAbFinGenMap)
  @assert domain(f) == domain(g)
  @assert codomain(f) == codomain(g)
  return hom(domain(f), codomain(g), GrpAbFinGenElem[f(x)+g(x) for x in gens(domain(f))])
end

function -(f::GrpAbFinGenMap, g::GrpAbFinGenMap)
  @assert domain(f) == domain(g)
  @assert codomain(f) == codomain(g)
  return hom(domain(f), codomain(g), GrpAbFinGenElem[f(x)-g(x) for x in gens(domain(f))])
end


################################################################################
#
#  Functions related to the action of a group of endomorphisms
#
################################################################################

function induce_action_on_subgroup(mS::GrpAbFinGenMap, acts::Vector{GrpAbFinGenMap})
  res = Vector{GrpAbFinGenMap}(undef, length(acts))
  S = domain(mS)
  for i = 1:length(acts)
    imgs = Vector{GrpAbFinGenElem}(undef, ngens(S))
    for j = 1:length(imgs)
      imgs[j] = mS\(acts[i](mS(S[j])))
    end
    res[i] = hom(S, S, imgs)
  end
  return res
end

function fixed_subgroup(f::GrpAbFinGenMap, to_lattice::Bool = true)
  @assert domain(f) == codomain(f)
  return kernel(f - id_hom(domain(f)), to_lattice)
end

function is_fixed_point_free(act::Vector{GrpAbFinGenMap})
  G = domain(act[1])
   intersection_of_kernels = id_hom(G)
  minus_id = hom(G, G, GrpAbFinGenElem[-x for x in gens(G)])
  for i = 1:length(act)
   k, mk = fixed_subgroup(act[i], false)
    kk, intersection_of_kernels = intersect(intersection_of_kernels, mk, false)
    if isone(order(kk))
      return true
    end
  end
  return false
end

################################################################################
#
#  Elementary divisors
#
################################################################################

@doc Markdown.doc"""
    elementary_divisors(G::GrpAbFinGen) -> Vector{fmpz}

Given $G$, returns the elementary divisors of $G$, that is, the unique positive
integers $e_1,\dotsc,e_k$ with $e_i \mid e_{i + 1}$ and
$G \cong \mathbf{Z}/e_1\mathbf{Z} \times \dotsb \times \mathbf{Z}/e_k\mathbf{Z}$.
"""
function elementary_divisors(G::GrpAbFinGen)
  if is_snf(G)
    return copy(G.snf)
  else
    return elementary_divisors(snf(G)[1])
  end
end

################################################################################
#
#  Has quotient
#
################################################################################

@doc Markdown.doc"""
    has_quotient(G::GrpAbFinGen, invariant::Vector{Int}) -> Bool

Given an abelian group $G$, returns true if it has a quotient with given elementary
divisors and false otherwise.
"""
function has_quotient(G::GrpAbFinGen, invariants::Vector{Int})
  H = abelian_group(invariants)
  H = snf(H)[1]
  G1 = snf(G)[1]
  arr_snfG1 = filter(x -> x != 1, G1.snf)
  arr_snfH = filter(x -> x != 1, H.snf)
  if length(arr_snfG1) < length(arr_snfH)
    return false
  end
  for i = 0:length(arr_snfH)-1
    if !divisible(arr_snfG1[end-i], arr_snfH[end-i])
      return false
    end
  end
  return true
end

################################################################################
#
#  Find complement
#
################################################################################

#TODO: a better algorithm?
@doc Markdown.doc"""
    has_complement(f::GrpAbFinGenMap) -> Bool, GrpAbFinGenMap

Given a map representing a subgroup of a group $G$, returns either true and
an injection of a complement in $G$, or false.
"""
function has_complement(m::GrpAbFinGenMap)
  G = codomain(m)
  if !isfinite(G)
    error("Not yet implemented")
  end
  H, mH = cokernel(m, false)
  SH, mSH = snf(H)
  mH = mH*inv(mSH)
  s, ms = snf(domain(m))
  m1 = ms*m
  gens_complement = GrpAbFinGenElem[]
  for i = 1:ngens(SH)
    igSH = mH\SH[i]
    test_el = SH.snf[i]*igSH
    if iszero(test_el)
      push!(gens_complement, igSH)
      continue
    end
    #I search for an element y in s such that SH.snf[i]*y = SH.snf[i]*igSH
    #If I can't find this, the complement does not exists, otherwise we push in the list
    #of generators igSH-s
    S1, mS1 = sub(s, SH.snf[i], false)
    fl, el = haspreimage(mS1*m1, test_el)
    if !fl
      return false, sub(G, GrpAbFinGenElem[])[2]
    end
    el1 = mS1(el)
    coeffs = zero_matrix(FlintZZ, 1, ngens(s))
    for j = 1:ngens(s)
      if !iszero(el1[j])
        R = ResidueRing(FlintZZ, s.snf[j], cached = false)
        r1 = R(el1[j])
				r2 = R(SH.snf[i])
				fl1, r = divides(r1, r2)
				@assert fl1
        coeffs[1, j] = lift(r)
      end
    end
    el_sub = GrpAbFinGenElem(s, coeffs)
    push!(gens_complement, igSH - m1(el_sub))
  end
  res, mres = sub(G, gens_complement, false)
  @assert order(res)*order(s) == order(G)
  return true, mres
end

################################################################################
#
#  Identity
#
################################################################################

id(G::GrpAbFinGen) = G(zeros(fmpz, ngens(G)))

################################################################################
#
#  Diagonalize a subgroup
#
################################################################################


#Given a subgroup H of a group G, I want to find generators $g_1, dots, g_s$ of
#G such that H = \sum H \cap <g_i> and the relation matrix of $G$ is diagonal.
function is_diagonalisable(mH::GrpAbFinGenMap)

  H = domain(mH)
  G = codomain(mH)
  SH, mSH = snf(H)
  SG, mSG = snf(G)
  if ngens(SH) == 0
    gg =  GrpAbFinGenElem[mSG(SG[i]) for i = 1:ngens(SG)]
    @assert all(x -> parent(x) == G, gg)
    return true, gg
  end
  mH1 = mSH * mH * inv(mSG)
  H1 = domain(mH1)
  G1 = codomain(mH1)
  el = mH1(H1[ngens(H1)])
  pk = gcd(fmpz[el[i] for i = 1:ngens(G1)])
  pk = gcd(pk, exponent(G1))
  e = G1[0]
  for i = 1:ngens(G1)
    e += divexact(el[i], pk)*G1[i]
  end
  sel, msel = sub(G1, GrpAbFinGenElem[e])
  fl, mk = has_complement(msel)
  if !fl
    return false, gens(G)
  end
  sH, msH = sub(G1, GrpAbFinGenElem[mH1(H1[i]) for i = 1:ngens(H1)-1])
  int, mint = intersect(mk, msH)
  if order(int) != order(sH)
    return false, gens(G)
  end
  mp = sub(domain(mk), GrpAbFinGenElem[haspreimage(mk, mint(x))[2] for x in gens(int)])[2]
  fl, new_gens = is_diagonalisable(mp)
  if !fl
    return false, gens(G)
  end
  comp = mk*mSG
  gg = map(comp, new_gens)
  push!(gg, mSG(e))
  @assert all(x -> parent(x) == G, gg)
  return true, gg
end
