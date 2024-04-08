################################################################################
#
#       GrpAb/FinGenAbGroup.jl : Finitely generated abelian groups
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

################################################################################
#
#  Functions for some abstract interfaces
#
################################################################################

elem_type(::Type{FinGenAbGroup}) = FinGenAbGroupElem

parent_type(::Type{FinGenAbGroupElem}) = FinGenAbGroup

is_abelian(::FinGenAbGroup) = true

##############################################################################
#
#  Constructors
#
##############################################################################

@doc raw"""
    abelian_group(::Type{T} = FinGenAbGroup, M::ZZMatrix) -> FinGenAbGroup

Creates the abelian group with relation matrix `M`. That is, the group will
have `ncols(M)` generators and each row of `M` describes one relation.
"""
abelian_group(M::ZZMatrix; name::String = "") = abelian_group(FinGenAbGroup, M, name=name)

function abelian_group(::Type{FinGenAbGroup}, M::ZZMatrix; name::String = "")
   if is_snf(M) && nrows(M) > 0  && ncols(M) > 0 && !isone(M[1, 1])
    N = ZZRingElem[M[i, i] for i = 1:min(nrows(M), ncols(M))]
    if ncols(M) > nrows(M)
      N = vcat(N, ZZRingElem[0 for i = 1:ncols(M)-nrows(M)])
    end
    G = FinGenAbGroup(N)
  else
    G = FinGenAbGroup(M)
  end
  name == "" || set_name!(G, name)
  return G
end

@doc raw"""
    abelian_group(::Type{T} = FinGenAbGroup, M::AbstractMatrix{<:IntegerUnion})

Creates the abelian group with relation matrix `M`. That is, the group will
have `ncols(M)` generators and each row of `M` describes one relation.
"""
function abelian_group(M::AbstractMatrix{<:IntegerUnion}; name::String = "")
  return abelian_group(FinGenAbGroup, M, name=name)
end

function abelian_group(::Type{FinGenAbGroup}, M::AbstractMatrix{<:IntegerUnion}; name::String = "")
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

@doc raw"""
    abelian_group(::Type{T} = FinGenAbGroup, M::AbstractVector{<:IntegerUnion}) -> FinGenAbGroup
    abelian_group(::Type{T} = FinGenAbGroup, M::IntegerUnion...) -> FinGenAbGroup

Creates the direct product of the cyclic groups $\mathbf{Z}/m_i$,
where $m_i$ is the $i$th entry of `M`.
"""
function abelian_group(M::AbstractVector{<:Union{Any, IntegerUnion}}; name::String = "")
  if eltype(M) === Any
    _M = convert(Vector{ZZRingElem}, (ZZ.(M)))::Vector{ZZRingElem}
    return abelian_group(FinGenAbGroup, _M, name=name)
  else
    return abelian_group(FinGenAbGroup, M, name=name)
  end
end

function abelian_group(::Type{FinGenAbGroup}, M::AbstractVector{<:IntegerUnion}; name::String = "")
  if _issnf(M)
    G = FinGenAbGroup(M)
  else
	N = zero_matrix(FlintZZ, length(M), length(M))
    for i = 1:length(M)
      N[i,i] = M[i]
    end
    G = FinGenAbGroup(N)
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

@doc raw"""
    free_abelian_group(::Type{T} = FinGenAbGroup, n::Int) -> FinGenAbGroup

Creates the free abelian group of rank `n`.
"""
free_abelian_group(n::Int) = free_abelian_group(FinGenAbGroup, n)

function free_abelian_group(::Type{FinGenAbGroup}, n::Int)
  return abelian_group(FinGenAbGroup, zeros(Int, n))
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, A::FinGenAbGroup)
  @show_name(io, A)
  @show_special(io, A)

  if is_snf(A)
    show_snf(io, A)
  else
    show_gen(io, A)
  end
end

function show(io::IO, ::MIME"text/plain", A::FinGenAbGroup)
  @show_name(io, A)
  @show_special(io, MIME"text/plain"(), A)

  if is_snf(A)
    show_snf(io, MIME"text/plain"(), A)
  else
    show_gen(io, MIME"text/plain"(), A)
  end
end

function show_hom(io::IO, G::FinGenAbGroup)
  D = get_attribute(G, :hom)
  D === nothing && error("only for hom")
  io = pretty(io)
  if get(io, :supercompact, false)
    print(io, LowercaseOff(), "Hom of abelian groups")
  else
    print(io, LowercaseOff(), "Hom(")
    print(IOContext(io, :supercompact => true), D[1])
    print(io, ", ")
    print(IOContext(io, :supercompact => true), D[2])
    print(io, ")")
  end
end

show_hom(io::IO, ::MIME"text/plain", G::FinGenAbGroup) = show_hom(io, G)

function show_direct_product(io::IO, G::FinGenAbGroup)
  D = get_attribute(G, :direct_product)
  D === nothing && error("only for direct products")
  if get(io, :supercompact, false)
    print(io, "Direct product of abelian groups")
  else
    print(io, "Direct product of ", ItemQuantity(length(D), "abelian group"))
  end
end

function show_direct_product(io::IO, ::MIME"text/plain", G::FinGenAbGroup)
  D = get_attribute(G, :direct_product)
  D === nothing && error("only for direct products")
  io = pretty(io)
  print(io, "Direct product of")
  for G in D
    print(io, "\n", Indent(), G, Dedent())
  end
end

function show_direct_sum(io::IO, G::FinGenAbGroup)
  D = get_attribute(G, :direct_product)
  D === nothing && error("only for direct sums")
  if get(io, :supercompact, false)
    print(io, "Direct sum of abelian groups")
  else
    print(io, "Direct sum of ", ItemQuantity(length(D), "abelian group"))
  end
end

function show_direct_sum(io::IO, ::MIME"text/plain", G::FinGenAbGroup)
  D = get_attribute(G, :direct_product)
  D === nothing && error("only for direct sums")
  io = pretty(io)
  print(io, "Direct sum of")
  for G in D
    print(io, "\n", Indent(), G, Dedent())
  end
end

function show_tensor_product(io::IO, G::FinGenAbGroup)
  D = get_attribute(G, :tensor_product)
  D === nothing && error("only for tensor products")
  if get(io, :supercompact, false)
    print(io, "Tensor product of abelian groups")
  else
    print(io, "Tensor product of ", ItemQuantity(length(D), "abelian group"))
  end
end

function show_tensor_product(io::IO, ::MIME"text/plain", G)#::FinGenAbGroup)
  D = get_attribute(G, :tensor_product)
  D === nothing && error("only for tensor products")
  io = pretty(io)
  print(io, "Tensor product of")
  for G in D
    print(io, "\n", Indent(), G, Dedent())
  end
end

function show_gen(io::IO, ::MIME"text/plain", A::FinGenAbGroup)
  io = pretty(io)
  println(io, "Finitely generated abelian group")
  if isdefined(A, :snf_map)
    println(io, Indent(), "isomorphic to ", domain(A.snf_map), Dedent())
  end
  println(io, Indent(), "with ", ItemQuantity(ncols(rels(A)), "generator"), " and ", ItemQuantity(nrows(rels(A)), "relation"), " and relation matrix")
  show(io, MIME"text/plain"(), rels(A))
  print(io, Dedent())
end

function show_gen(io::IO, A::FinGenAbGroup)
  if get(io, :supercompact, false)
    print(io, "Finitely generated abelian group")
  else
    print(io, "Finitely generated abelian group with ", ItemQuantity(ncols(rels(A)), "generator"), " and ", ItemQuantity(nrows(rels(A)), "relation"))
  end
end

show_snf(io::IO, ::MIME"text/plain", A::FinGenAbGroup) = show_snf_structure(io, A)
show_snf(io::IO, A::FinGenAbGroup) = show_snf_structure(io, A)

function show_snf_structure(io::IO, A::FinGenAbGroup, mul = "x")
  @assert is_snf(A)
  len = length(A.snf)
  io = pretty(io)
  if len == 0
    print(io, LowercaseOff(), "Z/1")
    return
  end

  if A.snf[1] == 0
    if len == 1
      print(io, LowercaseOff(), "Z")
    else
      print(io, LowercaseOff(), "Z^$(len)")
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
      print(io, LowercaseOff(), "Z")
      if j > 1
        print(io, "^($j)")
      end
    else
      if j > 1
        print(io, "(Z/$(inv))^$(j)")
      else
        print(io, LowercaseOff(), "Z/$(inv)")
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

@doc raw"""
    is_snf(G::FinGenAbGroup) -> Bool

Return whether the current relation matrix of the group $G$ is in Smith
normal form.
"""
is_snf(A::FinGenAbGroup) = A.is_snf

@doc raw"""
    number_of_generators(G::FinGenAbGroup) -> Int

Return the number of generators of $G$ in the current representation.
"""
function number_of_generators(A::FinGenAbGroup)
  if is_snf(A)
    return length(A.snf)
  else
    return ncols(A.rels)
  end
end

@doc raw"""
    number_of_relations(G::FinGenAbGroup) -> Int

Return the number of relations of $G$ in the current representation.
"""
function number_of_relations(A::FinGenAbGroup)
  if is_snf(A)
    return length(A.snf)
  else
    return nrows(A.rels)
  end
end

@doc raw"""
    rels(A::FinGenAbGroup) -> ZZMatrix

Return the currently used relations of $G$ as a single matrix.
"""
function rels(A::FinGenAbGroup)
  if is_snf(A)
    return rels_snf(A)
  else
    return rels_gen(A)
  end
end

function rels_gen(A::FinGenAbGroup)
  return A.rels
end

function rels_snf(A::FinGenAbGroup)
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

function assure_has_hnf(A::FinGenAbGroup)
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

@doc raw"""
    snf(A::FinGenAbGroup) -> FinGenAbGroup, FinGenAbGroupHom

Return a pair $(G, f)$, where $G$ is an abelian group in canonical Smith
normal form isomorphic to $A$ and an isomorphism $f : G \to A$.
"""
function snf(G::FinGenAbGroup)
  if isdefined(G, :snf_map)
    return domain(G.snf_map)::FinGenAbGroup, G.snf_map::FinGenAbGroupHom
  end

  if is_snf(G)
    G.snf_map = FinGenAbGroupHom(G) # identity
    return G, G.snf_map::FinGenAbGroupHom
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
        F = Native.GF(Int(e), cached = false)
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
function _reduce_snf(G::FinGenAbGroup, S::ZZMatrix, T::ZZMatrix, Ti::ZZMatrix)

  d = ZZRingElem[S[i,i] for i = 1:min(nrows(S), ncols(S))]

  while length(d) < ngens(G)
    push!(d, 0)
  end

  pos = Int[i for i = 1:length(d) if !isone(d[i])]
  r = Int[i for i = 1:nrows(T)]
  s = ZZRingElem[ d[i] for i in pos]
  TT = sub(T, r, pos)
  TTi = sub(Ti, pos, r)

  H = FinGenAbGroup(s)
  if !isempty(s) && !iszero(s[end])
    H.exponent = s[end]
    G.exponent = s[end]
  end
  mp = hom(H, G, TTi, TT, check = false)
  G.snf_map = mp
  return H, mp::FinGenAbGroupHom
end

################################################################################
#
#  Finiteness
#
################################################################################

@doc raw"""
    isfinite(A::FinGenAbGroup) -> Bool

Return whether $A$ is finite.
"""
isfinite(A::FinGenAbGroup) = all(!iszero, elementary_divisors(A))

################################################################################
#
#  Rank
#
################################################################################

@doc raw"""
    torsion_free_rank(A::FinGenAbGroup) -> Int

Return the torsion free rank of $A$, that is, the dimension of the
$\mathbf{Q}$-vectorspace $A \otimes_{\mathbf Z} \mathbf Q$.

See also [`rank`](@ref).
"""
function torsion_free_rank(A::FinGenAbGroup)
  if !is_snf(A)
    A = snf(A)[1]
  end
  return length(findall(iszero, A.snf))
end

# return the p-rank of A, which is the dimension of the elementary abelian
# group A/pA, or in other words, the rank (=size of minimal generating set) of
# the maximal p-quotient of A
function rank(A::FinGenAbGroup, p::Union{Int, ZZRingElem})
  if !is_snf(A)
    A = snf(A)[1]
  end
  if isempty(A.snf)
    return 0
  end
  if !iszero(mod(A.snf[end], p))
    return 0
  end
  i = findfirst(x -> iszero(mod(x, p)), A.snf)
  return length(A.snf)-i+1
end


@doc raw"""
    rank(A::FinGenAbGroup) -> Int

Return the rank of $A$, that is, the size of a minimal generating set for $A$.

See also [`torsion_free_rank`](@ref).
"""
rank(A::FinGenAbGroup) = error("rank(::FinGenAbGroup) has been renamed to torsion_free_rank")
#rank(A::FinGenAbGroup) = is_snf(A) ? length(A.snf) : return rank(snf(A)[1])


################################################################################
#
#  Order
#
################################################################################

@doc raw"""
    order(A::FinGenAbGroup) -> ZZRingElem

Return the order of $A$. It is assumed that $A$ is finite.
"""
function order(A::FinGenAbGroup)
  is_infinite(A) && error("Group must be finite")
  return prod(elementary_divisors(A))
end

################################################################################
#
#  Exponent
#
################################################################################

@doc raw"""
    exponent(A::FinGenAbGroup) -> ZZRingElem

Return the exponent of $A$. It is assumed that $A$ is finite.
"""
function exponent(A::FinGenAbGroup)
  is_infinite(A) && error("Group must be finite")
  s = elementary_divisors(A)
  length(s)==0 && return ZZ(1)
  return s[end]
end

################################################################################
#
#  Trivial
#
################################################################################

@doc raw"""
    is_trivial(A::FinGenAbGroup) -> Bool

Return whether $A$ is the trivial group.
"""
is_trivial(A::FinGenAbGroup) = isfinite(A) && isone(order(A))

################################################################################
#
#  Isomorphism
#
################################################################################

@doc raw"""
    is_isomorphic(G::FinGenAbGroup, H::FinGenAbGroup) -> Bool

Return whether $G$ and $H$ are isomorphic.
"""
function is_isomorphic(G::FinGenAbGroup, H::FinGenAbGroup)
  return elementary_divisors(G) == elementary_divisors(H)
end

################################################################################
#
#  Direct products/direct sums/biproducts
#
################################################################################
#TODO: check the universal properties here!!!

@doc raw"""
    direct_sum(G::FinGenAbGroup...) -> FinGenAbGroup, Vector{FinGenAbGroupHom}

Return the direct sum $D$ of the (finitely many) abelian groups $G_i$, together
with the injections $G_i \to D$.

For finite abelian groups, finite direct sums and finite direct products agree and
they are therefore called biproducts.
If one wants to obtain $D$ as a direct product together with the projections
$D \to G_i$, one should call `direct_product(G...)`.
If one wants to obtain $D$ as a biproduct together with the projections and the
injections, one should call `biproduct(G...)`.

Otherwise, one could also call `canonical_injections(D)` or `canonical_projections(D)`
later on.
"""
function direct_sum(G::FinGenAbGroup...; task::Symbol = :sum, kwargs...)
  @assert task in [:sum, :prod, :both, :none]
  return _direct_product(:sum, G...; task = task, kwargs...)
end

@doc raw"""
    direct_product(G::FinGenAbGroup...) -> FinGenAbGroup, Vector{FinGenAbGroupHom}

Return the direct product $D$ of the (finitely many) abelian groups $G_i$, together
with the projections $D \to G_i$.

For finite abelian groups, finite direct sums and finite direct products agree and
they are therefore called biproducts.
If one wants to obtain $D$ as a direct sum together with the injections $D \to G_i$,
one should call `direct_sum(G...)`.
If one wants to obtain $D$ as a biproduct together with the projections and the
injections, one should call `biproduct(G...)`.

Otherwise, one could also call `canonical_injections(D)` or `canonical_projections(D)`
later on.
"""
function direct_product(G::FinGenAbGroup...; task::Symbol = :prod, kwargs...)
  @assert task in [:prod, :sum, :both, :none]
  return _direct_product(:prod, G...; task = task, kwargs...)
end

@doc raw"""
    biproduct(G::FinGenAbGroup...) -> FinGenAbGroup, Vector{FinGenAbGroupHom}, Vector{FinGenAbGroupHom}

Return the direct product $D$ of the (finitely many) abelian groups $G_i$, together
with the projections $D \to G_i$ and the injections $G_i \to D$.

For finite abelian groups, finite direct sums and finite direct products agree and
they are therefore called biproducts.
If one wants to obtain $D$ as a direct sum together with the injections $G_i \to D$,
one should call `direct_sum(G...)`.
If one wants to obtain $D$ as a direct product together with the projections $D \to G_i$,
one should call `direct_product(G...)`.

Otherwise, one could also call `canonical_injections(D)` or `canonical_projections(D)`
later on.
"""
function biproduct(G::FinGenAbGroup...; task::Symbol = :both, kwargs...)
  @assert task in [:prod, :sum, :both, :none]
  return _direct_product(:prod, G...; task = task, kwargs...)
end

@doc raw"""
    ⊕(A::FinGenAbGroup...) -> FinGenAbGroup

Return the direct sum $D$ of the (finitely many) abelian groups $G_i$.

If one wants to access the injections $G_i \to D$ or the projections $D \to G_i$ later,
one can call respectively `canonical_injections(D)` or `canonical_projections(D)`.
"""
function _direct_product(t::Symbol, G::FinGenAbGroup...
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
  inj = FinGenAbGroupHom[]
  pro = FinGenAbGroupHom[]
  jj = 0
  for j=1:length(G)
    g = G[j]
    if task in [:sum, :both]
#      m = hom(g, Dp, FinGenAbGroupElem[Dp[j+i] for i = 1:ngens(g)], check = false)
#      should just be 0...Id 0... 0
      x = zero_matrix(ZZ, ngens(g), ngens(Dp))
      for j = 1:ngens(g)
        x[j, jj+j] = 1
      end
      m = hom(g, Dp, x, check = false)
      add_to_lattice && append!(L, m)
      push!(inj, m)
    end
    if task in [:prod, :both]
#      m = hom(Dp, g, vcat(FinGenAbGroupElem[g[0] for i = 1:j], gens(g), FinGenAbGroupElem[g[0] for i=j+ngens(g)+1:ngens(Dp)]), check = false)
      x = zero_matrix(ZZ, ngens(Dp), ngens(g))
      for j = 1:ngens(g)
        x[jj+j, j] = 1
      end
      m = hom(Dp, g, x, check = false)
      add_to_lattice && append!(L, m)
      push!(pro, m)
    end
    jj += ngens(g)
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

⊕(A::FinGenAbGroup...) = direct_sum(A..., task = :none)

#TODO: use matrices as above - or design special maps that are not tied
#      to matrices but operate directly.
@doc raw"""
    canonical_injections(G::FinGenAbGroup) -> Vector{FinGenAbGroupHom}

Given a group $G$ that was created as a direct product, return the
injections from all components.
"""
function canonical_injections(G::FinGenAbGroup)
  D = get_attribute(G, :direct_product)
  D === nothing && error("1st argument must be a direct product")
  return [canonical_injection(G, i) for i=1:length(D)]
end

@doc raw"""
    canonical_injection(G::FinGenAbGroup, i::Int) -> FinGenAbGroupHom

Given a group $G$ that was created as a direct product, return the
injection from the $i$th component.
"""
function canonical_injection(G::FinGenAbGroup, i::Int)
  D = get_attribute(G, :direct_product)
  D === nothing && error("1st argument must be a direct product")
  s = sum([ngens(D[j]) for j = 1:i-1], init = 0)
  h = hom(D[i], G, [G[s+j] for j = 1:ngens(D[i])])
  return h
end

@doc raw"""
    canonical_projections(G::FinGenAbGroup) -> Vector{FinGenAbGroupHom}

Given a group $G$ that was created as a direct product, return the
projections onto all components.
"""
function canonical_projections(G::FinGenAbGroup)
  D = get_attribute(G, :direct_product)
  D === nothing && error("1st argument must be a direct product")
  return [canonical_projection(G, i) for i=1:length(D)]
end

@doc raw"""
    canonical_projection(G::FinGenAbGroup, i::Int) -> FinGenAbGroupHom

Given a group $G$ that was created as a direct product, return the
projection onto the $i$th component.
"""
function canonical_projection(G::FinGenAbGroup, i::Int)
  D = get_attribute(G, :direct_product)
  D === nothing && error("1st argument must be a direct product")
  H = D[i]
  h = hom(G, H, vcat( [FinGenAbGroupElem[H[0] for j = 1:ngens(D[h])] for h = 1:i-1]...,
                         gens(H),
                      [FinGenAbGroupElem[H[0] for j = 1:ngens(D[h])] for h = i+1:length(D)]...))
  return h
end

function matrix(M::Map{FinGenAbGroup, FinGenAbGroup})
  if typeof(M) == FinGenAbGroupHom
    return M.map
  end
  G = domain(M)
  return reduce(vcat, [M(g).coeff for g = gens(G)])
end

function matrix(M::Generic.IdentityMap{FinGenAbGroup})
  return identity_matrix(FlintZZ, ngens(domain(M)))
end

@doc raw"""
    hom(G::FinGenAbGroup, H::FinGenAbGroup, A::Matrix{ <: Map{FinGenAbGroup, FinGenAbGroup}}) -> Map

Given groups $G$ and $H$ that are created as direct products as well
as a matrix $A$ containing maps $A[i,j] : G_i \to H_j$, return
the induced homomorphism.
"""
function hom(G::FinGenAbGroup, H::FinGenAbGroup, A::Matrix{ <: Map{FinGenAbGroup, FinGenAbGroup}})
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
  h = hom(G, H, reduce(vcat, [reduce(hcat, [matrix(A[i,j]) for j=1:c]) for i=1:r]))
  return h
end

function _flat(G::FinGenAbGroup)
  s = get_attribute(G, :direct_product)
  if s === nothing
    return [G]
  end
  return reduce(vcat, [_flat(x) for x = s])
end

function _tensor_flat(G::FinGenAbGroup)
  s = get_attribute(G, :tensor_product)
  if s === nothing
    return [G]
  end
  return reduce(vcat, [_tensor_flat(x) for x = s])
end


@doc raw"""
    flat(G::FinGenAbGroup) -> FinGenAbGroupHom

Given a group $G$ that is created using (iterated) direct products, or
(iterated) tensor products, return a group isomorphism into a flat product:
for $G := (A \oplus B) \oplus C$, it returns the isomorphism
$G \to A \oplus B \oplus C$ (resp. $\otimes$).
"""
function flat(G::FinGenAbGroup)
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

function tensor_product2(G::FinGenAbGroup, H::FinGenAbGroup)
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

parent(t::Tuple) = TupleParent(t)

@doc raw"""
    tensor_product(G::FinGenAbGroup...; task::Symbol = :map) -> FinGenAbGroup, Map

Given groups $G_i$, compute the tensor product $G_1\otimes \cdots \otimes G_n$.
If `task` is set to ":map", a map $\phi$ is returned that
maps tuples in $G_1 \times \cdots \times G_n$ to pure tensors
$g_1 \otimes \cdots \otimes g_n$. The map admits a preimage as well.
"""
function tensor_product(G::FinGenAbGroup...; task::Symbol = :map)
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

  function pure(g::FinGenAbGroupElem...)
    @assert length(g) == length(G)
    @assert all(i-> parent(g[i]) == G[i], 1:length(G))

    return T(vec(collect(prod(x) for x = Base.Iterators.product([h.coeff for h = reverse(g)]...))))
  end
  function pure(T::Tuple)
    return pure(T...)
  end
  function inv_pure(t::FinGenAbGroupElem)
    p = Base.findall(i -> !iszero(t[i]), 1:ngens(T))
    if length(p) == 0
      return Tuple(collect(g[0] for g = G))
    end
    @assert length(p) == 1
    @assert t[p[1]] == 1
    return reverse(g[p[1]])
  end

  return T, MapFromFunc(TupleParent(Tuple([g[0] for g = G])), T, pure, inv_pure)
end

⊗(G::FinGenAbGroup...) = tensor_product(G..., task = :none)

@doc raw"""
    hom(G::FinGenAbGroup, H::FinGenAbGroup, A::Vector{ <: Map{FinGenAbGroup, FinGenAbGroup}}) -> Map

Given groups $G = G_1 \otimes \cdots \otimes G_n$ and
$H = H_1 \otimes \cdot \otimes H_n$ as well as maps
$\phi_i: G_i\to H_i$, compute the tensor product of the maps.
"""
function hom(G::FinGenAbGroup, H::FinGenAbGroup, A::Vector{ <: Map{FinGenAbGroup, FinGenAbGroup}})
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

@doc raw"""
    is_torsion(G::FinGenAbGroup) -> Bool

Return whether `G` is a torsion group.
"""
is_torsion(G::FinGenAbGroup) = isfinite(G)

@doc raw"""
    torsion_subgroup(G::FinGenAbGroup) -> FinGenAbGroup, Map

Return the torsion subgroup of `G`.
"""
function torsion_subgroup(G::FinGenAbGroup, add_to_lattice::Bool = true,
                                          L::GrpAbLattice = GroupLattice)
  S, mS = snf(G)
  subs = FinGenAbGroupElem[]
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

@doc raw"""
    is_free(G::FinGenAbGroup) -> Bool

Returns whether `G` is free.
"""
function is_free(G::FinGenAbGroup)
  T, = torsion_subgroup(G, false)
  return isone(order(T))
end

##############################################################################
#
#  Subgroups
#
##############################################################################

@doc raw"""
    sub(G::FinGenAbGroup, s::Vector{FinGenAbGroupElem}) -> FinGenAbGroup, FinGenAbGroupHom

Create the subgroup $H$ of $G$ generated by the elements in `s` together
with the injection $\iota : H \to G$.
"""
function sub(G::FinGenAbGroup, s::Vector{FinGenAbGroupElem},
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice; simplify::Bool = false)

  if length(s) == 0
    S = FinGenAbGroup(Int[])
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
  if simplify
    s, mp = snf(S)
    S = s
    mS = FinGenAbGroupHom(mp*mS)
  end

  if add_to_lattice
    append!(L, mS)
  end
  return S, mS
end

@doc raw"""
    sub(s::Vector{FinGenAbGroupElem}) -> FinGenAbGroup, FinGenAbGroupHom

Assuming that the non-empty array `s` contains elements of an abelian group
$G$, this functions returns the subgroup $H$ of $G$ generated by the elements
in `s` together with the injection $\iota : H \to G$.
"""
function sub(s::Vector{FinGenAbGroupElem},
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  length(s) == 0 && error("Array must be non-empty")
  return sub(parent(s[1]), s, add_to_lattice, L)
end

@doc raw"""
    sub(G::FinGenAbGroup, M::ZZMatrix) -> FinGenAbGroup, FinGenAbGroupHom

Create the subgroup $H$ of $G$ generated by the elements corresponding to the
rows of $M$ together with the injection $\iota : H \to G$.
"""
function sub(G::FinGenAbGroup, M::ZZMatrix,
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

function _sub_integer_snf(G::FinGenAbGroup, n::ZZRingElem, add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  ind = 1
  while ind <= ngens(G) && gcd(n, G.snf[ind]) == G.snf[ind]
    ind += 1
  end
  if ind == ngens(G) && gcd(n, G.snf[ind]) == G.snf[ind]
    Gnew = FinGenAbGroup(Int[])
    mp = hom(Gnew, G, FinGenAbGroupElem[])
    if add_to_lattice
      append!(L, mp)
    end
    return Gnew, mp
  end
  invariants = Vector{ZZRingElem}(undef, ngens(G)-ind+1)
  for_map = Vector{ZZRingElem}(undef, ngens(G)-ind+1)
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

@doc raw"""
    sub(G::FinGenAbGroup, n::ZZRingElem) -> FinGenAbGroup, FinGenAbGroupHom

Create the subgroup $n \cdot G$ of $G$ together
with the injection $\iota : n\cdot G \to G$.
"""
function sub(G::FinGenAbGroup, n::ZZRingElem,
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

@doc raw"""
    sub(G::FinGenAbGroup, n::Integer) -> FinGenAbGroup, Map

Create the subgroup $n \cdot G$ of $G$ together
with the injection $\iota : n \cdot G \to G$.
"""
function sub(G::FinGenAbGroup, n::Integer,
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  return sub(G, ZZRingElem(n), add_to_lattice, L)
end

################################################################################
#
#  Quotients
#
################################################################################

@doc raw"""
    quo(G::FinGenAbGroup, s::Vector{FinGenAbGroupElem}) -> FinGenAbGroup, GrpAbfinGemMap

Create the quotient $H$ of $G$ by the subgroup generated by the elements in
$s$, together with the projection $p : G \to H$.
"""
function quo(G::FinGenAbGroup, s::Vector{FinGenAbGroupElem},
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

@doc raw"""
    quo(G::FinGenAbGroup, M::ZZMatrix) -> FinGenAbGroup, FinGenAbGroupHom

Create the quotient $H$ of $G$ by the subgroup generated by the elements
corresponding to the rows of $M$, together with the projection $p : G \to H$.
"""
function quo(G::FinGenAbGroup, M::ZZMatrix,
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

function quo(G::FinGenAbGroup, f::FinGenAbGroupHom,
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  M = f.map
  return quo(G, M, add_to_lattice, L)
end

@doc raw"""
    quo(G::FinGenAbGroup, n::Integer}) -> FinGenAbGroup, Map
    quo(G::FinGenAbGroup, n::ZZRingElem}) -> FinGenAbGroup, Map

Returns the quotient $H = G/nG$ together with the projection $p : G \to H$.
"""
function quo(G::FinGenAbGroup, n::IntegerUnion,
             add_to_lattice::Bool = true, L::GrpAbLattice = GroupLattice)
  if is_snf(G)
    return quo_snf(G, n, add_to_lattice, L)
  else
    return quo_gen(G, n, add_to_lattice, L)
  end
end

function quo_snf(G::FinGenAbGroup, n::IntegerUnion,
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

function quo_gen(G::FinGenAbGroup, n::IntegerUnion,
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

@doc raw"""
    intersect(mG::FinGenAbGroupHom, mH::FinGenAbGroupHom) -> FinGenAbGroup, Map

Given two injective maps of abelian groups with the same codomain $G$,
return the intersection of the images as a subgroup of $G$.
"""
function Base.intersect(mG::FinGenAbGroupHom, mH::FinGenAbGroupHom,
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
   return sub(GH, [mG(FinGenAbGroupElem(G, view(h, j:j, ngens(GH)+1:ncols(h)))) for j=i+1:nrows(h)], add_to_lattice, L, simplify = true)
end


################################################################################
#
#  use lattice...
#
################################################################################

function +(G::FinGenAbGroup, H::FinGenAbGroup, L::GrpAbLattice = GroupLattice)
  fl, GH, mG, mH = can_map_into_overstructure(L, G, H)
  if !fl
    error("no common overgroup known")
  end
  return sub(GH, vcat([GH(mG[i, :]) for i=1:nrows(mG)], [GH(mH[i, :]) for i=1:nrows(mH)]))[1]
end

function Base.intersect(G::FinGenAbGroup, H::FinGenAbGroup, L::GrpAbLattice = GroupLattice)
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
  return sub(G, [G(sub(h, j:j, ngens(GH)+1:ncols(h))) for j=i+1:nrows(h)], simplify = true)[1]
end

function Base.intersect(A::Vector{FinGenAbGroup})
  a = first(A)
  for b = A
    a = intersect(a, b)
  end
  return a
end

@doc raw"""
  issubset(G::FinGenAbGroup, H::FinGenAbGroup) -> Bool

Return true if G is contained in H, false otherwise.
"""
function Base.issubset(G::FinGenAbGroup, H::FinGenAbGroup, L::GrpAbLattice = GroupLattice)
  fl, GH, mG, mH = can_map_into_overstructure(L, G, H)
  if !fl
    error("no common overgroup known")
  end
  hH = hom(H, GH, mH)
  hG = hom(G, GH, mG)
  return _issubset(hG, hH)
end

#checks if the image of mH is contained in the image of mG
function _issubset(mH::FinGenAbGroupHom, mG::FinGenAbGroupHom)
  k, mk = cokernel(mG, false)
  return iszero(mH*mk)
end

function is_subgroup(G::FinGenAbGroup, H::FinGenAbGroup, L::GrpAbLattice = GroupLattice)
  fl, GH, mG, mH = can_map_into_overstructure(L, G, H)
  if !fl
    error("no common overgroup known")
  end
  hH = hom(H, GH, mH)
  els = [FinGenAbGroupElem(GH, mG[j:j, :]) for j = 1:nrows(mG)]
  fl, imgs = has_preimage_with_preimage(hH, els)
  if !fl
    return false, hH
  else
    return true, hom(G, H, imgs, check = false)
  end
end

#checks if the image of mG contains the image of mH


#cannot define == as this produces problems elsewhere... need some thought
function is_eq(G::FinGenAbGroup, H::FinGenAbGroup, L::GrpAbLattice = GroupLattice)
  isfinite(G) && (order(G) == order(H) || return false)
  return is_subgroup(G, H)[1] && is_subgroup(H, G)[1]
end

function Base.isequal(G::FinGenAbGroup, H::FinGenAbGroup)
  return G === H
end

@doc raw"""
    quo(G::FinGenAbGroup, U::FinGenAbGroup) -> FinGenAbGroup, Map

Create the quotient $H$ of $G$ by $U$, together with the projection
$p : G \to H$.
"""
function quo(G::FinGenAbGroup, U::FinGenAbGroup,  add_to_lattice::Bool = true,
                                            L::GrpAbLattice = GroupLattice)
  fl, m = is_subgroup(U, G, L)
  fl || error("not a subgroup")
  return quo(G, m.map, add_to_lattice, L)
end

################################################################################
#
#  Make Smith normal form
#
################################################################################

function make_domain_snf(m::Map{FinGenAbGroup, T}) where T
  G = domain(m)
  S, mS = snf(G)
  return mS*m
end

################################################################################
#
#  Cyclic
#
################################################################################

@doc raw"""
    is_cyclic(G::FinGenAbGroup) -> Bool

Return whether $G$ is cyclic.
"""
function is_cyclic(G::FinGenAbGroup)
  return length(elementary_divisors(G)) <= 1
end

################################################################################
#
#  p-Sylow subgroup
#
################################################################################

function _psylow_subgroup_gens(G::FinGenAbGroup, p::IntegerUnion)
  @assert is_snf(G)
  z = FinGenAbGroupElem[]
  for i in 1:ngens(G)
    k, m = remove(G.snf[i], p)
    if k != 0
      push!(z, m*G[i])
    end
  end
  return z
end

@doc raw"""
    sylow_subgroup(G::FinGenAbGroup, p::IntegerUnion) -> FinGenAbGroup, FinGenAbGroupHom

Return the Sylow $p-$subgroup of the finitely generated abelian group `G`, for a
prime `p`. This is the subgroup of `p`-power order in `G` whose index in `G` is
coprime to `p`.

# Examples
```jldoctest
julia> A = abelian_group(ZZRingElem[2, 6, 30])
Z/2 x Z/6 x Z/30

julia> H, j = sylow_subgroup(A, 2);

julia> H
(Z/2)^3

julia> divexact(order(A), order(H))
45
```
"""
function sylow_subgroup(G::FinGenAbGroup, p::IntegerUnion,
                        to_lattice::Bool = true)
  @req is_prime(p) "Number ($p) must be prime"
  S, mS = snf(G)
  z = _psylow_subgroup_gens(S, p)
  zz = [ image(mS, x) for x in z ]
  return sub(G, zz, to_lattice)
end

@doc raw"""
    primary_part(G::FinGenAbGroup, m::IntegerUnion) -> FinGenAbGroup, FinGenAbGroupHom

Return the $m$-primary part of `G`.
"""
function primary_part(G::FinGenAbGroup, m::IntegerUnion,
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
@doc raw"""
    multgrp_of_cyclic_grp(n::ZZRingElem) -> FinGenAbGroup

Returns the multiplicative group of the cyclic group with $n$ elements.
"""
function multgrp_of_cyclic_grp(n::ZZRingElem)
  composition = Vector{ZZRingElem}()
  for (p,mp) in factor(n)
    if (p == 2) && (mp >= 2)
      push!(composition,2)
      push!(composition,ZZRingElem(2)^(mp-2))
    else
      push!(composition,(p-1)*p^(mp-1))
    end
  end
  return abelian_group(composition)
end

multgrp_of_cyclic_grp(n::Integer) = multgrp_of_cyclic_grp(ZZRingElem(n))

################################################################################
#
#  Isomorphism to abelian groups
#
################################################################################

@doc raw"""
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
  GtoA = Dict{eltype(G), FinGenAbGroupElem}()
  AtoG = Dict{FinGenAbGroupElem, eltype(G)}()
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

function find_isomorphism_with_abelian_group(G::Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}})
	id = id_hom(domain(G[1]))
	S = small_generating_set(G)
  p = 2
  R = GF(p, cached = false)
  K = domain(G[1])
  Rx = polynomial_ring(R, "x", cached = false)[1]
  while iszero(discriminant(Rx(K.pol)))
    p = next_prime(p)
		R = GF(p, cached = false)
	  Rx = polynomial_ring(R, "x", cached = false)[1]
	end
  list = fpPolyRingElem[Rx(x.prim_img) for x in S]
  push!(list, gen(Rx))
  n = length(G)
  elem_to_index = Dict{morphism_type(AbsSimpleNumField, AbsSimpleNumField), Int}()
  words = Dict{fpPolyRingElem, Array{Int}}()
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
  GtoAsnf = Dict{eltype(G), FinGenAbGroupElem}()
  AsnftoG = Dict{FinGenAbGroupElem, eltype(G)}()
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
		@assert ind !== nothing
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
  GtoAsnf = Dict{eltype(G), FinGenAbGroupElem}()
  AsnftoG = Dict{FinGenAbGroupElem, eltype(G)}()
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

@doc raw"""
    abelian_groups(n::Int) -> Vector{FinGenAbGroup}

Given a positive integer $n$, return a list of all abelian groups of order $n$.
"""
function abelian_groups(n::Int)
  if n == 1
    return FinGenAbGroup[abelian_group(Int[])]
  end
  nn = ZZRingElem(n)
  fac = factor(nn)
  sylow_lists = Vector{Vector{FinGenAbGroup}}()
  for (p, e) in fac
    push!(sylow_lists, FinGenAbGroup[abelian_group(ZZRingElem[p^i for i in reverse(t)]) for t in AllParts(e)])
  end
  C = Base.Iterators.product(sylow_lists...)
  grps = FinGenAbGroup[]
  for c in C
    G = c[1]
    for i in 2:length(fac)
      G = snf(direct_product(G, c[i], task = :none))[1]
    end
    push!(grps, G)
  end
  return grps
end

function *(a::ZZRingElem, M::FinGenAbGroupHom)
  return hom(domain(M), codomain(M), [a*M(g) for g = gens(domain(M))], check = false)
end

*(a::Integer, M::FinGenAbGroupHom) = ZZRingElem(a)*M


################################################################################
#
#  Functions related to the action of a group of endomorphisms
#
################################################################################

function induce_action_on_subgroup(mS::FinGenAbGroupHom, acts::Vector{FinGenAbGroupHom})
  res = Vector{FinGenAbGroupHom}(undef, length(acts))
  S = domain(mS)
  for i = 1:length(acts)
    imgs = Vector{FinGenAbGroupElem}(undef, ngens(S))
    for j = 1:length(imgs)
      imgs[j] = mS\(acts[i](mS(S[j])))
    end
    res[i] = hom(S, S, imgs)
  end
  return res
end

function fixed_subgroup(f::FinGenAbGroupHom, to_lattice::Bool = true)
  @assert domain(f) == codomain(f)
  return kernel(f - id_hom(domain(f)), to_lattice)
end

function is_fixed_point_free(act::Vector{FinGenAbGroupHom})
  G = domain(act[1])
   intersection_of_kernels = id_hom(G)
  minus_id = hom(G, G, FinGenAbGroupElem[-x for x in gens(G)])
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

@doc raw"""
    elementary_divisors(G::FinGenAbGroup) -> Vector{ZZRingElem}

Given $G$, return the elementary divisors of $G$, that is, the unique non-negative
integers $e_1,\dotsc,e_k$ with $e_i \mid e_{i + 1}$ and $e_i\neq 1$ such that
$G \cong \mathbf{Z}/e_1\mathbf{Z} \times \dotsb \times \mathbf{Z}/e_k\mathbf{Z}$.
"""
function elementary_divisors(G::FinGenAbGroup)
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

@doc raw"""
    has_quotient(G::FinGenAbGroup, invariant::Vector{Int}) -> Bool

Given an abelian group $G$, return true if it has a quotient with given elementary
divisors and false otherwise.
"""
function has_quotient(G::FinGenAbGroup, invariants::Vector{Int})
  H = abelian_group(invariants)
  H = snf(H)[1]
  G1 = snf(G)[1]
  arr_snfG1 = filter(x -> x != 1, G1.snf)
  arr_snfH = filter(x -> x != 1, H.snf)
  if length(arr_snfG1) < length(arr_snfH)
    return false
  end
  for i = 0:length(arr_snfH)-1
    if !is_divisible_by(arr_snfG1[end-i], arr_snfH[end-i])
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

@doc raw"""
    is_pure(U::FinGenAbGroup, G::FinGenAbGroup) -> Bool

A subgroup `U` of `G` is called pure if for all `n` an element in `U`
that is in the image of the multiplication by `n` map of `G` is also
a multiple of an element in `U`.

For finite abelian groups this is equivalent to `U` having a complement in `G`.
They are also know as *isolated subgroups* and *serving subgroups*.

See also: [`is_neat`](@ref), [`has_complement`](@ref)

# EXAMPLES
```julia
julia> G = abelian_group([2, 8]);

julia> U, _ = sub(G, [G[1]+2*G[2]]);

julia> is_pure(U, G)
false

julia> U, _ = sub(G, [G[1]+4*G[2]]);

julia> is_pure(U)
true

julia> has_complement(U, G)[1]
true
```
"""
function is_pure(U::FinGenAbGroup, G::FinGenAbGroup)
  @assert is_finite(G)
  #not implemented in general: needs to be done via torsion subgroup
  n = exponent(G)
  lf = factor(n)
  for (p, k) = lf
    for i=1:k
      h = hom(G, G, [p^i*g for g = gens(G)])
      q, mq = quo(intersect(image(h)[1], U), h(U)[1])
      if order(q) != 1
        return false
      end
    end
  end
  return true
end

@doc raw"""
    is_neat(U::FinGenAbGroup, G::FinGenAbGroup) -> Bool

A subgroup `U` of `G` is called neat if for all primes `p` an element in `U`
that is in the image of the multiplication by `p` map of `G` is also
a multiple of an element in `U`.

See also: [`is_pure`](@ref)


# EXAMPLES
```julia
julia> G = abelian_group([2, 8]);

julia> U, _ = sub(G, [G[1] + 2*G[2]]);

julia> is_neat(U, G)
true

julia> is_pure(U, G)
false
```
"""
function is_neat(U::FinGenAbGroup, G::FinGenAbGroup)
  @assert is_finite(G)
  #not implemented in general: needs to be done via torsion subgroup
  n = exponent(G)
  lf = factor(n).fac
  for p = keys(lf)
    h = hom(G, G, [p*g for g = gens(G)])
    q, mq = quo(intersect(image(h)[1], U), h(U)[1])
    if order(q) != 1
      return false
    end
  end
  return true
end

@doc raw"""
    saturate(U::FinGenAbGroup, G::FinGenAbGroup) -> FinGenAbGroup

For a subgroup `U` of `G` find a minimal overgroup that is pure,
and thus has a complement.

See also: [`is_pure`](@ref), [`has_complement`](@ref)
"""
function saturate(U::FinGenAbGroup, G::FinGenAbGroup)
  @assert is_finite(G)
  #not implemented in general: needs to be done via torsion subgroup
  n = exponent(G)
  lf = factor(n)
  for (p, k) = lf
    for i=k:-1:1
      h = hom(G, G, [p^i*g for g = gens(G)])
      i, mi = image(h)
      s = intersect(i, U)
      fl, mp = is_subgroup(s, G)
      q, mq = quo(s, h(U)[1])
      if order(q) != 1
        oU = order(U)
        U = (U + sub(G, [preimage(h, image(mp, preimage(mq, g))) for g = gens(q)])[1])
        @assert oU != order(U)
      end
    end
  end
  return U
end

#TODO: a better algorithm?
@doc raw"""
    has_complement(f::FinGenAbGroupHom) -> Bool, FinGenAbGroupHom
    has_complement(U::FinGenAbGroup, G::FinGenAbGroup) -> Bool, FinGenAbGroupHom

Given a map representing a subgroup of a group $G$,
or a subgroup `U` of a group `G`, return either true and
an injection of a complement in $G$, or false.

See also: [`is_pure`](@ref)
"""
function has_complement(m::FinGenAbGroupHom, to_lattice::Bool = true)
  G = codomain(m)
  if !isfinite(G)
    U = domain(m)
    q, mq = quo(G, U, false)
    q, _mq = snf(q)
    mq = mq*inv(_mq)
    Cgens = [preimage(mq, g) for g = gens(q)]
    C, mC = sub(G, Cgens, false)
    _, sumUC = sub(G, append!(m.(gens(U)), Cgens), false)
    return is_trivial(intersect(m, mC, false)[1])  && is_trivial(quo(G, sumUC, false)[1]), mC
  end
  H, mH = cokernel(m, false)
  SH, mSH = snf(H)
  mH = mH*inv(mSH)
  s, ms = snf(domain(m))
  m1 = ms*m
  gens_complement = FinGenAbGroupElem[]
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
    fl, el = has_preimage_with_preimage(mS1*m1, test_el)
    if !fl
      return false, sub(G, FinGenAbGroupElem[], false)[2]
    end
    el1 = mS1(el)
    coeffs = zero_matrix(FlintZZ, 1, ngens(s))
    for j = 1:ngens(s)
      if !iszero(el1[j])
        R = residue_ring(FlintZZ, s.snf[j], cached = false)[1]
        r1 = R(el1[j])
        r2 = R(SH.snf[i])
        fl1, r = divides(r1, r2)
        @assert fl1
        coeffs[1, j] = lift(r)
      end
    end
    el_sub = FinGenAbGroupElem(s, coeffs)
    push!(gens_complement, igSH - m1(el_sub))
  end
  res, mres = sub(G, gens_complement, false)
  @assert order(res)*order(s) == order(G)
  return true, mres
end

#TODO: is this the correct(?) interface? it feels natural, but the map
#      may or may not be required
function has_complement(U::FinGenAbGroup, G::FinGenAbGroup)
  fl, mp = is_subgroup(U, G)
  fl || error("not a subgroup")
  fl, mp = has_complement(mp)
  fl && return fl, image(mp)[1]
  return fl, U
end

################################################################################
#
#  Identity
#
################################################################################

id(G::FinGenAbGroup) = G(zeros(ZZRingElem, ngens(G)))

################################################################################
#
#  Diagonalize a subgroup
#
################################################################################


#Given a subgroup H of a group G, I want to find generators $g_1, dots, g_s$ of
#G such that H = \sum H \cap <g_i> and the relation matrix of $G$ is diagonal.
function is_diagonalisable(mH::FinGenAbGroupHom)

  H = domain(mH)
  G = codomain(mH)
  SH, mSH = snf(H)
  SG, mSG = snf(G)
  if ngens(SH) == 0
    gg =  FinGenAbGroupElem[mSG(SG[i]) for i = 1:ngens(SG)]
    @assert all(x -> parent(x) == G, gg)
    return true, gg
  end
  mH1 = mSH * mH * inv(mSG)
  H1 = domain(mH1)
  G1 = codomain(mH1)
  el = mH1(H1[ngens(H1)])
  pk = gcd(ZZRingElem[el[i] for i = 1:ngens(G1)])
  pk = gcd(pk, exponent(G1))
  e = G1[0]
  for i = 1:ngens(G1)
    e += divexact(el[i], pk)*G1[i]
  end
  sel, msel = sub(G1, FinGenAbGroupElem[e])
  fl, mk = has_complement(msel)
  if !fl
    return false, gens(G)
  end
  sH, msH = sub(G1, FinGenAbGroupElem[mH1(H1[i]) for i = 1:ngens(H1)-1])
  int, mint = intersect(mk, msH)
  if order(int) != order(sH)
    return false, gens(G)
  end
  mp = sub(domain(mk), FinGenAbGroupElem[has_preimage_with_preimage(mk, mint(x))[2] for x in gens(int)])[2]
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
