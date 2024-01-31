################################################################################
#
#  GrpAb/SubgroupEnum.jl : Subgroup enumeration for finitely generated
#                          abelian groups.
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

################################################################################
#
#  Enumeration of subgroups of index p
#
################################################################################

function index_p_subgroups(A::FinGenAbGroup, p::Integer)
  return index_p_subgroups(A, ZZRingElem(p))
end

mutable struct IndexPSubgroups{S, T}
  p::Int
  n::UInt
  st::Int
  mp::S
  c::ZZMatrix
  mthd::T

  function IndexPSubgroups{T}(A::FinGenAbGroup, p::ZZRingElem, mthd::T = sub) where {T}
    if order(A) % p != 0
      r = new{Generic.IdentityMap{FinGenAbGroup}, T}()
      r.n = 0
      return r
    end
    s, ms = snf(A)  # ms: A -> s
    r = new{typeof(inv(ms)), T}()
    @assert s.is_snf
    r.p = Int(p)
    r.mp = inv(ms)
    i=1
    while s.snf[i] % p != 0
      i += 1
    end
    r.st = i
    r.n = UInt(div(ZZRingElem(p)^(length(s.snf)-i+1) - 1, ZZRingElem(p)-1))
    r.c = zero_matrix(FlintZZ, length(s.snf), length(s.snf))
    r.mthd = mthd
    r.c
    return r
  end
end

function index_p_subgroups(A::FinGenAbGroup, p::IntegerUnion, mthd::T = sub) where {T}
  q = ZZRingElem(p)
  @assert is_prime(q)
  I = IndexPSubgroups{T}(A, q, mthd)

  #a subgroup of index p corresponds to a HNF with exactly one p on the
  #diagonal - and the other entries arbitrary reduced.
  #so it should be 1 + p + p^2 + + p^(n-1) = ((p^n)-1)/(p-1) many
  return I
end

function index_to_group(s::IndexPSubgroups, i::UInt)
  j = 1
  x = 1
  while i>=x
    i -= x
    x *= s.p
    j += 1
  end
  c = s.c
  zero!(c)
  for k=1:nrows(c)
    if s.st+j-1 != k
      c[k, k] = 1
    end
  end
  k = 1
  while i != 0
    c[k+s.st-1, s.st + j-1] = i%s.p
    i = div(i, s.p)
    k += 1
  end
  c[s.st + j-1, s.st + j-1] = s.p
  gen = [s.mp\(FinGenAbGroupElem(codomain(s.mp), sub(c, l:l, 1:ncols(c)))) for l=1:nrows(c)]
  return s.mthd(domain(s.mp), gen)
end

function Base.iterate(s::IndexPSubgroups, i::UInt = UInt(0))
  if i + 1 > s.n
    return nothing
  end

  return index_to_group(s, i), (i + 1)
end

#function Base.iterate(s::IndexPSubgroups, i::UInt)
#  if i > s.n - 1
#    return nothing
#  end
#
#  return index_to_group(s, i), i + 1
#end

Base.IteratorSize(::Type{IndexPSubgroups{S, T}}) where {S, T} = Base.HasLength()

function Base.length(s::IndexPSubgroups)
  return s.n
end

#function Base.done(s::IndexPSubgroups, i::UInt)
#  return i>=s.n
#end

#=
example:
 julia> sg = index_p_subgroups(FinGenAbGroup([3,3,3,3]), 3)
 julia> index_to_group(sg, UInt(6));
=#

################################################################################
#
#  Subgroup iterators for p-groups
#
################################################################################

# We use the algorithm of Butler, Subgroup Lattices and Symmetric Functions,
# Section 1.6. But we use the description of Cohen, Advanced Topics in
# Computational Number Theory, Theorem 4.1.18.

# Some notation/convention:
# An abelian p-group A has a unique type (n_1,...,n_r), which is decreasing
# with the property that A \cong Z/p^{n_1} x ... x Z/p^{n_r}.

# Given a p-group with type x, the following function enumerates all possible
# types y of a subgroup of length t. The only restrictions on y are
# length(y) <= length(x), y_1 \leq x_1 and y_i \leq min(y_{i-1}, x_i) for
# 2 \leq i \leq length(y). This is part (1) of Theorem 4.1.18.

struct yIterator
  t::Int
  x::Vector{Int}
  nulls::Vector{Int}
  res::Vector{Int}

  function yIterator(x::Vector{Int}, t::Int)
    z = new(t, x, zeros(Int, length(x) - t), zeros(Int, length(x)))
    return z
  end
end

function Base.iterate(F::yIterator, i::Vector{Int})
  if length(i) == 0
    return nothing
  end

  done = true

  for j in 1:length(i)
    if i[j] != F.x[j]
      done = false
    end
  end

  if done
    return nothing
  end

  if i[1] < F.x[1]
    i[1] = i[1] + 1
  else # the first one is as large as possible
    j = 0
    for j in 2:length(i)
      if i[j] < F.x[j]
        i[j] = i[j] + 1
        for k in j-1:-1:1
          i[k] = i[j]
        end
        break
      end
    end
  end

  for j in 1:F.t
    F.res[j] = i[j]
  end

  return copy(F.res), i
end

function Base.iterate(F::yIterator)
  i = ones(Int, F.t)

  if F.t == 0
    return copy(F.res), i
  end

  @inbounds if F.t > 0
    i[1] = 0
  end

  @inbounds if i[1] < F.x[1]
    i[1] = i[1] + 1
  else # the first one is as large as possible
    j = 0
    for j in 2:length(i)
      if i[j] < F.x[j]
        i[j] = i[j] + 1
        for k in j-1:-1:1
          i[k] = i[j]
        end
        break
      end
    end
  end

  @inbounds for j in 1:F.t
    F.res[j] = i[j]
  end

  return copy(F.res), i
end

Base.IteratorSize(::Type{yIterator}) = Base.SizeUnknown()

Base.eltype(::Type{yIterator}) = Vector{Int}

_subpartitions(x) = Iterators.flatten((yIterator(x, t) for t in 0:length(x)))

# Given a type y for the subgroup, we can iterator through all possible
# valid permutations. This is part (2) of Theorem 4.1.18.

struct SigmaIteratorGivenY{T}
  gen::T
end

@inline function _isvalid(s, t, x, y, sigma)
  for i in 1:t
    if y[i] > x[sigma[i]]
      return false
    end
  end
  for i in 1:(s-1)
    # TODO: Precompute the indices where they are equal
    if y[i] == y[i + 1]
      if sigma[i] < sigma[i + 1]
        return false
      end
    end
  end
  return true
end

function SigmaIteratorGivenY(s, x, y)
  t = something(findlast(!iszero, y), 0)
  SigmaIteratorGivenY(Iterators.filter(sigma -> _isvalid(s, t, x, y, sigma),
                                       (deepcopy(z.d) for z in AllPerms(s))))
end

Base.iterate(S::SigmaIteratorGivenY) = Base.iterate(S.gen)

Base.iterate(S::SigmaIteratorGivenY, s) = Base.iterate(S.gen, s)

Base.length(S::SigmaIteratorGivenY) = Base.length(S.gen)

Base.eltype(::Type{SigmaIteratorGivenY{T}}) where {T} = Vector{Int}

# for some reason this is type unstable.

# Finally we have to enumerate the possible matrices defining the generators
# of the subgroup (step (3)). There are two parts to this. First we compute,
# for a given sigma, the indice in the matrix.

function compute_indice(s, t, x, y, sigma)
  tau = Nemo.inv!(perm(sigma))
  indice = Tuple{Int, Int, Int}[]
  @inbounds for j in 1:t
    for i in 1:s
      if tau[i] > j
        if i < sigma[j] # case a)
          push!(indice, (i, j, 0))
        elseif i > sigma[j] && x[i] < y[j] #case b)
          push!(indice, (i, j, 1))
        elseif i > sigma[j] && x[i] >= y[j] # case c)
          push!(indice, (i, j, 2))
        end
      end
    end
  end
  return [( indice, tau )]
end

# Given sigma, we can iterate through all possible choices of integers
# c_{i,j}. To do this we collect the single ranges at the indice and the
# produce a product iterator.

mutable struct cIteratorGivenSigma{T}
  s::Int
  t::Int
  x::Vector{Int}
  y::Vector{Int}
  p::Int
  sigma::Vector{Int}
  tau::Vector{Int}
  indice::Vector{Tuple{Int, Int, Int}}
  it::T
end

function _cIteratorGivenSigma(s::Int, t::Int, x::Vector{Int},
                              y::Vector{Int}, p::IntegerUnion, sigma::Vector{Int})
  pp = Int(p)
  tau = Vector{Int}(Nemo.inv!(perm(sigma)))
  indice, it = getintervals(t, s, x, y, pp, sigma, tau)
  return cIteratorGivenSigma{typeof(it)}(s, t, x, y, pp, sigma, tau, indice, it)
end

function getintervals(t, s, x, y, p, sigma, tau)
  indice = Tuple{Int, Int, Int}[]
  ranges = UnitRange{Int}[]

  @inbounds for j in 1:t
    for i in 1:s
      if tau[i] > j
        if i < sigma[j] # case a)
          push!(indice, (i, j, 0))
          push!(ranges, 1:p^(y[j] - y[tau[i]]))
        elseif i > sigma[j] && x[i] < y[j] #case b)
          push!(indice, (i, j, 1))
          push!(ranges, 1:p^(x[i] - y[tau[i]]))
        elseif i > sigma[j] && x[i] >= y[j] # case c)
          push!(indice, (i, j, 2))
          push!(ranges, 1:p^(y[j] - y[tau[i]] - 1))
        end
      end
    end
  end
  if length(indice) == 0
    return indice, (Int[] for z in 1:1)
  end
  return indice, Base.product(ranges...)
end

Base.iterate(C::cIteratorGivenSigma) = Base.iterate(C.it)

Base.iterate(C::cIteratorGivenSigma, s) = Base.iterate(C.it, s)

Base.length(C::cIteratorGivenSigma) = Base.length(C.it)

Base.eltype(::Type{cIteratorGivenSigma{T}}) where {T} = Base.eltype(T)

# Now we have the y, the permutation sigma with inverse tau, the indices ind
# and the corresponding ranges describing the exponents in the generator
# matrix. Now get the matrix!

function get_matrix(s, t, ind, c, sigma, tau, p, x, y)
  M = zeros(Int, s, t)
  get_matrix!(M, s, t, ind, c, sigma, tau, p, x, y)
  return M
end

function get_matrix!(M, s, t, ind, c, sigma, tau, p, x, y)
  @inbounds for j in 1:t
    for i in 1:s
      if tau[i] < j
        M[i, j] = p^x[i]
      elseif tau[i] == j
        M[i,j] = p^(x[i] - y[j])
      end
    end
  end
  @inbounds for k in 1:length(ind)
    i, j, _case = ind[k]
    if _case == 0
      # case a)
      M[i, j] = c[k]*p^(x[i] - y[j])
    elseif _case == 1
      # case b)
      M[i, j] = c[k]
    elseif _case == 2
      # case c)
      M[i, j] = c[k] * p^(x[i] - y[j] + 1)
    end
  end
  return M
end

# Put everything together:
# Given the type x of a p-group G and a type y, this function iterates
# through all generating matrices of subgroups of type y.
# (The matrix is with respect to the canonical form
# G = Z/p^x[1] x .... x Z/p^x[r]

function _subgroup_type_iterator(x, y, p)
  @assert length(x) == length(y)
  s = length(x)
  t = something(findlast(!iszero, y), 0)

  # have to treat the empty y separately


  if any(y[i] > x[i] for i in 1:length(x))
    return (x for x in 1:-1)
  end

  if t == 0
    return (x for x in [zeros(Int, s, 0)])
  elseif x == y
    return (x for x in [Matrix{Int}(I, s, s)])
  end

  return (get_matrix(s, t, f[1], c, sigma, f[2], p, x, y)
          for sigma in SigmaIteratorGivenY(s, x, y)
          for f in compute_indice(s, t, x, y, sigma)
          for c in _cIteratorGivenSigma(s, t, x, y, p, sigma))
end

# Same as above but for all subgroups.
function _subgroup_iterator(x, p, types = (y for t in 0:length(x)
                                             for y in yIterator(x, t)))
  s = length(x)
  # Flatten just concatenates two iterators.
  #return #Iterators.flatten(([Array{Int}(s, 0)],
  return Iterators.flatten((_subgroup_type_iterator(x, y, p) for y in types))
end

# Given a matrix M and a group G, this function constructs elements from
# the columns of M. The indice allows to handle the case, where the
# generators of G correspond to a permutation of the rows of M.
function _matrix_to_elements(G::FinGenAbGroup, M::Matrix{Int},
                             indice::Vector{Int} = collect(1:ngens(G)))
  numgenssub = size(M, 2)
  numgen = ngens(G)
  r = size(M, 1)
  z = Array{FinGenAbGroupElem}(undef, numgenssub)
  v = zeros(Int, numgen)
  for i in 1:numgenssub
    for j in 1:r
      v[indice[j]] = M[j, i]
    end
    z[i] = G(v)
    for j in 1:numgen
      v[j] = 0
    end
  end
  return z
end

# Given a finitely generated p-group G in Smith normal form, and a type t,
# this function returns an iterator, which iterates over generators of
# subgroups of type t. If t = [-1], then there is no restriction on the type.
function __psubgroups_gens(G::FinGenAbGroup, p::IntegerUnion,
                           order, index, t::Vector{Int})
  @assert isfinite(G)
  @assert is_snf(G)
  # The SNF can contain 1's and 0's
  # Have to help inference here with the explicit type
  x = Tuple{Int, Int}[ (valuation(G.snf[i], p), i)
                       for i in 1:length(G.snf) if G.snf[i] > 1]
  reverse!(x)
  Gtype = [ t[1] for t in x ]
  indice = [ t[2] for t in x ]
  if length(t) > length(Gtype)
    return ( i for i in 1:-1)
  end
  # x is the "type" of the p-group G as a partition
  if length(t) == 1 && t[1] == -1
    return (_matrix_to_elements(G, M, indice) for
            M in _subgroup_iterator(Gtype, p))
  else
    t = vcat(t, zeros(Int, length(x) - length(t)))
    return  (_matrix_to_elements(G, M, indice) for
             M in _subgroup_type_iterator(Gtype, t, p))
  end
  return Gtype, indice
end

function __psubgroups_gens(G::FinGenAbGroup, p::IntegerUnion,
                           order, index, types)
  @assert isfinite(G)
  @assert is_snf(G)
  # The SNF can contain 1's and 0's
  # Have to help inference here with the explicit type
  x = Tuple{Int, Int}[ (valuation(G.snf[i], p), i)
                       for i in 1:length(G.snf) if G.snf[i] > 1]
  reverse!(x)
  Gtype = [ t[1] for t in x ]
  indice = [ t[2] for t in x ]
  # x is the "type" of the p-group G as a partition
  if order != -1
    v = valuation(order, p)
    adjusted_types = (vcat(t, zeros(Int, length(x) - length(t)))
                      for t in types if sum(t) == v)
  elseif index != -1
    v = sum(Gtype) - valuation(index, p)
    adjusted_types = (vcat(t, zeros(Int, length(x) - length(t)))
                      for t in types if sum(t) == v)
  else
    adjusted_types = (vcat(t, zeros(Int, length(x) - length(t))) for t in types)
  end

  return  (_matrix_to_elements(G, M, indice)
           for M in _subgroup_iterator(Gtype, p, adjusted_types))
  return Gtype, indice
end

function __psubgroups_gens(G::FinGenAbGroup, p::IntegerUnion, order, index)
  @assert isfinite(G)
  @assert is_snf(G)
  # The SNF can contain 1's and 0's
  # Have to help inference here with the explicit type
  x = Tuple{Int, Int}[ (valuation(G.snf[i], p), i)
                       for i in 1:length(G.snf) if G.snf[i] > 1]
  reverse!(x)
  Gtype = [ t[1] for t in x ]
  indice = [ t[2] for t in x ]
  types = _subpartitions(Gtype)
  # x is the "type" of the p-group G as a partition
  if order != -1
    v = valuation(order, p)
    adjusted_types = (vcat(t, zeros(Int, length(x) - length(t)))
                      for t in types if sum(t) == v)
  elseif index != -1
    v = sum(Gtype) - valuation(index, p)
    adjusted_types = (vcat(t, zeros(Int, length(x) - length(t)))
                      for t in types if sum(t) == v)
  else
    adjusted_types = (vcat(t, zeros(Int, length(x) - length(t))) for t in types)
  end
  return  (_matrix_to_elements(G, M, indice)
           for M in _subgroup_iterator(Gtype, p, adjusted_types))
end

# Same as above but now for arbitrary p-groups
function _psubgroups_gens(G::FinGenAbGroup, p, t, order, index)
  if is_snf(G)
    if t == [-1]
      return __psubgroups_gens(G, p, order, index)
    else
      return __psubgroups_gens(G, p, order, index, t)
    end
  else
    S, mS = snf(G)
    if t == [-1]
      return ( map(x -> image(mS, x)::FinGenAbGroupElem, z)
               for z in __psubgroups_gens(S, p, order, index))
    else
      return ( map(x -> image(mS, x)::FinGenAbGroupElem, z)
               for z in __psubgroups_gens(S, p, order, index, t))
    end
  end
end


function _psubgroups_gens_quotype(G::FinGenAbGroup, p, t, order, index)
  if is_snf(G)
    x = Tuple{Int, Int}[ (valuation(G.snf[i], p), i)
                       for i in 1:length(G.snf) if G.snf[i] > 1]
    reverse!(x)
    Gtype = [ t[1] for t in x ]
    indice = [ t[2] for t in x ]
    types = _subpartitions(Gtype)
    filtered_types = Iterators.filter(z -> sum(z) == sum(Gtype) - sum(t), types)
    return __psubgroups_gens(G, p, order, index, filtered_types)
  else
    S, mS = snf(G)
    return ( map(x -> image(mS, x)::FinGenAbGroupElem, z)
             for z in _psubgroups_gens_quotype(S, p, t, order, index))
  end
end

function _ptype(G, p)
  Gsnf = domain(snf(G)[2])
  x = Int[ valuation(Gsnf.snf[i], p)
                       for i in 1:length(Gsnf.snf) if Gsnf.snf[i] > 1]
  reverse!(x)
  t = findlast(!iszero, x)
  if t === nothing
    return x[1:0]
  else
    return x[1:t]
  end
end

# Same as above but now allow a function to be applied to the output
function _psubgroups(G::FinGenAbGroup, p::IntegerUnion; subtype = [-1],
                                                              quotype = [-1],
                                                              order = -1,
                                                              index = -1,
                                                              fun = sub)
  P, mP = sylow_subgroup(G, p, false)

  if quotype != [-1]
    return ( fun(G, map(mP, z))
            for z in _psubgroups_gens_quotype(P, p, quotype, order, index)
            if _ptype(quo(G, map(mP, z), false)[1], p) == quotype)
  end

  return ( fun(G, map(mP, z)) for z in _psubgroups_gens(P, p, subtype, order, index))
end

# We use a custom type for the iterator to have pretty printing.
mutable struct pSubgroupIterator{F, T, E}
  G::FinGenAbGroup
  p::ZZRingElem
  subtype::Vector{Int}
  quotype::Vector{Int}
  index::ZZRingElem
  order::ZZRingElem
  fun::F
  it::T
end

function Base.show(io::IO, I::pSubgroupIterator)
  print(io, "p-subgroup iterator of \n$(I.G)\n")

  print(io, "p: $(I.p)\n")

  if I.subtype == [-1]
    print(io, "subgroup type: any\n")
  else
    print(io, "subgroup type: $(I.subtype)\n")
  end

  if I.quotype == [-1]
    print(io, "quotient type: any\n")
  else
    print(io, "quotient type: $(I.quotype)\n")
  end

  if I.index == -1
    print(io, "index: any\n")
  else
    print(io, "index: $(I.index)\n")
  end

  if I.order == -1
    print(io, "order: any\n")
  else
    print(io, "order: $(I.order)\n")
  end

  if I.fun != sub
    print(io, "function: $(I.fun)")
  end
end

function pSubgroupIterator(G::FinGenAbGroup, p::IntegerUnion;
                                           subtype::Vector{Int} = [-1],
                                           quotype::Vector{Int} = [-1],
                                           index::Union{ZZRingElem, Int} = -1,
                                           order::Union{ZZRingElem, Int} = -1,
                                           fun = sub)
  if index == p
    it = index_p_subgroups(G, p, fun)
  else
    it = _psubgroups(G, p; subtype = subtype, quotype = quotype,
                           fun = fun, index = index, order = order)
  end

  E = Core.Compiler.return_type(fun, Tuple{FinGenAbGroup, Vector{FinGenAbGroupElem}})

  z = pSubgroupIterator{typeof(fun), typeof(it), E}(G, ZZRingElem(p), subtype, [-1],
                                                    ZZRingElem(index), ZZRingElem(order), fun, it)
  return z
end

@doc raw"""
    psubgroups(g::FinGenAbGroup, p::Integer;
               subtype = :all,
               quotype = :all,
               index = -1,
               order = -1)

Return an iterator for the subgroups of $G$ of the specific form. Note that
`subtype` (and `quotype`) is the type of the subgroup as an abelian $p$-group.
"""
function psubgroups(G::FinGenAbGroup, p::IntegerUnion; subtype = :all,
                                                             quotype = :all,
                                                             index =  -1,
                                                             order = -1,
                                                             fun = sub)

  options = Int16[ subtype != :all, quotype != :all, index != -1, order != -1 ]

  if sum(options) > 1
    error("Currently only one non-default parameter is supported.")
  end

  if subtype == :all
    _subtype = [-1]
  else
    for i in 1:(length(subtype) - 1)
      if subtype[i + 1] > subtype[i]
        error("Subtype must be a partition")
      end
    end
    _subtype = subtype
  end

  if quotype == :all
    _quotype = [-1]
  else
    for i in 1:(length(quotype) - 1)
      if quotype[i + 1] > quotype[i]
        error("Subtype must be a partition")
      end
    end
    _quotype = quotype
  end

  return pSubgroupIterator(G, p; subtype = _subtype, quotype = _quotype, order = order, index = index,
                                 fun = fun)
end

Base.iterate(S::pSubgroupIterator) = Base.iterate(S.it)

Base.iterate(S::pSubgroupIterator, st) = Base.iterate(S.it, st)

Base.eltype(::Type{pSubgroupIterator{F, T, E}}) where {F, T, E} = E

Base.IteratorSize(::Type{pSubgroupIterator{F, T, E}}) where {F, T, E} = Base.SizeUnknown()

################################################################################
#
#  Subgroup enumeration
#
################################################################################

mutable struct SubgroupIterator{F, T, E}
  G::FinGenAbGroup
  subtype::Vector{Int}
  quotype::Vector{Int}
  index::ZZRingElem
  order::ZZRingElem
  fun::F
  it::T
end

function Base.show(io::IO, I::SubgroupIterator)
  print(io, "p-subgroup iterator of \n$(I.G)\n")

  if I.subtype == [-1]
    print(io, "subgroup type: any\n")
  else
    print(io, "subgroup type: $(I.subtype)\n")
  end

  if I.quotype == [-1]
    print(io, "quotient type: any\n")
  else
    print(io, "quotient type: $(I.quotype)\n")
  end

  if I.index == -1
    print(io, "index: any\n")
  else
    print(io, "index: $(I.index)\n")
  end

  if I.order == -1
    print(io, "order: any\n")
  else
    print(io, "order: $(I.order)\n")
  end

  if I.fun != sub
    print(io, "function: $(I.fun)")
  end
end

Base.iterate(S::SubgroupIterator) = Base.iterate(S.it)

Base.iterate(S::SubgroupIterator, s) = Base.iterate(S.it, s)

Base.IteratorSize(::Type{SubgroupIterator{F, T, E}}) where {F, T, E} = Base.SizeUnknown()

Base.eltype(::Type{SubgroupIterator{F, T, E}}) where {F, T, E} = E

function _subgroups_gens(G::FinGenAbGroup, subtype::Vector{S} = [-1],
                         quotype = [-1], suborder = -1,
                         subindex = -1) where S <: IntegerUnion
  primes = ZZRingElem[]

  pgens = []

  if quotype != [-1]

    fac = factor(order(G))

    for (p, e) in fac
      if !iszero(mod(order(G), p))
        error("no subgroup exists")
      end
      ptype = map(l -> valuation(l, p), quotype)
      filter!( z -> z > 0, ptype)
      sort!(ptype, rev = true)
      T = psubgroups(G, Int(p), quotype = ptype, fun = (g, m) -> sub(g, m, false))
      genss = ( FinGenAbGroupElem[ t[2](x) for x in gens(t[1]) ] for t in T )
      push!(pgens, genss)
    end
  elseif subtype != [-1]
    for l in subtype
      fac = factor(ZZRingElem(l))
      for (p, e) in fac
        push!(primes, p)
      end
    end

    primes = unique(primes)

    for p in primes
      if !iszero(mod(order(G), p))
        error("no subgroup exists")
      end
      ptype = map(l -> valuation(l, p), subtype)
      filter!( z -> z > 0, ptype)
      sort!(ptype, rev = true)
      T = psubgroups(G, Int(p), subtype = ptype, fun = (g, m) -> sub(g, m, false))
      genss = ( FinGenAbGroupElem[ t[2](x) for x in gens(t[1]) ] for t in T )
      push!(pgens, genss)
    end
  elseif suborder != -1 || subindex != -1
    # Do the order/index at the same time
    if subindex != -1
      _suborder = divexact(order(G), subindex)
    else
      _suborder = suborder
    end
    fac = factor(ZZRingElem(_suborder))
    for (p, e) in fac
      orderatp = p^e
      T = psubgroups(G, Int(p), order = orderatp, fun = (g, m) -> sub(g, m, false))
      genss = ( FinGenAbGroupElem[ t[2](x) for x in gens(t[1]) ] for t in T )
      push!(pgens, genss)
    end
  else
    fac = factor(order(G))
    for (p, e) in fac
      T = psubgroups(G, Int(p), fun = (g, m) -> sub(g, m, false))
      genss = ( FinGenAbGroupElem[ t[2](x) for x in gens(t[1]) ] for t in T )
      push!(pgens, genss)
    end
  end

  final_it = ( vcat(c...) for c in Iterators.product(pgens...))
  return final_it
end

# Same as above but now allow a function to be applied to the output
function _subgroups(G::FinGenAbGroup; subtype = [-1], quotype = [-1], order = -1,
                                    index = -1, fun = sub)
  return ( fun(G, convert(Vector{FinGenAbGroupElem}, z)) for z in _subgroups_gens(G, subtype, quotype, order, index))
end


function SubgroupIterator(G::FinGenAbGroup; subtype::Vector{Int} = [-1],
                                          quotype::Vector{Int} = [-1],
                                          index::Union{ZZRingElem, Int} = -1,
                                          order::Union{ZZRingElem, Int} = -1,
                                          fun = sub)

  if index != -1 && is_prime(ZZRingElem(index))
    it = index_p_subgroups(G, ZZRingElem(index), fun)
  else
    it = _subgroups(G; subtype = subtype, quotype = quotype,
                       fun = fun, index = index, order = order)
  end

  E = Core.Compiler.return_type(fun, Tuple{FinGenAbGroup, Vector{FinGenAbGroupElem}})

  z = SubgroupIterator{typeof(fun), typeof(it), E}(G, subtype, quotype,
                                                   ZZRingElem(index), ZZRingElem(order),
                                                   fun, it)
  return z
end

@doc raw"""
    subgroups(g::FinGenAbGroup;
              subtype = :all ,
              quotype = :all,
              index = -1,
              order = -1)

Return an iterator for the subgroups of $G$ of the specific form.
"""
function subgroups(G::FinGenAbGroup; subtype = :all,
                                   quotype = :all,
                                   index =  -1,
                                   order = -1,
                                   fun = sub)

  # Handle the parameters

  options = Int16[ subtype != :all, quotype != :all, order != -1, index != -1]

  if mod(Hecke.order(G), index) != 0
    error("Index must divide the group order")
  end

  if mod(Hecke.order(G), order) != 0
    error("Index must divide the group order")
  end

  if sum(options) > 1
    error("Currently only one non-default parameter is supported.")
  end

  if subtype == :all
    _subtype = [-1]
  else
    _subtype = subtype
  end

  if quotype == :all
    _quotype = [-1]
  else
    _quotype = quotype
  end

  return SubgroupIterator(G; subtype = _subtype, quotype = _quotype, order = order, index = index,
                                 fun = fun)
end

################################################################################
#
#  Minimal subgroups
#
################################################################################

@doc doc"""
    minimal_subgroups(G::FinGenAbGroup) -> Vector{Tuple{FinGenAbGroup, Map}}

Return the minimal subgroups of $G$.
"""
function minimal_subgroups(G::FinGenAbGroup, add_to_lattice::Bool = false)
  @req isfinite(G) "Group must be finite"
  o = order(G)
  l = prime_divisors(o)
  res = Vector{Tuple{FinGenAbGroup, FinGenAbGroupHom}}()
  for p in l
    append!(res, psubgroups(G, p, order = p, fun = (x, m) -> sub(x, m, add_to_lattice)))
  end
  return res
end
