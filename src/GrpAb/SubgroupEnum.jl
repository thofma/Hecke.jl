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

export psubgroups, index_p_subgroups, subgroups

################################################################################
#
#  Enumeration of subgroups of index p
#
################################################################################

function index_p_subgroups(A::GrpAbFinGen, p::Integer)
  return index_p_subgroups(A, fmpz(p))
end

mutable struct IndexPSubgroups{S, T}
  p::Int
  n::UInt
  st::Int
  mp::S
  c::fmpz_mat
  mthd::T

  function IndexPSubgroups{T}(A::GrpAbFinGen, p::fmpz, mthd::T = sub) where {T}
    if order(A) % p != 0
      r = new{Generic.IdentityMap{GrpAbFinGen}, T}()
      r.n = 0
      return r
    end
    s, ms = snf(A)  # ms: A -> s
    r = new{typeof(inv(ms)), T}()
    @assert s.issnf
    r.p = Int(p)
    r.mp = inv(ms)
    i=1
    while s.snf[i] % p != 0
      i += 1
    end
    r.st = i
    r.n = UInt(div(fmpz(p)^(length(s.snf)-i+1) - 1, fmpz(p)-1))
    r.c = zero_matrix(FlintZZ, length(s.snf), length(s.snf))
    r.mthd = mthd
    return r
  end
end

function index_p_subgroups(A::GrpAbFinGen, p::Union{fmpz, Integer}, mthd::T = sub) where {T}
  q = fmpz(p)
  @assert isprime(q)
  return IndexPSubgroups{T}(A, q, mthd)

  #a subgroup of index p corresponds to a HNF with exactly one p on the
  #diagonal - and the other entries arbitrary reduced.
  #so it should be 1 + p + p^2 + + p^(n-1) = ((p^n)-1)/(p-1) many
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
  for k=1:rows(c)
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
  gen = [s.mp\(codomain(s.mp)(sub(c, l:l, 1:cols(c)))) for l=1:rows(c)]
  return s.mthd(domain(s.mp), gen)
end

function Base.start(s::IndexPSubgroups)
  return UInt(0)
end

function Base.next(s::IndexPSubgroups, i::UInt)
  return index_to_group(s, i), i+1
end

function Base.length(s::IndexPSubgroups)
  return s.n
end

function Base.done(s::IndexPSubgroups, i::UInt)
  return i>=s.n
end

#=
example:
 julia> sg = index_p_subgroups(GrpAbFinGen([3,3,3,3]), 3)
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
  x::Array{Int, 1}
  nulls::Array{Int, 1}
  res::Array{Int, 1}

  function yIterator(x::Array{Int, 1}, t::Int)
    z = new(t, x, zeros(Int, length(x) - t), zeros(Int, length(x)))
    return z
  end
end

Base.start(F::yIterator) = (z = ones(Int, F.t); F.t > 0 ? z[1] = 0 : nothing; return z)

function Base.next(F::yIterator, i::Array{Int, 1})
  if length(i) == 0
    return copy(F.res), copy(F.x) # this will make it abort
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

function Base.done(F::yIterator, i::Array{Int, 1})
  # note that this is a hack to make the case t = 0 work
  if length(i) == 0
    return false
  end
  for j in 1:length(i)
    if i[j] != F.x[j]
      return false
    end
  end
  return true
end

Base.iteratorsize(::Type{yIterator}) = Base.SizeUnknown()

Base.eltype(::Type{yIterator}) = Array{Int, 1}

_subpartitions(x) = Iterators.flatten(( yIterator(x, t) for t in 0:length(x)))

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
    # TODO: Precompute the indicies where they are equal
    if y[i] == y[i + 1]
      if sigma[i] < sigma[i + 1]
        return false
      end
    end
  end
  return true
end

function SigmaIteratorGivenY(s, x, y)
  t = findlast(!iszero, y)
  SigmaIteratorGivenY(Iterators.filter(sigma -> _isvalid(s, t, x, y, sigma),
                                       Nemo.AllPerms(s)))
end

Base.start(S::SigmaIteratorGivenY) = Base.start(S.gen)

Base.next(S::SigmaIteratorGivenY, s) = Base.next(S.gen, s)

Base.done(S::SigmaIteratorGivenY, s) = Base.done(S.gen, s)

Base.length(S::SigmaIteratorGivenY) = Base.length(S.gen)

Base.iteratorsize(::Type{SigmaIteratorGivenY{T}}) where {T} = Base.iteratorsize(T)

Base.eltype(::Type{SigmaIteratorGivenY{T}}) where {T} = Array{Int, 1}

# for some reason this is type unstable.

# Finally we have to enumerate the possible matrices defining the generators
# of the subgroup (step (3)). There are two parts to this. First we compute,
# for a given sigma, the indice in the matrix.

function compute_indice(s, t, x, y, sigma)
  tau = Nemo.inv!(perm(sigma))
  indice = Tuple{Int, Int, Int}[]
  for j in 1:t
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

# Given sigma, we can iteraterate through all possible choices of intergers
# c_{i,j}. To do this we collect the single ranges at the indice and the
# produce a product iterator.

mutable struct cIteratorGivenSigma{T}
  s::Int
  t::Int
  x::Array{Int, 1}
  y::Array{Int, 1}
  p::Int
  sigma::Array{Int, 1}
  tau::Array{Int, 1}
  indice::Array{Tuple{Int, Int, Int}, 1}
  it::T
end

function _cIteratorGivenSigma(s::Int, t::Int, x::Array{Int, 1},
                              y::Array{Int, 1}, p::Int, sigma::Array{Int, 1})
  tau = Nemo.inv!(perm(sigma))
  indice, it = getintervals(t, s, x, y, p, sigma, tau)
  return cIteratorGivenSigma{typeof(it)}(s, t, x, y, p, sigma, tau, indice, it)
end

function getintervals(t, s, x, y, p, sigma, tau)
  indice = Tuple{Int, Int, Int}[]
  ranges = UnitRange{Int}[]

  for j in 1:t
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
    return indice, (z for z in 2:1)
  end
  return indice, Base.product(ranges...)
end

Base.start(C::cIteratorGivenSigma) = Base.start(C.it)

Base.next(C::cIteratorGivenSigma, s) = Base.next(C.it, s)

Base.done(C::cIteratorGivenSigma, s) = Base.done(C.it, s)

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
  for j in 1:t
    for i in 1:s
      if tau[i] < j
        M[i, j] = p^x[i]
      elseif tau[i] == j
        M[i,j] = p^(x[i] - y[j])
      end
    end
  end
  for k in 1:length(ind)
    i = ind[k][1]
    j = ind[k][2]
    _case = ind[k][3]
    if _case == 0 # case a)
      M[i, j] = c[k]*p^(x[i] - y[j])
    elseif _case == 1 # case b)
      M[i, j] = c[k]
    elseif _case == 2 # case c)
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
  t = findlast(!iszero, y)

  # have to treat the empty y separately

  if any( y[i] > x[i] for i in 1:length(x))
    return ( x for x in 1:-1)
  end

  if t == 0
    return ( x for x in [zeros(Int, s, 0)])
  elseif x == y
    return ( x for x in [eye(Int, s)])
  end

  return (get_matrix(s, t, f[1], c, sigma, f[2], p, x, y)
          for sigma in SigmaIteratorGivenY(s, x, y)
          for f in compute_indice(s, t, x, y, sigma)
          for c in _cIteratorGivenSigma(s, t, x, y, p, sigma))
end

# Same as above but for all subgroups.
function _subgroup_iterator(x, p, types = ( y for t in 0:length(x)
                                           for y in yIterator(x, t)))
  s = length(x)
  # Flatten just concatenates two iterators.
  #return #Iterators.flatten(([Array{Int}(s, 0)],
  return Iterators.flatten(( _subgroup_type_iterator(x, y, p) for y in types))
end

# Given a matrix M and a group G, this function constructs elements from
# the columns of M. The indice allows to handle the case, where the
# generators of G correspond to a permutation of the rows of M.
function _matrix_to_elements(G::GrpAbFinGen, M::Array{Int, 2},
                             indice::Array{Int, 1} = collect(1:ngens(G)))
  numgenssub = size(M, 2)
  numgen = ngens(G)
  r = size(M, 1)
  z = Array{GrpAbFinGenElem}(numgenssub)
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
function __psubgroups_gens(G::GrpAbFinGen, p::Union{fmpz, Integer},
                           order, index, t::Array{Int, 1})
  @assert isfinite(G)
  @assert issnf(G)
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

function __psubgroups_gens(G::GrpAbFinGen, p::Union{fmpz, Integer},
                           order, index, types)
  @assert isfinite(G)
  @assert issnf(G)
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

function __psubgroups_gens(G::GrpAbFinGen, p::Union{Integer, fmpz}, order, index)
  @assert isfinite(G)
  @assert issnf(G)
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
function _psubgroups_gens(G::GrpAbFinGen, p, t, order, index)
  if issnf(G)
    if t == [-1]
      return __psubgroups_gens(G, p, order, index)
    else
      return __psubgroups_gens(G, p, order, index, t)
    end
  else
    S, mS = snf(G)
    if t == [-1]
      return ( map(x -> image(mS, x)::GrpAbFinGenElem, z)
               for z in __psubgroups_gens(S, p, order, index))
    else
      return ( map(x -> image(mS, x)::GrpAbFinGenElem, z)
               for z in __psubgroups_gens(S, p, order, index, t))
    end
  end
end


function _psubgroups_gens_quotype(G::GrpAbFinGen, p, t, order, index)
  if issnf(G)
  #=
    v=[divexact(G.snf[end], G.snf[i]) for i=1:ngens(G)]
    return (_dualize(G, x, v) for x in _psubgroups_gens(G, p, t, order, index))
  =#
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
    return ( map(x -> image(mS, x)::GrpAbFinGenElem, z)
             for z in _psubgroups_gens_quotype(S, p, t, order, index))
  end
end

function _dualize(G::GrpAbFinGen, x::Array{GrpAbFinGenElem,1}, v::Array{fmpz,1})

  if isempty(x)
    return gens(G)
  end
  @assert parent(x[1])==G
  M = zero_matrix(FlintZZ, ngens(G), length(x))
  for i = 1:length(x)
    for j = 1:ngens(G)
      M[j,i] = (x[i][j])*v[j]
    end
  end
  D = DiagonalGroup([G.snf[end] for i = 1:length(x)])
  f = GrpAbFinGenMap(G,D,M)
  K = kernel_as_submodule(f)
  return GrpAbFinGenElem[G(view(K,i:i,1:cols(K))) for i=1:rows(K)]
  
end

function _ptype(G, p)
  Gsnf = domain(snf(G)[2])
  x = Int[ valuation(Gsnf.snf[i], p)
                       for i in 1:length(Gsnf.snf) if Gsnf.snf[i] > 1]
  reverse!(x)
  t = findlast(!iszero, x)
  return x[1:t]
end

# Same as above but now allow a function to be applied to the output
function _psubgroups(G::GrpAbFinGen, p::Union{Integer, fmpz}; subtype = [-1],
                                                              quotype = [-1],
                                                              order = -1,
                                                              index = -1,
                                                              fun = sub)
  P, mP = psylow_subgroup(G, p, false)

  if quotype != [-1]
    return ( fun(G, map(mP, z))
            for z in _psubgroups_gens_quotype(P, p, quotype, order, index)
            if _ptype(quo(G, map(mP, z), false)[1], p) == quotype)
  end

  return ( fun(G, map(mP, z)) for z in _psubgroups_gens(P, p, subtype, order, index))
end



# We use a custom type for the iterator to have pretty printing.
mutable struct pSubgroupIterator{F, T, E}
  G::GrpAbFinGen
  p::fmpz
  subtype::Array{Int, 1}
  quotype::Array{Int, 1}
  index::fmpz
  order::fmpz
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

function pSubgroupIterator(G::GrpAbFinGen, p::Union{fmpz, Integer};
                                           subtype::Array{Int, 1} = [-1],
                                           quotype::Array{Int, 1} = [-1],
                                           index::Union{fmpz, Int} = -1,
                                           order::Union{fmpz, Int} = -1,
                                           fun = sub)
  if index == p
    it = index_p_subgroups(G, p, fun)
  else
    it = _psubgroups(G, p; subtype = subtype, quotype = quotype,
                           fun = fun, index = index, order = order)
  end
  E = Core.Inference.return_type(fun, (GrpAbFinGen, Array{GrpAbFinGenElem, 1}))
  z = pSubgroupIterator{typeof(fun), typeof(it), E}(G, fmpz(p), subtype, [-1],
                                                    fmpz(index), fmpz(order), fun, it)
  return z
end

doc"""
    psubgroups(g::GrpAbFinGen, p::Integer;
               subtype = :all,
               quotype = :all,
               index = -1,
               order = -1)

Return an iterator for the subgroups of $G$ of the specific form. Note that
`subtype` (and `quotype`) is the type of the subgroup as an abelian $p$-group.
"""
function psubgroups(G::GrpAbFinGen, p::Union{Integer, fmpz}; subtype = :all,
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

Base.start(S::pSubgroupIterator) = Base.start(S.it)

Base.next(S::pSubgroupIterator, s) = Base.next(S.it, s)

Base.done(S::pSubgroupIterator, s) = Base.done(S.it, s)

Base.iteratorsize(::Type{pSubgroupIterator{F, T, E}}) where {F, T, E} =
      Base.SizeUnknown()

Base.eltype(::Type{pSubgroupIterator{F, T, E}}) where {F, T, E} = E

Base.length(S::pSubgroupIterator) = Base.length(S.it)

################################################################################
#
#  Subgroup enumeration
#
################################################################################

mutable struct SubgroupIterator{F, T, E}
  G::GrpAbFinGen
  subtype::Array{Int, 1}
  quotype::Array{Int, 1}
  index::fmpz
  order::fmpz
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

Base.start(S::SubgroupIterator) = Base.start(S.it)

Base.next(S::SubgroupIterator, s) = Base.next(S.it, s)

Base.done(S::SubgroupIterator, s) = Base.done(S.it, s)

Base.length(S::SubgroupIterator) = Base.length(S.it)

Base.iteratorsize(::Type{SubgroupIterator{F, T, E}}) where {F, T, E} =
    Base.SizeUnknown()

Base.eltype(::Type{SubgroupIterator{F, T, E}}) where {F, T, E} = E

function _subgroups_gens(G::GrpAbFinGen, subtype::Array{S, 1} = [-1],
                         quotype = [-1], suborder = -1,
                         subindex = -1) where S <: Union{Integer, fmpz}
  primes = fmpz[]

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
      genss = ( [ t[2](x) for x in gens(t[1]) ] for t in T )
      push!(pgens, genss)
    end
  elseif subtype != [-1]
    for l in subtype
      fac = factor(fmpz(l))
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
      genss = ( [ t[2](x) for x in gens(t[1]) ] for t in T )
      push!(pgens, genss)
    end
  elseif suborder != -1 || subindex != -1
    # Do the order/index at the same time
    if subindex != -1
      _suborder = divexact(order(G), subindex)
    else
      _suborder = suborder
    end
    fac = factor(fmpz(_suborder))
    for (p, e) in fac
      orderatp = p^e
      T = psubgroups(G, Int(p), order = orderatp, fun = (g, m) -> sub(g, m, false))
      genss = ( [ t[2](x) for x in gens(t[1]) ] for t in T )
      push!(pgens, genss)
    end
  else
    fac = factor(order(G))
    for (p, e) in fac
      T = psubgroups(G, Int(p), fun = (g, m) -> sub(g, m, false))
      genss = ( [ t[2](x) for x in gens(t[1]) ] for t in T )
      push!(pgens, genss)
    end
  end

  final_it = ( vcat(c...) for c in Iterators.product(pgens...))
  return final_it
end

# Same as above but now allow a function to be applied to the output
function _subgroups(G::GrpAbFinGen; subtype = [-1], quotype = [-1], order = -1,
                                    index = -1, fun = sub)
  return ( fun(G, z) for z in _subgroups_gens(G, subtype, quotype, order, index))
end


function SubgroupIterator(G::GrpAbFinGen; subtype::Array{Int, 1} = [-1],
                                          quotype::Array{Int, 1} = [-1],
                                          index::Union{fmpz, Int} = -1,
                                          order::Union{fmpz, Int} = -1,
                                          fun = sub)

  if index != -1 && isprime(fmpz(index))
    it = index_p_subgroups(G, fmpz(index), fun)
  else
    it = _subgroups(G; subtype = subtype, quotype = quotype,
                       fun = fun, index = index, order = order)
  end

  E = Core.Inference.return_type(fun, (GrpAbFinGen, Array{GrpAbFinGenElem, 1}))
  z = SubgroupIterator{typeof(fun), typeof(it), E}(G, subtype, quotype,
                                                   fmpz(index), fmpz(order),
                                                   fun, it)
  return z
end

doc"""
    subgroups(g::GrpAbFinGen;
              subtype = :all ,
              quotype = :all,
              index = -1,
              order = -1)

Return an iterator for the subgroups of $G$ of the specific form.
"""
function subgroups(G::GrpAbFinGen; subtype = :all,
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
