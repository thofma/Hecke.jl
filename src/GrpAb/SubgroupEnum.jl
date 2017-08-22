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

Base.start(F::yIterator) = (z = ones(Int, F.t); z[1] = 0; return z)

function Base.next(F::yIterator, i::Array{Int, 1})
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
      end
    end
  end
  for j in 1:F.t
    F.res[j] = i[j]
  end
  return F.res, i
end

function Base.done(F::yIterator, i::Array{Int, 1})
  for j in 1:length(i)
    if i[j] != F.x[j]
      return false
    end
  end
  return true
end

Base.iteratorsize(::Type{yIterator}) = Base.SizeUnknown()

Base.eltype(::Type{yIterator}) = Array{Int, 1}

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

SigmaIteratorGivenY(s, t, x, y) = SigmaIteratorGivenY(Iterators.filter(sigma -> _isvalid(s, t, x, y, sigma), Nemo.AllPerms(s)))

Base.start(S::SigmaIteratorGivenY) = Base.start(S.gen)

Base.next(S::SigmaIteratorGivenY, s) = Base.next(S.gen, s)

Base.done(S::SigmaIteratorGivenY, s) = Base.done(S.gen, s)

Base.iteratorsize(::Type{SigmaIteratorGivenY}) = Base.SizeUnknown()

Base.eltype(::Type{SigmaIteratorGivenY}) = Array{Int, 1}

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

function _cIteratorGivenSigma(s::Int, t::Int, x::Array{Int, 1}, y::Array{Int, 1}, p::Int, sigma::Array{Int, 1})
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
  return indice, Base.product(ranges)
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
  M = Array{Int}(s, t)
  get_matrix!(M, s, t, ind, c, sigma, tau, p, x, y)
  return M
end

function get_matrix!(M, s, t, ind::Array{Tuple{Int, Int, Int}, 1}, c, sigma, tau, p, x, y)
  @show M
  @show s
  @show t
  @show ind
  @show c
  @show sigma
  @show tau
  @show p
  @show x
  @show y
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
  s = length(x)
  t = findlast(!iszero, y)

  # have to treat the empty y separately
  if t == 0
    return ( x for x in [zeros(Int, s, 0)])
  end

  return ((println(f); get_matrix(s, t, f[1], c, sigma, f[2], p, x, y))
          for sigma in SigmaIteratorGivenY(s, t, x, y)
          for f in compute_indice(s, t, x, y, sigma)
          for c in _cIteratorGivenSigma(s, t, x, y, p, sigma))
end

# Same as above but for all subgroups.
function _subgroup_iterator(x, p)
  s = length(x)
  # We have to treat the trivial group separately.
  # Flatten just concatenates two iterators.
  return Iterators.flatten(([Array{Int}(s, 0)], (get_matrix(s, t, f[1], c, sigma, f[2], p, x, y)
          for t in 1:s
          for y in yIterator(x, t)
          for sigma in SigmaIteratorGivenY(s, t, x, y)
          for f in compute_indice(s, t, x, y, sigma)
          for c in cIteratorGivenSigma(s, t, x, y, p, sigma))))
end

function _matrix_to_generators(G::GrpAbFinGen, M::Array{Int, 2}, indices::Array{Int, 1} = collect(1:ngens(G)))
  numgenssub = size(M, 2)
  numgen = ngens(G)
  r = size(M, 1)
  z = Array{GrpAbFinGenElem}(numgenssub)
  v = zeros(Int, numgen)
  for i in 1:numgenssub
    for j in 1:r
      v[indices[j]] = M[j, i]
    end
    z[i] = G(v)
    for j in 1:numgen
      v[j] = 0
    end
  end
  #H, m =  sub(G, z)
  return z
end

function _psubgroups_gens(G::GrpAbFinGen, p, t::Array{Int, 1} = [-1])
  S, mS = snf(G)
  return ( map(x -> preimage(mS, x),z) for z in __psubgroups_gens(S, p, t))
end

function __psubgroups_gens(G::GrpAbFinGen, p, t::Array{Int, 1} = [-1])
  # The SNF can contain 1's and 0's
  # Have to help inference here with the explicit type
  x = Tuple{Int, Int}[ (valuation(G.snf[i], p), i) for i in 1:length(G.snf) if G.snf[i] > 1]
  reverse!(x)
  Gtype = [ t[1] for t in x ]
  indice = [ t[2] for t in x ]
  # x is the "type" of the p-group G as a partition
  if length(t) == 1 && t[1] == -1
    return (_matrix_to_generators(G, M, indice) for M in _subgroup_iterator(Gtype, p))
  else
    t = vcat(t, zeros(Int, length(x) - length(t)))
    return  (_matrix_to_generators(G, M, indice) for M in _subgroup_type_iterator(Gtype, t, p))
    #return  Gtype, indice, (M  for M in _SubgroupTypeIterator(Gtype, t, p))
  end
  return Gtype, indice
end

function _psylow_subgroup_gens(G::GrpAbFinGen, p::Int)
  @assert issnf(G)
  z = GrpAbFinGenElem[]
  for i in 1:ngens(G)
    k, m = remove(G.snf[i], p)
    #@show m, k
    if k != 0
      #@show m, G[i]
      push!(z, m*G[i])
    end
  end
  return z
end

function psylow_subgroup(G::GrpAbFinGen, p::Int)
  S, mS = snf(G)
  z = _psylow_subgroup_gens(S, p)
  zz = [ preimage(mS, x) for x in z ]
  return sub(G, zz)
end

function _psubgroups(G::GrpAbFinGen, p::Int; sub_type::Array{Int, 1} = [-1],
                                            fun = sub)
  S, mS = psylow_subgroup(G, p)
  return ( fun(G, map(mS, z)) for z in _psubgroups_gens(S, p, sub_type))
end

mutable struct pSubgroupIterator{F, T, E}
  G::GrpAbFinGen
  sub_type::Array{Int, 1}
  quot_type::Array{Int, 1}
  fun::F
  it::T
end

function Base.show(io::IO, I::pSubgroupIterator)
  print(io, "p-subgroup iterator of \n$(I.G)\n")

  if I.sub_type == [-1]
    print(io, "subgroup type: any\n")
  else
    print(io, "subgroup type: $(I.sub_type)\n")
  end

  if I.quot_type == [-1]
    print(io, "quotient type: any\n")
  else
    print(io, "quotient type: $(I.quot_type)\n")
  end

  if I.fun != sub
    print(io, "function: $(I.fun)")
  end
end

# this is wrong.
function _quo_type_get_sub_type(x::Array{Int, 1}, y::Array{Int, 1})
  y = vcat(y, zeros(Int, length(x) - length(y)))
  z = x .- y
  sort!(z, rev = true)
  t = findlast(!iszero, z)
  return z[1:t]
end

function pSubgroupIterator(G::GrpAbFinGen, p::Int; sub_type::Array{Int, 1} = [-1],
                                                   quot_type::Array{Int, 1} = [-1],
                                                   fun = sub)
  !(length(sub_type) == 1 && sub_type[1] == -1) &&
  !( length(quot_type) == 1 && quot_type[1] == -1) &&
  error("Specify either subgroup type or quotient type but not both")

  it = _psubgroups(G, p; sub_type = sub_type, fun = fun)
  E = Core.Inference.return_type(fun, (GrpAbFinGen, Array{GrpAbFinGenElem, 1}))
  z = pSubgroupIterator{typeof(fun), typeof(it), E}(G, sub_type, quot_type, fun, it)
  return z
end

function psubgroups(G::GrpAbFinGen, p::Int; sub_type::Array{Int, 1} = [-1],
                                                   quot_type::Array{Int, 1} = [-1],
                                                   fun = sub)
  return pSubgroupIterator(G, p; sub_type = sub_type,
                                 quot_type = quot_type,
                                 fun = fun)
end


Base.start(S::pSubgroupIterator) = Base.start(S.it)

Base.next(S::pSubgroupIterator, s) = Base.next(S.it, s)

Base.done(S::pSubgroupIterator, s) = Base.done(S.it, s)

Base.length(S::pSubgroupIterator) = Base.start(S.it)

Base.eltype(::Type{pSubgroupIterator{F, T, E}}) where {F, T, E} = E

Base.collect(S::pSubgroupIterator) = Base.collect(S.it)

