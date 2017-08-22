# Buttler

# Iterator for all possible y's

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

function Base.collect(Y::yIterator)
  s = Array{Int, 1}[]
  for x in Y
    push!(s, x)
  end
  return s
end

struct SigmaIteratorGivenY{T}
  gen::T
end

#SigmaIteratorGivenY{T}(x) where {T} = SigmaIteratorGivenY{T}(x)

SigmaIteratorGivenY(s, t, x, y) = SigmaIteratorGivenY(Iterators.filter(sigma -> _isvalid(s, t, x, y, sigma), Nemo.AllPerms(s)))

Base.start(S::SigmaIteratorGivenY) = Base.start(S.gen)

Base.next(S::SigmaIteratorGivenY, s) = Base.next(S.gen, s)
Base.done(S::SigmaIteratorGivenY, s) = Base.done(S.gen, s)
Base.length(S::SigmaIteratorGivenY) = Base.start(S.gen)
Base.eltype(::Type{SigmaIteratorGivenY}) = Array{Int, 1}

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

#Base.iteratorsize(::Type{SigmaIteratorGivenY}) = Base.SizeUnknown()
#
#Base.eltype(::Type{SigmaIteratorGivenY}) = Array{Int, 1}
#
#
#function Base.start(F::SigmaIteratorGivenY)
#  perm_state = start(F.perms)
#  old_perm_state = copy_perm_state(perm_state)
#
#  sigma, perm_state = next(F.perms, perm_state)
#
#  while !_isvalid(F, sigma) && !done(F.perms, perm_state)
#    old_perm_state = copy_perm_state(perm_state)
#    sigma, perm_state = next(F.perms, perm_state)
#  end
#
#  return old_perm_state
#end
#
#function copy_perm_state(perm_state)
#  return (copy(perm_state[1]), perm_state[2], perm_state[3], copy(perm_state[4]))
#end
#
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

type cIteratorGivenSigma
  s::Int
  t::Int
  x::Array{Int, 1}
  y::Array{Int, 1}
  p::Int
  sigma::Array{Int, 1}
  tau::Array{Int, 1}
  indice::Array{Tuple{Int, Int, Int}, 1}
  it


  function cIteratorGivenSigma(s::Int, t::Int, x::Array{Int, 1}, y::Array{Int, 1}, p::Int, sigma::Array{Int, 1})
    tau = Nemo.inv!(perm(sigma))
    z = new(s, t, x, y, p, sigma, tau)
    a, b = getintervals(z)
    z.indice = a
    z.it = b
    return z
  end
end

function getintervals(C::cIteratorGivenSigma)
  indice = Tuple{Int, Int, Int}[]
  ranges = UnitRange{Int}[]

  t = C.t
  s = C.s
  y = C.y
  x = C.x
  p = C.p
  sigma = C.sigma
  tau = C.tau

  for j in 1:C.t
    for i in 1:C.s
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
  return indice, Base.product(ranges...)
end

Base.start(C::cIteratorGivenSigma) = Base.start(C.it)

Base.next(C::cIteratorGivenSigma, s) = Base.next(C.it, s)

Base.done(C::cIteratorGivenSigma, s) = Base.done(C.it, s)

Base.length(C::cIteratorGivenSigma) = Base.length(C.it)

function get_matrix(s, t, ind::Array{Tuple{Int, Int, Int}, 1}, c, sigma, tau, p, x, y)
  M = Array{Int}(s, t)
  get_matrix!(M, s, t, ind, c, sigma, tau, p, x, y)
  return M
end

function get_matrix!(M, s, t, ind::Array{Tuple{Int, Int, Int}, 1}, c, sigma, tau, p, x, y)
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
    #else
    #  error("sdas")
    end
  end
  return M
end

function _SubgroupTypeIterator(x, y, p)
  s = length(x)
  t = findlast(!iszero, y)
  return (get_matrix(s, t, f[1], c, sigma, f[2], p, x, y)
          for sigma in SigmaIteratorGivenY(s, t, x, y)
          for f in compute_indice(s, t, x, y, sigma)
          for c in cIteratorGivenSigma(s, t, x, y, p, sigma))
end

function _SubgroupIterator(x, p)
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

#    z = new(s, t, x, y, SigmaIteratorGivenY(s, t, x, y, Nemo.AllPerms(s)))
#    return z
#  end
#end

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
    return (_matrix_to_generators(G, M, indice) for M in _SubgroupIterator(Gtype, p))
  else
    t = vcat(t, zeros(Int, length(x) - length(t)))
    return  (_matrix_to_generators(G, M, indice) for M in _SubgroupTypeIterator(Gtype, t, p))
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

