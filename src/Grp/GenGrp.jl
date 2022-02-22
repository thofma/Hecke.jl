################################################################################
#
#  Generic group given by multiplication table
#
################################################################################

export GrpGen, GrpGenElem, GrpGenToGrpGenMor, GrpGenToGrpAbMor, GrpAbToGrpGenMor,
generic_group, isabelian, iscyclic, order, elements,
getindex, subgroups, quotient, inv, kernel, elem_type, parent, *,
psylow_subgroup, commutator_subgroup, derived_series, order, direct_product,
conjugacy_classes, ischaracteristic, induces_to_subgroup, induces_to_quotient,
max_order, gen_2_ab, orbit, stabilizer

################################################################################
#
#  Types
#
################################################################################

mutable struct GrpGen <: Group
  identity::Int
  order::Int
  mult_table::Matrix{Int}
  gens::Vector{Int}
  isabelian::Bool
  iscyclic::Bool
  issolvable::Int
  isnilpotent::Int
  isfromdb::Bool
  small_group_id::Tuple{Int, Int}

  function GrpGen(M::Matrix{Int})
    z = new()
    z.mult_table = M
    z.identity = find_identity(z)
    z.order = size(M, 1)
    z.issolvable = 0
    z.isnilpotent = 0
    # Because it is cheap, let us check some properties
    n = z.order
    z.isabelian = defines_abelian_group(M)
    e = Int(euler_phi(n))
    # There are e generators in case it is cyclic
    # If I find n - e + 1 elements of the wrong order, we are done
    z.iscyclic = false
    z.isfromdb = false
    z.small_group_id = (0, 0)

    for i in 1:(n - e + 1)
      if order(z[i]) == n
        z.iscyclic = true
        z.gens = Int[i]
        break
      end
    end

    return z
  end
end

struct GrpGenElem <: GroupElem
  group::GrpGen
  i::Int
  function GrpGenElem(group::GrpGen, i::Int)
    og = order(group)
    if i > og
      error("There are only $og elements in $group")
    end
    if i < 1
      error("The index has to be positive but is $i")
    end
    return z = new(group, i)
  end
end

################################################################################
#
#  Morphism type
#
################################################################################

mutable struct GrpGenToGrpGenMor <: Map{GrpGen, GrpGen, HeckeMap, GrpGen}

  domain::GrpGen
  codomain::GrpGen
  img::Vector{GrpGenElem}
  preimg::Vector{GrpGenElem}

  function GrpGenToGrpGenMor(G::GrpGen, H::GrpGen, image::Vector{GrpGenElem})
    z = new()
    z.domain = G
    z.codomain = H
    z.img = image
    return z
  end
end


mutable struct GrpGenToGrpAbMor #<: Map

  domain::GrpGen
  codomain::GrpAbFinGen
  dict::Dict{GrpGenElem, GrpAbFinGenElem}

  function GrpGenToGrpAbMor(S::Vector{GrpGenElem}, I::Vector{GrpAbFinGenElem})
    z = new()
    z.domain = parent(S[1])
    z.codomain = parent(I[1])
    dict = Dict{GrpGenElem, GrpAbFinGenElem}()
    op(t1::Tuple{GrpGenElem, GrpAbFinGenElem}, t2::Tuple{GrpGenElem, GrpAbFinGenElem}) = (t1[1] * t2[1], t1[2] + t2[2])
    close = closure([(S[i],I[i]) for i in 1:length(S)], op)
    for c in close
      dict[c[1]] = c[2]
    end
    z.dict = dict
    return z
  end

  function GrpGenToGrpAbMor(dict::Dict{GrpGenElem, GrpAbFinGenElem})
    z = new()
    z.domain = parent(first(dict)[1])
    z.codomain = parent(first(dict)[2])
    z.dict = dict
    return z
  end
end

mutable struct GrpAbToGrpGenMor#<: Map

  domain::GrpAbFinGen
  codomain::GrpGen
  I::Vector{GrpGenElem}

  function GrpAbToGrpGenMor(G::GrpAbFinGen, I::Vector{GrpGenElem})
    z = new()
    z.domain = G
    z.codomain = parent(I[1])
    z.I = I
    return z
  end
end


################################################################################
#
#  Compute generic group from anything
#
################################################################################
@doc Markdown.doc"""
     generic_group(G, op)
Computes group of $G$ with operation $op$, implemented with multiplication
table 'G.mult_table'.
The elements are just 1..n and i * j = 'G.mult_table'[i, j].
"""
function generic_group(G, op)
  Gen = GrpGen(_multiplication_table(G, op))
  GentoG = Dict{GrpGenElem, eltype(G)}(Gen[i] => G[i] for i in 1:length(G))
  GtoGen = Dict{eltype(G), GrpGenElem}(G[i] => Gen[i] for i in 1:length(G))
  return Gen, GtoGen, GentoG
end

###############################################################################
#
#   AbstractString I/O
#
###############################################################################

function show(io::IO, m::GrpAbToGrpGenMor)
   print(io, "Group Morphism from\n", m.domain, "\nto ", m.codomain)
end

function show(io::IO, m::GrpGenToGrpAbMor)
   print(io, "Group Morphism from\n", m.domain, "\nto ", m.codomain)
end

################################################################################
#
#  Basic functionality
#
################################################################################

elem_type(::Type{GrpGen}) = GrpGenElem

elem_type(::GrpGen) = GrpGenElem

Base.hash(G::GrpGenElem, h::UInt) = Base.hash(G.i, h)

Base.hash(G::GrpGen, h::UInt) = UInt(0)

Base.hash(G::GrpGenToGrpGenMor, h::UInt) = UInt(0)

function Base.deepcopy_internal(g::GrpGenElem, dict::IdDict)
  return GrpGenElem(g.group, g.i)
end

################################################################################
#
#  Parent
#
################################################################################

function parent(g::GrpGenElem)
  return g.group
end

################################################################################
#
#  Construct the ith element
#
################################################################################
@doc Markdown.doc"""
     getindex(G::GrpGen, i::Int)
Returns the $i$-th element of $G$.
"""
function getindex(G::GrpGen, i::Int)
  return GrpGenElem(G, i)
end

function getindex(G::GrpGenElem)
  return G.i
end

################################################################################
#
#  Equality
#
################################################################################

function ==(g::GrpGenElem, h::GrpGenElem)
  return parent(g) === parent(h) && g.i == h.i
end

function ==(g::GrpGenToGrpGenMor, h::GrpGenToGrpGenMor)
  return g.domain === h.domain && g.codomain === h.codomain && g.img == h.img
end

################################################################################
#
#  Order
#
################################################################################

function order(G::GrpGen)
  return size(G.mult_table, 1)
end

length(G::GrpGen) = order(G)

################################################################################
#
#  Order of an element
#
################################################################################

function order(g::GrpGenElem)
  k = 2
  h = g * g
  while h != g
    h = g * h
    k = k + 1
  end
  return k - 1
end

################################################################################
#
#  Identity
#
################################################################################

function find_identity(G::GrpGen)
  return _find_identity(G.mult_table)
end

function _find_identity(m::Matrix{Int})
  return find_identity([1], (i, j) -> m[i, j])
end

@doc Markdown.doc"""
     id(G::GrpGen)
Returns the identity element of $G$.
"""
function id(G::GrpGen)
  return GrpGenElem(G, G.identity)
end

################################################################################
#
#  Multiplication
#
################################################################################

function *(g::GrpGenElem, h::GrpGenElem)
  G = parent(g)
  return GrpGenElem(G, G.mult_table[g.i, h.i])
end

op(g::GrpGenElem, h::GrpGenElem) = g*h

function ^(g::GrpGenElem, i::T) where T <: Union{Int64, fmpz}
  if i == 0
    return id(parent(g))
  end
  if i > 0
    res = g
    for j in 2:i
      res = res * g
    end
    return res
  else
    res = inv(g)
    for j in 2:-i
      res = res * inv(g)
    end
    return res
  end
end

################################################################################
#
#  Neutral element
#
################################################################################

iszero(a::GrpGenElem) = a == id(parent(a))

isone(a::GrpGenElem) = a == id(parent(a))

isidentity(a::GrpGenElem) = a == id(parent(a))

################################################################################
#
#  Inverse
#
################################################################################

function inv(g::GrpGenElem)
  G = parent(g)
  m = G.mult_table
  i = g.i
  l = size(m, 1)
  ide = id(G)
  for j in 1:l
    if m[i, j] == G.identity
      return GrpGenElem(G, j)
    end
  end
  error("Not possible")
end

################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, G::GrpGen)
  print(io, "Generic group of order ", order(G), " with multiplication table")
end

function Base.show(io::IO, g::GrpGenElem)
  print(io, "($(g.i))\n")
end

################################################################################
#
#  Iterator interface
#
################################################################################

Base.eltype(::Type{GrpGen}) = GrpGenElem

function Base.iterate(G::GrpGen, state::Int = 1)
  if state > G.order
    return nothing
  end

  return G[state], state + 1
end

################################################################################
#
#  Generators
#
################################################################################

function gens(G::GrpGen)
  if isdefined(G, :gens)
    return [G[i] for i in G.gens]
  else
    S = small_generating_set(collect(G), *, id(G))
    G.gens = [g.i for g in S]
    return S
  end
end

################################################################################
#
#  Cyclic subgroups
#
################################################################################

@doc Markdown.doc"""
     _isnormal(H::Vector{GrpGenElem}) -> Bool
Check if $H$ is invariant under conjugation by the generators of the group.
"""
function _isnormal(H::Vector{GrpGenElem})
  S = gens(parent(H[1]))
  for s in S
    for h in H
      if !(inv(s) * h * s in H)
        return false
      end
    end
  end

  return true
end

@doc Markdown.doc"""
     _isnormal(H::Vector{GrpGenElem}, gen::GrpGenElem) -> Bool
Check if the cyclic group $H$ with generator $gen$ is invariant under
conjugation by the generators of the group.
"""
function _isnormal(H::Vector{GrpGenElem}, gen::GrpGenElem)
  S = gens(parent(H[1]))
  for s in S
    if !(inv(s) * gen * s in H)
      return false
    end
  end

  return true
end

# Compute the cyclic subgroups naively.
# TODO: Improve this
function _cyclic_subgroups(G::GrpGen; normal::Bool = false)
  res = Vector{GrpGenElem}[]
  res_elem = GrpGenElem[]
  idG = id(G)
  for g in G
    S = closure([g], *, idG)
    if normal && !_isnormal(S, g)
      continue
    end

    h = first(sort!([ s for s in S if order(s) == length(S)], by = x -> x.i))
    if h in res_elem
      continue
    else
      sort!(S, by = x -> x.i)
      @assert !(S in res)
      push!(res, S)
      push!(res_elem, h)
    end
  end

  return res, res_elem
end

################################################################################
#
#  Subgroup algorithm
#
################################################################################

@doc Markdown.doc"""
     _subgroups_all(G::GrpGen; normal::Bool = false)
Iteratively built up subgroups from cyclic groups.
Any subgroup is of the form <C_1,...,C_k>, where k are cyclic subgroups.
"""
function _subgroups_all(G::GrpGen; normal::Bool = false)
  res = Vector{GrpGenElem}[]
  res_gens = Vector{GrpGenElem}[]
  cur_grps, Cgen = _cyclic_subgroups(G)
  cur = Vector{GrpGenElem}[GrpGenElem[g] for g in Cgen]
  old = cur
  ngenext = Vector{GrpGenElem}[]
  while true
    new = Vector{GrpGenElem}[]
    for c in old
      for cy in Cgen
        n = push!(copy(c), cy)
        S = sort!(closure(n, *), by = x -> x.i)
        sort!(n, by = x -> x.i)
        if !(S in cur_grps)
          push!(new, n)
          push!(cur_grps, S)
        end
      end
    end

    if length(new) == 0
      break
    else
      append!(cur, new)
    end
    old = new
  end
  if normal
    return [cur_grps[i] for i in 1:length(cur_grps) if _isnormal(cur_grps[i])]
  else
    return cur_grps
  end
end

@doc Markdown.doc"""
     subgroups(G::GrpGen; order::Int = 0,
                              index::Int = 0,
                              normal::Bool = false,
                              conjugacy_classes::Bool = false)
Returns subgroups of $G$ with embedding.
"""
function subgroups(G::GrpGen; order::Int = 0,
                              index::Int = 0,
                              normal::Bool = false,
                              conjugacy_classes::Bool = false)
  H = _subgroups_all(G, normal = normal)
  if order > 0
    HH = Vector{Vector{GrpGenElem}}([h for h in H if length(h) == order])
  elseif index > 0
    HH = Vector{Vector{GrpGenElem}}([h for h in H if divexact(length(G), length(h)) == index])
  else
    HH = H
  end

  if conjugacy_classes
    HHH = Vector{Vector{GrpGenElem}}()
    for S in HH
      new = true
      for g in G
        Sg = sort!(GrpGenElem[g * s * inv(g) for s in S], by = x -> x.i)
        if any(isequal(Sg), HHH)
          new = false
          break
        end
      end
      if new
        push!(HHH, S)
      end
    end
    HH = HHH
  end

  res = Vector{Tuple{GrpGen, GrpGenToGrpGenMor}}(undef, length(HH))
  for i in 1:length(HH)
    res[i] = sub(G, HH[i])
  end
  return res
end

@doc Markdown.doc"""
    sub(G::GrpGen, H::Vector{GrpGenElem})

Assume that $H$ is a subgroup of $G$, compute a generic group and an embedding.
"""
function sub(G::GrpGen, H::Vector{GrpGenElem})
  Hgen, = generic_group(H, *)
  m = GrpGenToGrpGenMor(Hgen, G, H)
  return Hgen, m
end

################################################################################
#
#  Predicates
#
################################################################################

@doc Markdown.doc"""
    isabelian(G::GrpGen) -> Bool

Returns whether $G$ is abelian.
"""
function isabelian(G::GrpGen)
  return G.isabelian
end

function defines_abelian_group(m)
  return issymmetric(m)
end

@doc Markdown.doc"""
    iscyclic(G::GrpGen) -> Bool

Returns whether $G$ is cyclic.
"""
function iscyclic(G::GrpGen)
  return G.iscyclic
end

################################################################################
#
#  Normalizer
#
################################################################################

function normalizer(G::GrpGen, mH::GrpGenToGrpGenMor)
  C = left_cosets(G, mH)
  H = GrpGenElem[mH(h) for h in domain(mH)]
  ge = GrpGenElem[mH(h) for h in gens(domain(mH))]
  norm = GrpGenElem[]
  for c in C
    isnorm = true
    for h in ge
      if !(inv(c) * h * c in H)
        isnorm = false
        break
      end
    end
    if isnorm
      push!(norm, c)
    end
  end
  append!(H, norm)
  unique!(H)
  H = closure(H, *)
  return sub(G, H)
end

function left_cosets(G::GrpGen, mH::GrpGenToGrpGenMor)
  H = GrpGenElem[mH(h) for h in domain(mH)]
  GG = collect(G)
  cosets = GrpGenElem[id(G)]
  setdiff!(GG, H)
  while !isempty(GG)
    h = pop!(GG)
    push!(cosets, h)
    setdiff!(GG, (h * hh for hh in H))
  end
  return cosets
end

function right_cosets(G::GrpGen, mH::GrpGenToGrpGenMor)
  H = GrpGenElem[mH(h) for h in domain(mH)]
  GG = collect(G)
  cosets = GrpGenElem[id(G)]
  setdiff!(GG, H)
  while !isempty(GG)
    h = pop!(GG)
    push!(cosets, h)
    setdiff!(GG, (hh * h for hh in H))
  end
  return cosets
end

################################################################################
#
#  GroupsofGroups
#
################################################################################

@doc Markdown.doc"""
     quotient(G::GrpGen, H::GrpGen, HtoG::GrpGenToGrpGenMor)
Returns the quotient group $Q$ = $G$/$H$ with canonical map $G$ -> $Q$.
"""
function quotient(G::GrpGen, H::GrpGen, HtoG::GrpGenToGrpGenMor)
  elems = elements(HtoG)
  if !_isnormal(elems)
      return @error("Subgroup is not normal")
  end
  elements_indx = [getindex(i) for i in elems]
  M = G.mult_table
  rows_2delete = Vector{Int64}()
  cols_2delete = Vector{Int64}()
  for i in 1:order(G)
    if !(i in elements_indx)
       pushfirst!(rows_2delete,i)
    end
  end
  for i in rows_2delete
    M = M[vcat(1:i-1,i+1:end),:]
  end
  for j in 1:order(G)
    if j in M[:,1:j-1]
      pushfirst!(cols_2delete,j)
    end
  end
  for j in cols_2delete
      M = M[:,vcat(1:j-1,j+1:end)]
  end

  function quotient_op(A::Vector{GrpGenElem}, B::Vector{GrpGenElem})
     i = getindex(A[1]*B[1])
     j = findfirst(x->x == i, M)[2]
     return getindex.([G],M[:,j])
  end

  Q,SetGtoQ,QtoSetG = generic_group([getindex.(Ref(G),M[:,i]) for i in 1:size(M)[2]], quotient_op)

  image = Vector{GrpGenElem}(undef, order(G))
  for i in 1:order(G)
    j = findfirst(x->x == i, M)[2]
    image[i] = SetGtoQ[getindex.([G],M[:,j])]
  end

  return Q, GrpGenToGrpGenMor(G, Q, image)
end

#mainly for testing
function quotient_indx(a::Int64,b::Int64)
  G = Hecke.small_group(a,b)
  subgroups = Hecke.subgroups(G, normal=true)
  return Res = sort([tuple(find_small_group(quotient(G, subgroups[i][1], subgroups[i][2])[1])[1]...) for i in 1:length(subgroups)])
end

function direct_product(G1::GrpGen, G2::GrpGen)
  S = [(g1,g2) for g1 in collect(G1), g2 in collect(G2)]
  directproduct_op(g1::Tuple{GrpGenElem,GrpGenElem}, g2::Tuple{GrpGenElem,GrpGenElem}) = (g1[1] * g2[1], g1[2] * g2[2])
  DP, GprodtoDP, DPtoGprod = generic_group(S, directproduct_op)
  DPtoG1 = [DPtoGprod[DP[i]][1] for i in 1:length(DP)]
  DPtoG2 = [DPtoGprod[DP[i]][2] for i in 1:length(DP)]
  return (DP, GrpGenToGrpGenMor(DP, G1, DPtoG1), GrpGenToGrpGenMor(DP, G2, DPtoG2))
end

# The commutator subgroup is generated by [g, h]^k, where g, h run through the generators of G and k through the elements of G.
function commutator_subgroup(G::GrpGen)
  S = gens(G)
  gens_of_com = Set(elem_type(G)[])
  for g in S
    for h in S
      co = g * h * inv(g) * inv(h)
      for k in G
        push!(gens_of_com, k * co * inv(k))
      end
    end
  end
  _gens_of_com = collect(gens_of_com)
  H = closure(_gens_of_com, *)
  return sub(G, H)
end

function derived_series(G::GrpGen, n::Int64 = 2 * order(G))
  Res = Vector{Tuple{GrpGen, GrpGenToGrpGenMor}}()
  push!(Res,(G, GrpGenToGrpGenMor(G,G,elements(G))))
  Gtemp = G
  indx = 1
  while true
    Gtemp, GtempToGtemp = commutator_subgroup(Gtemp)
    if Gtemp == Res[indx][1]
      break
    end
    push!(Res,(Gtemp, GtempToGtemp))
    indx += 1
  end
  return Res
end

function ==(G::GrpGen, H::GrpGen)
  # TODO: Understand why the following makes the tests not pass
  #return G === H
  return G.mult_table == H.mult_table
end

elements(G::GrpGen) = collect(G)

elements(HtoG::GrpGenToGrpGenMor) = unique(HtoG.img)

function psylow_subgroup(G::GrpGen, p::IntegerUnion)
  if !isprime(p)
    error("$p not prime")
  end
  n = order(G)
  b = remove(n,p)[1]
  return subgroups(G, order=p^b)[1]
end

################################################################################
#
#  Conjugancy Classes
#
################################################################################

function conjugacy_classes(G::GrpGen)
  CC = Vector{Vector{GrpGenElem}}()
  for x in collect(G)
    if true in in.(Ref(x), CC)##immer
      break
    end
    new_cc = Vector{GrpGenElem}()
    for g in collect(G)
      elem = g * x * inv(g)
        if !(elem in new_cc)
          push!(new_cc, elem)
        end
    end
    push!(CC, new_cc)
  end
  return CC
end

################################################################################
#
#  characteristic groups
#
################################################################################

function ischaracteristic(G::GrpGen, mH::GrpGenToGrpGenMor)
  auts = automorphisms(G)
  for aut in auts
    if !issubset(aut.img, mH.img)
      return false
    end
  end
  return true
end

function induces_to_subgroup(G::GrpGen, mH::GrpGenToGrpGenMor, aut::GrpGenToGrpGenMor)
  H = mH.domain
  return GrpGenToGrpGenMor(H, H, [preimage(mH, aut(mH(h))) for h in collect(H)])
end

function induces_to_quotient(G::GrpGen, mQ::GrpGenToGrpGenMor, aut::GrpGenToGrpGenMor)
  Q = mQ.domain
  return GrpGenToGrpGenMor(Q, Q, [mQ(aut(preimage(mQ, q))) for q in collect(Q)])
end

@doc Markdown.doc"""
     max_order(G::GrpGen) -> (g::GrpGenElem, i::Int64)
Returns an element of $G$ with maximal order and the corresponding order.
"""
function max_order(G::GrpGen)
  temp = id(G)
  temp_max = order(temp)
  for g in G
    if order(g) > temp_max
      temp = g
      temp_max = order(g)
    end
  end
  return(temp, temp_max)
end

function gen_2_ab(G::GrpGen)
  if !isabelian(G)
      error("Given group is not abelian")
  end

  d = order(G)
  d_first = max_order(G)[2]
  pos = Vector{Vector{Int64}}()

  _d_find_rek!([[d_first]], d, pos)

  for pos_elem in pos
    Cycl_group, TupleToGroup, GroupToTuple = cycl_prod(pos_elem)
    Gens = Vector{GrpGenElem}(undef,length(pos_elem))
    Rels = [[j for i in 1:pos_elem[j]] for j in 1:length(pos_elem)]
    A = [0 for j in 1:length(pos_elem)]
    for i in 1:length(pos_elem)
      A[i] = 1
      Gens[i] = TupleToGroup[Tuple(A)]
      A[i] = 0
    end
    #improve to auts directly
    for mor in Hecke._morphisms_with_gens(Cycl_group, G, Gens, Rels)
      if isbijective(mor)
        #due to construction alrdy in snf
        GrpAb = GrpAbFinGen(pos_elem, true)
        #GrpAbtoG = Dict{GrpAbFinGenElem, GrpGenElem}(x => mor(TupleToGroup[Tuple(Int64.(x.coeff))]) for x in collect(GrpAb))
        GrpAbtoG = [mor(TupleToGroup[Tuple(Int64.(x.coeff))]) for x in gens(GrpAb)]
        GtoGrpAb = Dict{GrpGenElem, GrpAbFinGenElem}(G[i] => GrpAb([GroupToTuple[inv(mor)(G[i])]...]) for i in 1:length(G))
        return (GrpAb, GrpGenToGrpAbMor(GtoGrpAb), GrpAbToGrpGenMor(GrpAb, GrpAbtoG))
      end
    end
  end
end

function _d_find_rek!(candidates::Vector{Vector{Int64}}, bound::Int64, Res::Vector{Vector{Int64}})
  new_candidates = Vector{Vector{Int64}}()
  for can in candidates
    produ = prod(can)
    for div in divisors(can[1])
      if produ * div < bound && div != 1
        new_can = vcat(div, can)
        push!(new_candidates, new_can)
      elseif produ * div == bound
        if div != 1
          new_res = vcat(div, can)
          push!(Res, new_res)
        else
        push!(Res, can)
      end
      end
    end
  end
  if length(new_candidates) == 0
    return
  else
    _d_find_rek!(new_candidates, bound, Res)
  end
end

function cycl_prod(A::Vector{Int64})
  Ar_elems = [[k for k in 0:A[i]-1] for i in 1:length(A)]
  it = Iterators.product(Ar_elems...)
  cycl_prod_op(A1,A2) = Tuple([mod(A1[i] + A2[i], A[i]) for i in 1:length(A)])
  return generic_group(vec([i for i in it]), cycl_prod_op)
end

function orbit(G::GrpGen, action, x)
  Gens = gens(G)
  L = [x]
  i = 1
  while i <= length(L)
    temp = L[i]
    for g in Gens
      y = action(g, temp)
      if !in(y, L)
        push!(L, y)
      end
      i += 1
    end
  end
  return L
end

function stabilizer(G::GrpGen, action, x::T) where T
  Gens = gens(G)
  S = Vector{GrpGenElem}()
  D = Dict{T, GrpGenElem}()
  D[x] = id(G)
  L = [x]
  i = 1
  while i <= length(L)
    temp = L[i]
    for g in Gens
      y = action(g, temp)
      if !haskey(D,y)
        D[y] = D[temp] * g
        push!(L, y)
      else push!(S, D[temp] * g * inv(D[y]))
      end
      i += 1
    end
  end
  return S
end

################################################################################
#
#  Intersect
#
################################################################################

function intersect(mH::GrpGenToGrpGenMor, mK::GrpGenToGrpGenMor)
  @assert codomain(mH) == codomain(mK)
  H = domain(mH)
  K = domain(mK)
  I = intersect(elem_type(K)[mK(k) for k in K], elem_type(H)[mH(h) for h in H])
  return sub(codomain(mH), I)
end

################################################################################
#
#  Center
#
################################################################################

function center(G::GrpGen)
  if isabelian(G)
    return sub(G, collect(G))
  end

  c = elem_type(G)[]

  for g in G
    cent = true
    for h in G
      if h * g != g *h
        cent = false
        break
      end
    end

    if cent
      push!(c, g)
    end
  end

  return sub(G, c)
end
