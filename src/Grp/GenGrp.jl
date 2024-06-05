################################################################################
#
#  Generic group given by multiplication table
#
################################################################################

################################################################################
#
#  Types
#
################################################################################

@attributes mutable struct MultTableGroup <: Group
  identity::Int
  order::Int
  mult_table::Matrix{Int}
  gens::Vector{Int}
  is_abelian::Bool
  is_cyclic::Bool
  issolvable::Int
  is_nilpotent::Int
  isfromdb::Bool
  small_group_id::Tuple{Int, Int}

  function MultTableGroup(M::Matrix{Int})
    z = new()
    z.mult_table = M
    z.identity = find_identity(z)
    z.order = size(M, 1)
    z.issolvable = 0
    z.is_nilpotent = 0
    # Because it is cheap, let us check some properties
    n = z.order
    z.is_abelian = defines_abelian_group(M)
    e = Int(euler_phi(n))
    # There are e generators in case it is cyclic
    # If I find n - e + 1 elements of the wrong order, we are done
    z.is_cyclic = false
    z.isfromdb = false
    z.small_group_id = (0, 0)

    for i in 1:(n - e + 1)
      if order(z[i]) == n
        z.is_cyclic = true
        z.gens = Int[i]
        break
      end
    end

    return z
  end
end

struct MultTableGroupElem <: GroupElem
  group::MultTableGroup
  i::Int
  function MultTableGroupElem(group::MultTableGroup, i::Int)
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

mutable struct MultTableGroupHom <: Map{MultTableGroup, MultTableGroup, HeckeMap, MultTableGroup}

  domain::MultTableGroup
  codomain::MultTableGroup
  img::Vector{MultTableGroupElem}
  preimg::Vector{MultTableGroupElem}

  function MultTableGroupHom(G::MultTableGroup, H::MultTableGroup, image::Vector{MultTableGroupElem})
    z = new()
    z.domain = G
    z.codomain = H
    z.img = image
    return z
  end
end


mutable struct MultTableGroupToGroupHom #<: Map

  domain::MultTableGroup
  codomain::FinGenAbGroup
  dict::Dict{MultTableGroupElem, FinGenAbGroupElem}

  function MultTableGroupToGroupHom(S::Vector{MultTableGroupElem}, I::Vector{FinGenAbGroupElem})
    z = new()
    z.domain = parent(S[1])
    z.codomain = parent(I[1])
    dict = Dict{MultTableGroupElem, FinGenAbGroupElem}()
    op(t1::Tuple{MultTableGroupElem, FinGenAbGroupElem}, t2::Tuple{MultTableGroupElem, FinGenAbGroupElem}) = (t1[1] * t2[1], t1[2] + t2[2])
    close = closure([(S[i],I[i]) for i in 1:length(S)], op)
    for c in close
      dict[c[1]] = c[2]
    end
    z.dict = dict
    return z
  end

  function MultTableGroupToGroupHom(dict::Dict{MultTableGroupElem, FinGenAbGroupElem})
    z = new()
    z.domain = parent(first(dict)[1])
    z.codomain = parent(first(dict)[2])
    z.dict = dict
    return z
  end
end

mutable struct FinGenAbGroupToGroupHom#<: Map

  domain::FinGenAbGroup
  codomain::MultTableGroup
  I::Vector{MultTableGroupElem}

  function FinGenAbGroupToGroupHom(G::FinGenAbGroup, I::Vector{MultTableGroupElem})
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
@doc raw"""
     generic_group(G, op)

Compute a group on the set $G$ with operation $op$.

Returns a triple `(Gen, GtoGen, GentoG)`, where `Gen` is a group,
`GtoGen` is a dictionary mapping elements in `G` to elements of `Gen`,
and `GentoG` is likewise but the other way around.

# Examples
```jldoctest
julia> G = [1, -1, im, -im]
4-element Vector{Complex{Int64}}:
  1 + 0im
 -1 + 0im
  0 + 1im
  0 - 1im

julia> Gen, GtoGen, GentoG = generic_group(G, *);

julia> Gen
Generic group of order 4 with multiplication table

julia> one(Gen)
(1)

julia> GentoG[one(Gen)]
1 + 0im

julia> GtoGen[-1]
(2)
```
"""
function generic_group(G, op)
  Gen = MultTableGroup(_multiplication_table(G, op))
  GentoG = Dict{MultTableGroupElem, eltype(G)}(Gen[i] => G[i] for i in 1:length(G))
  GtoGen = Dict{eltype(G), MultTableGroupElem}(G[i] => Gen[i] for i in 1:length(G))
  return Gen, GtoGen, GentoG
end

###############################################################################
#
#   AbstractString I/O
#
###############################################################################

function show(io::IO, m::FinGenAbGroupToGroupHom)
   print(io, "Group Morphism from\n", m.domain, "\nto ", m.codomain)
end

function show(io::IO, m::MultTableGroupToGroupHom)
   print(io, "Group Morphism from\n", m.domain, "\nto ", m.codomain)
end

################################################################################
#
#  Basic functionality
#
################################################################################

elem_type(::Type{MultTableGroup}) = MultTableGroupElem

Base.hash(G::MultTableGroupElem, h::UInt) = Base.hash(G.i, h)

Base.hash(G::MultTableGroupHom, h::UInt) = UInt(0)

function Base.deepcopy_internal(g::MultTableGroupElem, dict::IdDict)
  return MultTableGroupElem(g.group, g.i)
end

################################################################################
#
#  Parent
#
################################################################################

function parent(g::MultTableGroupElem)
  return g.group
end

################################################################################
#
#  Construct the ith element
#
################################################################################
@doc raw"""
     getindex(G::MultTableGroup, i::Int)
Returns the $i$-th element of $G$.
"""
function getindex(G::MultTableGroup, i::Int)
  return MultTableGroupElem(G, i)
end

function getindex(G::MultTableGroupElem)
  return G.i
end

################################################################################
#
#  Equality
#
################################################################################

function ==(g::MultTableGroupElem, h::MultTableGroupElem)
  return parent(g) === parent(h) && g.i == h.i
end

function ==(g::MultTableGroupHom, h::MultTableGroupHom)
  return g.domain === h.domain && g.codomain === h.codomain && g.img == h.img
end

################################################################################
#
#  Order
#
################################################################################

function order(G::MultTableGroup)
  return size(G.mult_table, 1)
end

length(G::MultTableGroup) = order(G)

################################################################################
#
#  Order of an element
#
################################################################################

function order(g::MultTableGroupElem)
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

function find_identity(G::MultTableGroup)
  return _find_identity(G.mult_table)
end

function _find_identity(m::Matrix{Int})
  return find_identity([1], (i, j) -> m[i, j])
end

@doc raw"""
     id(G::MultTableGroup)
Returns the identity element of $G$.
"""
function id(G::MultTableGroup)
  return MultTableGroupElem(G, G.identity)
end

one(G::MultTableGroup) = id(G)

################################################################################
#
#  Multiplication
#
################################################################################

function *(g::MultTableGroupElem, h::MultTableGroupElem)
  G = parent(g)
  return MultTableGroupElem(G, G.mult_table[g.i, h.i])
end

op(g::MultTableGroupElem, h::MultTableGroupElem) = g*h

function ^(g::MultTableGroupElem, i::T) where T <: Union{Int64, ZZRingElem}
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

iszero(a::MultTableGroupElem) = a == id(parent(a))

isone(a::MultTableGroupElem) = a == id(parent(a))

is_identity(a::MultTableGroupElem) = a == id(parent(a))

################################################################################
#
#  Inverse
#
################################################################################

function inv(g::MultTableGroupElem)
  G = parent(g)
  m = G.mult_table
  i = g.i
  l = size(m, 1)
  ide = id(G)
  for j in 1:l
    if m[i, j] == G.identity
      return MultTableGroupElem(G, j)
    end
  end
  error("Not possible")
end

################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, G::MultTableGroup)
  print(io, "Generic group of order ", order(G), " with multiplication table")
end

function Base.show(io::IO, g::MultTableGroupElem)
  print(io, "($(g.i))")
end

################################################################################
#
#  Iterator interface
#
################################################################################

Base.eltype(::Type{MultTableGroup}) = MultTableGroupElem

function Base.iterate(G::MultTableGroup, state::Int = 1)
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

function gens(G::MultTableGroup)
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

@doc raw"""
     _isnormal(H::Vector{MultTableGroupElem}) -> Bool
Check if $H$ is invariant under conjugation by the generators of the group.
"""
function _isnormal(H::Vector{MultTableGroupElem})
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

@doc raw"""
     _isnormal(H::Vector{MultTableGroupElem}, gen::MultTableGroupElem) -> Bool
Check if the cyclic group $H$ with generator $gen$ is invariant under
conjugation by the generators of the group.
"""
function _isnormal(H::Vector{MultTableGroupElem}, gen::MultTableGroupElem)
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
function _cyclic_subgroups(G::MultTableGroup; normal::Bool = false)
  res = Vector{MultTableGroupElem}[]
  res_elem = MultTableGroupElem[]
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

@doc raw"""
     _subgroups_all(G::MultTableGroup; normal::Bool = false)
Iteratively built up subgroups from cyclic groups.
Any subgroup is of the form <C_1,...,C_k>, where k are cyclic subgroups.
"""
function _subgroups_all(G::MultTableGroup; normal::Bool = false)
  res = Vector{MultTableGroupElem}[]
  res_gens = Vector{MultTableGroupElem}[]
  cur_grps, Cgen = _cyclic_subgroups(G)
  cur = Vector{MultTableGroupElem}[MultTableGroupElem[g] for g in Cgen]
  old = cur
  ngenext = Vector{MultTableGroupElem}[]
  while true
    new = Vector{MultTableGroupElem}[]
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

@doc raw"""
     subgroups(G::MultTableGroup; order::Int = 0,
                              index::Int = 0,
                              normal::Bool = false,
                              conjugacy_classes::Bool = false)
Returns subgroups of $G$ with embedding.
"""
function subgroups(G::MultTableGroup; order::Int = 0,
                              index::Int = 0,
                              normal::Bool = false,
                              conjugacy_classes::Bool = false)
  H = _subgroups_all(G, normal = normal)
  if order > 0
    HH = Vector{Vector{MultTableGroupElem}}([h for h in H if length(h) == order])
  elseif index > 0
    HH = Vector{Vector{MultTableGroupElem}}([h for h in H if divexact(length(G), length(h)) == index])
  else
    HH = H
  end

  if conjugacy_classes
    HHH = Vector{Vector{MultTableGroupElem}}()
    for S in HH
      new = true
      for g in G
        Sg = sort!(MultTableGroupElem[g * s * inv(g) for s in S], by = x -> x.i)
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

  res = Vector{Tuple{MultTableGroup, MultTableGroupHom}}(undef, length(HH))
  for i in 1:length(HH)
    res[i] = sub(G, HH[i])
  end
  return res
end

@doc raw"""
    sub(G::MultTableGroup, H::Vector{MultTableGroupElem})

Assume that $H$ is a subgroup of $G$, compute a generic group and an embedding.
"""
function sub(G::MultTableGroup, H::Vector{MultTableGroupElem})
  Hgen, = generic_group(H, *)
  m = MultTableGroupHom(Hgen, G, H)
  return Hgen, m
end

################################################################################
#
#  Predicates
#
################################################################################

@doc raw"""
    is_abelian(G::MultTableGroup) -> Bool

Returns whether $G$ is abelian.
"""
function is_abelian(G::MultTableGroup)
  return G.is_abelian
end

function defines_abelian_group(m)
  return is_symmetric(m)
end

@doc raw"""
    is_cyclic(G::MultTableGroup) -> Bool

Returns whether $G$ is cyclic.
"""
function is_cyclic(G::MultTableGroup)
  return G.is_cyclic
end

################################################################################
#
#  Normalizer
#
################################################################################

function normalizer(G::MultTableGroup, mH::MultTableGroupHom)
  C = left_cosets(G, mH)
  H = MultTableGroupElem[mH(h) for h in domain(mH)]
  ge = MultTableGroupElem[mH(h) for h in gens(domain(mH))]
  norm = MultTableGroupElem[]
  for c in C
    is_norm = true
    for h in ge
      if !(inv(c) * h * c in H)
        is_norm = false
        break
      end
    end
    if is_norm
      push!(norm, c)
    end
  end
  append!(H, norm)
  unique!(H)
  H = closure(H, *)
  return sub(G, H)
end

function left_cosets(G::MultTableGroup, mH::MultTableGroupHom)
  H = MultTableGroupElem[mH(h) for h in domain(mH)]
  GG = collect(G)
  cosets = MultTableGroupElem[id(G)]
  setdiff!(GG, H)
  while !isempty(GG)
    h = pop!(GG)
    push!(cosets, h)
    setdiff!(GG, (h * hh for hh in H))
  end
  return cosets
end

function right_cosets(G::MultTableGroup, mH::MultTableGroupHom)
  H = MultTableGroupElem[mH(h) for h in domain(mH)]
  GG = collect(G)
  cosets = MultTableGroupElem[id(G)]
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

@doc raw"""
     quotient(G::MultTableGroup, H::MultTableGroup, HtoG::MultTableGroupHom)
Returns the quotient group $Q$ = $G$/$H$ with canonical map $G$ -> $Q$.
"""
function quotient(G::MultTableGroup, H::MultTableGroup, HtoG::MultTableGroupHom)
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

  function quotient_op(A::Vector{MultTableGroupElem}, B::Vector{MultTableGroupElem})
     i = getindex(A[1]*B[1])
     j = findfirst(x->x == i, M)[2]
     return getindex.([G],M[:,j])
  end

  Q,SetGtoQ,QtoSetG = generic_group([getindex.(Ref(G),M[:,i]) for i in 1:size(M)[2]], quotient_op)

  image = Vector{MultTableGroupElem}(undef, order(G))
  for i in 1:order(G)
    j = findfirst(x->x == i, M)[2]
    image[i] = SetGtoQ[getindex.([G],M[:,j])]
  end

  return Q, MultTableGroupHom(G, Q, image)
end

#mainly for testing
function quotient_indx(a::Int64,b::Int64)
  G = Hecke.small_group(a,b)
  subgroups = Hecke.subgroups(G, normal=true)
  return ResidueRingElem = sort([tuple(find_small_group(quotient(G, subgroups[i][1], subgroups[i][2])[1])[1]...) for i in 1:length(subgroups)])
end

function direct_product(G1::MultTableGroup, G2::MultTableGroup)
  S = [(g1,g2) for g1 in collect(G1), g2 in collect(G2)]
  directproduct_op(g1::Tuple{MultTableGroupElem,MultTableGroupElem}, g2::Tuple{MultTableGroupElem,MultTableGroupElem}) = (g1[1] * g2[1], g1[2] * g2[2])
  DP, GprodtoDP, DPtoGprod = generic_group(S, directproduct_op)
  DPtoG1 = [DPtoGprod[DP[i]][1] for i in 1:length(DP)]
  DPtoG2 = [DPtoGprod[DP[i]][2] for i in 1:length(DP)]
  return (DP, MultTableGroupHom(DP, G1, DPtoG1), MultTableGroupHom(DP, G2, DPtoG2))
end

# The commutator subgroup is generated by [g, h]^k, where g, h run through the generators of G and k through the elements of G.
function commutator_subgroup(G::MultTableGroup)
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

function derived_series(G::MultTableGroup, n::Int64 = 2 * order(G))
  ResidueRingElem = Vector{Tuple{MultTableGroup, MultTableGroupHom}}()
  push!(ResidueRingElem,(G, MultTableGroupHom(G,G,elements(G))))
  Gtemp = G
  indx = 1
  while true
    Gtemp, GtempToGtemp = commutator_subgroup(Gtemp)
    if order(Gtemp) == order(ResidueRingElem[indx][1])
      break
    end
    push!(ResidueRingElem,(Gtemp, GtempToGtemp))
    indx += 1
  end
  return ResidueRingElem
end

elements(G::MultTableGroup) = collect(G)

elements(HtoG::MultTableGroupHom) = unique(HtoG.img)

function sylow_subgroup(G::MultTableGroup, p::IntegerUnion)
  if !is_prime(p)
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

function conjugacy_classes(G::MultTableGroup)
  CC = Vector{Vector{MultTableGroupElem}}()
  for x in collect(G)
    if true in in.(Ref(x), CC)##immer
      break
    end
    new_cc = Vector{MultTableGroupElem}()
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

function is_characteristic(G::MultTableGroup, mH::MultTableGroupHom)
  auts = automorphism_list(G)
  for aut in auts
    if !issubset(aut.img, mH.img)
      return false
    end
  end
  return true
end

function induces_to_subgroup(G::MultTableGroup, mH::MultTableGroupHom, aut::MultTableGroupHom)
  H = mH.domain
  return MultTableGroupHom(H, H, [preimage(mH, aut(mH(h))) for h in collect(H)])
end

function induces_to_quotient(G::MultTableGroup, mQ::MultTableGroupHom, aut::MultTableGroupHom)
  Q = mQ.domain
  return MultTableGroupHom(Q, Q, [mQ(aut(preimage(mQ, q))) for q in collect(Q)])
end

@doc raw"""
     max_order(G::MultTableGroup) -> (g::MultTableGroupElem, i::Int64)
Returns an element of $G$ with maximal order and the corresponding order.
"""
function max_order(G::MultTableGroup)
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

function gen_2_ab(G::MultTableGroup)
  if !is_abelian(G)
      error("Given group is not abelian")
  end

  d = order(G)
  d_first = max_order(G)[2]
  pos = Vector{Vector{Int64}}()

  _d_find_rek!([[d_first]], d, pos)

  for pos_elem in pos
    Cycl_group, TupleToGroup, GroupToTuple = cycl_prod(pos_elem)
    Gens = Vector{MultTableGroupElem}(undef,length(pos_elem))
    Rels = [[j for i in 1:pos_elem[j]] for j in 1:length(pos_elem)]
    A = [0 for j in 1:length(pos_elem)]
    for i in 1:length(pos_elem)
      A[i] = 1
      Gens[i] = TupleToGroup[Tuple(A)]
      A[i] = 0
    end
    #improve to auts directly
    for mor in Hecke._morphisms_with_gens(Cycl_group, G, Gens, Rels)
      if is_bijective(mor)
        #due to construction alrdy in snf
        GrpAb = FinGenAbGroup(pos_elem, true)
        #GrpAbtoG = Dict{FinGenAbGroupElem, MultTableGroupElem}(x => mor(TupleToGroup[Tuple(Int64.(x.coeff))]) for x in collect(GrpAb))
        GrpAbtoG = [mor(TupleToGroup[Tuple(Int64.(x.coeff))]) for x in gens(GrpAb)]
        GtoGrpAb = Dict{MultTableGroupElem, FinGenAbGroupElem}(G[i] => GrpAb([GroupToTuple[inv(mor)(G[i])]...]) for i in 1:length(G))
        return (GrpAb, MultTableGroupToGroupHom(GtoGrpAb), FinGenAbGroupToGroupHom(GrpAb, GrpAbtoG))
      end
    end
  end
end

function _d_find_rek!(candidates::Vector{Vector{Int64}}, bound::Int64, ResidueRingElem::Vector{Vector{Int64}})
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
          push!(ResidueRingElem, new_res)
        else
        push!(ResidueRingElem, can)
      end
      end
    end
  end
  if length(new_candidates) == 0
    return
  else
    _d_find_rek!(new_candidates, bound, ResidueRingElem)
  end
end

function cycl_prod(A::Vector{Int64})
  Ar_elems = [[k for k in 0:A[i]-1] for i in 1:length(A)]
  it = Iterators.product(Ar_elems...)
  cycl_prod_op(A1,A2) = Tuple([mod(A1[i] + A2[i], A[i]) for i in 1:length(A)])
  return generic_group(vec([i for i in it]), cycl_prod_op)
end

function orbit(G::MultTableGroup, action, x)
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

function stabilizer(G::MultTableGroup, action, x::T) where T
  Gens = gens(G)
  S = Vector{MultTableGroupElem}()
  D = Dict{T, MultTableGroupElem}()
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

function intersect(mH::MultTableGroupHom, mK::MultTableGroupHom)
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

function center(G::MultTableGroup)
  if is_abelian(G)
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
