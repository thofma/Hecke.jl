################################################################################
#
#  Generic group given by multiplication table
#
################################################################################

export GrpGen, GrpGenElem, GrpGenToGrpGenMor, generic_group, GrpGen, GrpGenElem, isabelian, iscyclic, order, elements,
getindex, subgroups, subgroup, quotient, inv, kernel, elem_type, parent, *,
psylow_subgroup, commutator_subgroup, derived_series, order, direct_product,
conjugancy_classes, ischaracteristic, induces_to_subgroup, induces_to_quotient

################################################################################
#
#  Types
#
################################################################################

mutable struct GrpGen
  identity::Int
  order::Int
  mult_table::Array{Int, 2}
  gens::Array{Int, 1}
  isabelian::Bool
  iscyclic::Bool
  issolvable::Int
  isnilpotent::Int
  isfromdb::Bool
  small_group_id::Tuple{Int, Int}

  function GrpGen(M::Array{Int, 2})
    z = new()
    z.mult_table = M
    z.identity = find_identity(z)
    z.order = size(M, 1)
    z.issolvable = 0
    z.isnilpotent = 0
    # Because it is cheap, let us check some properties
    n = z.order
    z.isabelian = defines_abelian_group(M)
    e = eulerphi(n)
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

struct GrpGenElem
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

################################################################################
#
#  Basic functionality
#
################################################################################

elem_type(::Type{GrpGen}) = GrpGenElem

elem_type(::GrpGen) = GrpGenElem

Base.hash(G::GrpGenElem, h::UInt) = Base.hash(G.i, h)

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
Returns the $i$ th element of $G$.
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
  return g.domain == h.domain && g.codomain == h.codomain && g.img == h.img
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

function _find_identity(m::Array{Int, 2})
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
Check if $H$ is invariant under conjugaction by the generators of the group.
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
conjugaction by the generators of the group.
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
Any subgroup is of the form <C_1,...C_k>, where k are cyclic subgroups.
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
    res[i] = subgroup(G, HH[i])
  end
  return res
end

@doc Markdown.doc"""
    subgroup(G::GrpGen, H::Vector{GrpGenElem})
Assume that $H$ is a subgroup of $G$, compute a generic group and an embedding.
"""
function subgroup(G::GrpGen, H::Vector{GrpGenElem})
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
  return G.isscyclic
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
  return subgroup(G, H)
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

###############################################################################
#
#  NfToNfMor closure
#
###############################################################################

function closure(S::Vector{NfToNfMor}, final_order::Int = -1)

  K = domain(S[1])
  d = numerator(discriminant(K.pol))
  p = 11
  while mod(d, p) == 0
    p = next_prime(p)
  end
  R = GF(p, cached = false)
  Rx, x = PolynomialRing(R, "x", cached = false)
  fmod = Rx(K.pol)

  t = length(S)
  order = 1
  elements = [id_hom(K)]
  pols = gfp_poly[x]
  gpol = Rx(S[1].prim_img)
  if gpol != x
    push!(pols, gpol)
    push!(elements, S[1])
    order += 1

    gpol = compose_mod(gpol, pols[2], fmod)

    while gpol != x
      order = order +1
      push!(elements, S[1]*elements[end])
      push!(pols, gpol)
      gpol = compose_mod(gpol, pols[2], fmod)
    end
  end
  if order == final_order
    return elements
  end

  for i in 2:t
    if !(S[i] in elements)
      pi = Rx(S[i].prim_img)
      previous_order = order
      order = order + 1
      push!(elements, S[i])
      push!(pols, Rx(S[i].prim_img))
      for j in 2:previous_order
        order = order + 1
        push!(pols, compose_mod(pols[j], pi, fmod))
        push!(elements, elements[j]*S[i])
      end
      if order == final_order
        return elements
      end
      rep_pos = previous_order + 1
      while rep_pos <= order
        for k in 1:i
          s = S[k]
          po = Rx(s.prim_img)
          att = compose_mod(pols[rep_pos], po, fmod)
          if !(att in pols)
            elt = elements[rep_pos]*s
            order = order + 1
            push!(elements, elt)
            push!(pols, att)
            for j in 2:previous_order
              order = order + 1
              push!(pols, compose_mod(pols[j], att, fmod))
              push!(elements, elements[j] *elt)
            end
            if order == final_order
              return elements
            end
          end
        end
        rep_pos = rep_pos + previous_order
      end
    end
  end
  return elements
end

function small_generating_set(Aut::Array{NfToNfMor, 1})
  K = domain(Aut[1])
  a = gen(K)
  Identity = Aut[1]
  for i in 1:length(Aut)
    Au = Aut[i]
    if Au.prim_img == a
      Identity = Aut[i]
      break
    end
  end
  return small_generating_set(Aut, *, Identity)
end

################################################################################
#
#  GroupsofGroups
#
################################################################################

@doc Markdown.doc"""
     quotient(G::GrpGen, H::GrpGen, HtoG::GrpGenToGrpGenMor)
Returns the quotient group 'Q' = $G$/$H$ with canonical map $G$ -> $Q$.
"""
function quotient(G::GrpGen, H::GrpGen, HtoG::GrpGenToGrpGenMor)
  elems = elements(HtoG)
  if !_isnormal(elems)
      return @error("Subgroup is not normal")
  end
  elements_indx = [getindex(i) for i in elems]
  M = G.mult_table
  rows_2delete = Array{Int64,1}()
  cols_2delete = Array{Int64,1}()
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

  function quotient_op(A::Array{GrpGenElem,1}, B::Array{GrpGenElem,1})
     i = getindex(A[1]*B[1])
     j = findfirst(x->x == i, M)[2]
     return getindex.([G],M[:,j])
  end

  Q,SetGtoQ,QtoSetG = generic_group([getindex.(Ref(G),M[:,i]) for i in 1:size(M)[2]], quotient_op)

  image = Array{GrpGenElem,1}(undef, order(G))
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

function commutator_subgroup(G::GrpGen)
  normal_subgroups = subgroups(G,normal = true)
  #sort groups w.r.t order
  normal_subgroups = normal_subgroups[sortperm([order(i[1]) for i in normal_subgroups])]
  for (subgroup,StoG) in normal_subgroups
    if isabelian(quotient(G, subgroup, StoG)[1])
      return (subgroup,StoG)
    end
  end
end

function derived_series(G::GrpGen, n::Int64 = 2 * order(G))
  Res = Array{Tuple{GrpGen, GrpGenToGrpGenMor},1}()
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
  return G.mult_table == H.mult_table
end

elements(G::GrpGen) = collect(G)

elements(HtoG::GrpGenToGrpGenMor) = unique(HtoG.img)

function psylow_subgroup(G::GrpGen, p::Union{fmpz, Integer})
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

function conjugancy_classes(G::GrpGen)
  CC = Array{Array{GrpGenElem,1},1}()
  for x in collect(G)
    if true in in.(Ref(x), CC)##immer
      break
    end
    new_cc = Array{GrpGenElem,1}()
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
