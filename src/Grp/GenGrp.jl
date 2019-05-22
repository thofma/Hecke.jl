################################################################################
#
#  Generic group given by multiplication table
#
################################################################################

export generic_group, GrpGen, GrpGenElem, isabelian, iscyclic, order, elements, getindex, isbijective, isinjective, issurjective, subgroups,
       subgroup, quotient, image, kernel, elem_type, parent, psylow_subgroup, GrpGenToGrpGenMor, commutator_subgroup, derived_series,
       id_hom, find_small_group, order, direct_product, conjugancy_classes

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
      @error("There are only $og elements in $group")
    end
    return z = new(group, i)
  end
end

################################################################################
#
#  Compute generic group from anything
#
################################################################################
@doc Markdown.doc"""
     generic_group(G, op)
Computes group of $G$ with operation $op$, implemented with multiplication table 'G.mult_table'.
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

@doc Markdown.doc"""
    image(f::GrpGenToGrpGenMor, g::GrpGenElem) -> h::GrpGenElem
Returns the image of $g$ under $f$.
"""
function image(f::GrpGenToGrpGenMor, g::GrpGenElem)
  return f.img[g.i]
end

function Base.show(io::IO, f::GrpGenToGrpGenMor)
  println(io, "Morphism from group\n", f.domain, " to\n", f.codomain)
end

domain(f::GrpGenToGrpGenMor) = f.domain

codomain(f::GrpGenToGrpGenMor) = f.codomain

id_hom(G::GrpGen) = GrpGenToGrpGenMor(G, G, collect(G))

image(GtoH::GrpGenToGrpGenMor) = subgroup(GtoH.codomain, unique(GtoH.img))

kernel(GtoH::GrpGenToGrpGenMor) = subgroup(GtoH.domain, getindex.([GtoH.domain], findall(x->image(GtoH, x) == id(GtoH.codomain), collect(GtoH.domain))))

issurjective(GtoH::GrpGenToGrpGenMor) = order(GtoH.codomain) == length(unique(GtoH.img)) ? true : false
#finite groups
isinjective(GtoH::GrpGenToGrpGenMor) = issurjective(GtoH)

isbijective(GtoH::GrpGenToGrpGenMor) = issurjective(GtoH)

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
#  Automorphisms
#
################################################################################

# TODO: Cache the orders of the generators of the small_groups.
#       Do not recompute it here.
function find_small_group(G::GrpGen)
  l = order(G)

  elements_by_orders = Dict{Int, Array{GrpGenElem, 1}}()

  for i in 1:l
    g = G[i]
    o = order(g)
    if haskey(elements_by_orders, o)
      push!(elements_by_orders[o], g)
    else
      elements_by_orders[o] = [g]
    end
  end

  candidates = Int[]

  local ordershape

  for j in 1:length(small_groups_1_63[order(G)])
    ordershape = small_groups_1_63[order(G)][j][4]

    candidate = true
    for (o, no) in ordershape
      if !haskey(elements_by_orders, o)
        candidate = false
        break
      else
        elts = elements_by_orders[o]
        if length(elts) != no
          candidate = false
          break
        end
      end
     end

     if candidate
        push!(candidates, j)
     end
  end

  @assert length(candidates) > 0


  sort!(candidates, rev = true)

  idG = id(G)

  for j in candidates
    H = small_groups_1_63[order(G)][j]

    elbyord = [elements_by_orders[order(o)] for o in H[1]]

    it = Iterators.product(elbyord...)

    words = H[2]

    for poss in it
      is_hom = true
      for w in words
        if eval_word(collect(poss), w) != idG
          is_hom = false
          break
        end
      end

      if is_hom
        if length(closure(collect(poss), *, idG)) == order(G)
          return order(G), j
        end
      end
    end
  end
  throw(error("Could not identify group"))
end

function eval_word(S, w::Vector{Int})
  g = id(parent(S[1]))
  for i in 1:length(w)
    if w[i] > 0
      g = g * S[w[i]]
    else
      g = g * inv(S[-w[i]])
    end
  end
  return g
end

function automorphisms(i, j)
  Gdata = small_groups_1_63[i][j]
  P = PermGroup(i)
  G, _  = generic_group(closure([P(p) for p in Gdata[1]], *), *)

  l = order(G)

  elements_by_orders = Dict{Int, Array{GrpGenElem, 1}}()

  for i in 1:l
    g = G[i]
    o = order(g)
    if haskey(elements_by_orders, o)
      push!(elements_by_orders[o], g)
    else
      elements_by_orders[o] = [g]
    end
  end

  elbyord = [elements_by_orders[order(o)] for o in Gdata[1]]

  it = Iterators.product(elbyord...)

  words::Vector{Vector{Int}} = Gdata[2]

  idG = id(G)

  auts = _aut_group(it, words, idG, order(G))::Vector{Vector{GrpGenElem}}

  return auts
end

@noinline function _aut_group(it, words, idG, n)
  auts = Vector{GrpGenElem}[]
  for poss in it
    is_hom = true
    for w in words
      if eval_word(poss, w) != idG
        is_hom = false
        break
      end
    end

    if is_hom
      cposs = collect(poss)
      if length(closure(cposs, *, idG)) == n
        push!(auts, cposs)
      end
    end
  end

  return auts
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

  Q,SetGtoQ,QtoSetG = generic_group([getindex.([G],M[:,i]) for i in 1:size(M)[2]], quotient_op)

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
  return Res = sort([Hecke.find_small_group(Hecke.quotient(G, subgroups[i][1], subgroups[i][2])[1]) for i in 1:length(subgroups)])
  end

  function direct_product(G1::GrpGen, G2::GrpGen)
    S = [(g1,g2) for g1 in collect(G1), g2 in collect(G2)]
    directproduct_op(g1::Tuple{GrpGenElem,GrpGenElem}, g2::Tuple{GrpGenElem,GrpGenElem}) = (g1[1] * g2[1], g1[2] * g2[2])
    return generic_group(S, directproduct_op)
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
    if true in in.([x], CC)
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
