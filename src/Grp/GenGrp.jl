
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

# The elements are just 1..n and i * j = G.mult_table[i, j]
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
end

################################################################################
#
#  Compute generic group from anything
#
################################################################################

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

function getindex(G::GrpGen, i::Int)
  return GrpGenElem(G, i)
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

# Check if H is invariant under conjugaction by the generators of the group.
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

# Check if the cyclic group H with generator gen is invariant under
# conjugaction by the generators of the group.
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

# Iteratively built up subgroups from cyclic groups.
# Any subgroup is of the form <C_1,...C_k>, where k are cyclic subgroups.
function _subgroups(G::GrpGen; normal::Bool = false)
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

# TODO: Once the subfield code is merged, make subgroups return proper
# subgroups
function subgroups(G::GrpGen; order::Int = 0, index::Int = 0, normal::Bool = false)
  H = _subgroups(G, normal = normal)
  if order > 0
    return [h for h in H if length(h) == order]
  elseif index > 0
    return [h for h in H if divexact(length(G), length(h)) == index]
  else
    return H
  end
end

function _proper_subgroups(G::GrpGen; kw...)
  subs = subgroups(G; kw...)
  res = Vector{Tuple{GrpGen, GrpGenToGrpGenMor}}(undef, length(subs))
  for i in 1:length(subs)
    res[i] = subgroup(G, subs[i])
  end
  return res
end

# Assume that H is a subgroup of G, compute a generic group and an embedding.
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

function isabelian(G::GrpGen)
  return G.isabelian
end

function defines_abelian_group(m)
  return issymmetric(m)
end

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

function image(f::GrpGenToGrpGenMor, g::GrpGenElem)
  return f.img[g.i]
end

function Base.show(io::IO, f::GrpGenToGrpGenMor)
  println(io, "Morphism from group\n", f.domain, "to\n", f.codomain)
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
  elements = [NfToNfMor(K, K, gen(K))]
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
  K=Aut[1].header.domain
  a=gen(K)
  Identity = Aut[1]
  for i in 1:length(Aut)
    Au = Aut[i]
    if Au.prim_img == a
      Identity = Aut[i]
      break
    end
  end
  return  Hecke.small_generating_set(Aut, *, Identity)
end

################################################################################
#
#  Automorphisms
#
################################################################################

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

  for j in 1:length(groups_from_magma[order(G)])
    ordershape = groups_from_magma[order(G)][j][4]

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
  println("Candidate groups are $candidates")

  sort!(candidates, rev = true)

  idG = id(G)

  for j in candidates
    H = groups_from_magma[order(G)][j]

    elbyord = [elements_by_orders[o] for o in H[2]]

    it = Iterators.product(elbyord...)

    words = H[3]
    
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
          return true, j, poss
        end
      end
    end
  end

  return false
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
  Gdata = groups_from_magma[i][j]
  P = PermGroup(i)
  G = generic_group(closure([P(p) for p in Gdata[1]], *), *)

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

  elbyord = [elements_by_orders[o] for o in Gdata[2]]

  it = Iterators.product(elbyord...)

  words::Vector{Vector{Int}} = Gdata[3]

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
