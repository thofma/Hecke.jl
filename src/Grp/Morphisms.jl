################################################################################
#
#  Morphism functionality
#
################################################################################

@doc raw"""
    image(f::MultTableGroupHom, g::MultTableGroupElem) -> h::MultTableGroupElem

Returns the image of $g$ under $f$.
"""
image(f::MultTableGroupHom, g::MultTableGroupElem) = f.img[g.i]

@doc raw"""
    preimage(f::MultTableGroupHom, g::MultTableGroupElem) -> h::MultTableGroupElem

Returns one element of the preimage of $g$ under $f$.
"""
function preimage(f::MultTableGroupHom, g::MultTableGroupElem)
  h = findfirst(x -> f(x) == g, collect(f.domain))
   if h === nothing
     error("$g has no preimage under $f")
   end
   return f.domain[h]
end

@doc raw"""
    has_preimage_with_preimage(f::MultTableGroupHom, g::MultTableGroupElem) -> (b::Bool, h::MultTableGroupElem)

Returns whether $g$ has a preimage under $f$. If so, the second return value is an
element $h$ with $f(h) = g$.
"""
function has_preimage_with_preimage(f::MultTableGroupHom, g::MultTableGroupElem)
  h = findfirst(x -> f(x) == g, collect(f.domain))
   if h === nothing
     return false, id(domain(f))
   end
   return (true, f.domain[h])
end

@doc raw"""
    *(f::MultTableGroupHom, g::MultTableGroupHom) -> h::MultTableGroupHom

Returns the composition $(f * g) = g(f)$.
"""
function *(f::MultTableGroupHom, g::MultTableGroupHom)
  return MultTableGroupHom(f.domain, g.codomain, [g(f(x)) for x in collect(f.domain)])
end

@doc raw"""
    inv(f::MultTableGroupHom) -> h::MultTableGroupHom

Assumes that $f$ is an isomorphism. Returns the inverse of $f$.
"""
function inv(f::MultTableGroupHom)
  return MultTableGroupHom(f.codomain, f.domain, collect(f.domain)[sortperm(getindex.(f.img))])
end

function Base.show(io::IO, f::MultTableGroupHom)
  println(io, "Morphism from group\n", f.domain, " to\n", f.codomain)
end

domain(f::MultTableGroupHom) = f.domain

codomain(f::MultTableGroupHom) = f.codomain

id_hom(G::MultTableGroup) = MultTableGroupHom(G, G, collect(G))

image(GtoH::MultTableGroupHom) = sub(GtoH.codomain, unique(GtoH.img))

function kernel(GtoH::MultTableGroupHom)
  G = GtoH.domain
  H = GtoH.codomain
  return sub(G, getindex.(Ref(G), findall(x-> GtoH(x) == id(H), collect(G))))
end

function is_surjective(GtoH::MultTableGroupHom)
  return order(GtoH.codomain) == length(unique(GtoH.img))
end
#finite groups
is_injective(GtoH::MultTableGroupHom) = is_surjective(GtoH)

is_bijective(GtoH::MultTableGroupHom) = is_surjective(GtoH)

(M::MultTableGroupToGroupHom)(g::MultTableGroupElem) = M.dict[g]

function (M::FinGenAbGroupToGroupHom)(g::GrpAbElem)
  elem = id(M.codomain)
  for i in 1:length(g.coeff)
    elem = elem * M.I[i]^g.coeff[i]
  end
  return elem
end

################################################################################
#
#  Find Morphisms
#
################################################################################

# TODO: Cache the orders of the generators of the small_groups.
#       Do not recompute it here.
function find_small_group(G::MultTableGroup; DB = DefaultSmallGroupDB())
  l = order(G)

  D = DB.db

  elements_by_orders = Dict{Int, Vector{MultTableGroupElem}}()

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

  for j in 1:length(D[order(G)])
    ordershape = D[order(G)][j].orderdis

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
    H = D[order(G)][j]

    elbyord = [elements_by_orders[order(o)] for o in H.gens]

    it = Iterators.product(elbyord...)

    words = H.rels

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
          # Found it!
          H = small_group(order(G), j, DB = DB)
          return (order(G), j), H, _spin_up_morphism(gens(H), collect(poss))
        end
      end
    end
  end
  error("Could not identify group")
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

@doc raw"""
    automorphism_list(G::MultTableGroup) -> A::Vector{MultTableGroupHom}

Returns all group isomorphisms from $G$ to $G$.
"""
function automorphism_list(G::MultTableGroup)
  Gn, GntoG = find_small_group(G)[2:3]
  auts = _automorphisms(Gn)
  return [inv(GntoG) * aut * GntoG for aut in auts]
end

function _automorphisms(G::MultTableGroup)
  @assert is_from_db(G)
  i, j = G.small_group_id
  Gdata = DefaultSmallGroupDB().db[i][j]

  l = order(G)

  elements_by_orders = Dict{Int, Vector{MultTableGroupElem}}()

  # TODO: I think the following is cached somewhere (in the database)
  for i in 1:l
    g = G[i]
    o = order(g)
    if haskey(elements_by_orders, o)
      push!(elements_by_orders[o], g)
    else
      elements_by_orders[o] = [g]
    end
  end

  elbyord = [elements_by_orders[order(G[o])] for o in G.gens]

  it = Iterators.product(elbyord...)

  words::Vector{Vector{Int}} = Gdata.rels

  idG = id(G)

  auts = _aut_group(it, words, idG, order(G))::Vector{Vector{MultTableGroupElem}}

  # Any element A of auts determines an isomorphism by mapping gens(G)[i] to A[i]

  Ggens = gens(G)

  # TODO: preallocate
  return [_spin_up_morphism(Ggens, a) for a in auts]
end

function _spin_up_morphism(domain::Vector{MultTableGroupElem}, codomain::Vector{MultTableGroupElem})
  @assert length(domain) > 0
  @assert length(domain) == length(codomain)
  G = parent(domain[1])
  H = parent(codomain[1])
  pairs = [(domain[i], codomain[i]) for i in 1:length(domain)]
  cl = closure(pairs, (x, y) -> (x[1]*y[1], x[2]*y[2]), (id(G), id(H)))
  img = Vector{MultTableGroupElem}(undef, length(G))
  for i in 1:length(G)
    img[cl[i][1][]] = cl[i][2]
  end
  phi = MultTableGroupHom(G, H, img)

  # TODO: Remove this assertion once this is battle tested
  for g in G
    for h in G
      @assert phi(g * h) == phi(g) * phi(h)
    end
  end
  return phi
end

@noinline function _aut_group(it, words, idG, n)
  auts = Vector{MultTableGroupElem}[]
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

function _morphisms_with_gens(G::MultTableGroup, H::MultTableGroup, Gens::Vector{MultTableGroupElem}, Rels::Vector{Vector{Int64}})

  l = order(H)

  elements_by_orders = Dict{Int, Vector{MultTableGroupElem}}()

  for i in 1:l
    h = H[i]
    o = order(h)
    for k in multiples(o, order(G))
      if haskey(elements_by_orders, k)
        push!(elements_by_orders[k], h)
      else
        elements_by_orders[k] = [h]
      end
    end
  end


  elbyord = [elements_by_orders[order(o)] for o in Gens]

  it = Iterators.product(elbyord...)

  words::Vector{Vector{Int}} = Rels

  idH = id(H)

  homs = _hom_group(it, words, idH)::Vector{Vector{MultTableGroupElem}}

  Ggens = Gens

  return [_spin_up_morphism(Ggens, a) for a in homs]
end

@doc raw"""
    morphisms(G::MultTableGroup, H::MultTableGroup) -> A::Vector{MultTableGroupHom}

Returns all group homomorphisms from $G$ to $H$.
"""
function morphisms(G::MultTableGroup, H::MultTableGroup)
  Gn, isom = find_small_group(G)[2:3]
  return [inv(isom) * mor for mor in _morphisms(Gn,H)]
end

function _morphisms(G::MultTableGroup, H::MultTableGroup)
  @assert is_from_db(G)
  i, j = G.small_group_id
  Gdata = DefaultSmallGroupDB().db[i][j]

  l = order(H)

  elements_by_orders = Dict{Int, Vector{MultTableGroupElem}}()

  for i in 1:l
    h = H[i]
    o = order(h)
    for k in multiples(o, order(G))
      if haskey(elements_by_orders, k)
        push!(elements_by_orders[k], h)
      else
        elements_by_orders[k] = [h]
      end
    end
  end

  elbyord = [elements_by_orders[order(G[o])] for o in G.gens]

  it = Iterators.product(elbyord...)

  words::Vector{Vector{Int}} = Gdata.rels

  idH = id(H)

  homs = _hom_group(it, words, idH)::Vector{Vector{MultTableGroupElem}}

  # Any element a of homs determines an homomorphism by mapping gens(G)[i] to A[i]

  Ggens = gens(G)

  # TODO: preallocate
  return [_spin_up_morphism(Ggens, a) for a in homs]
end

@noinline function _hom_group(it, words, idH)
  homs = Vector{MultTableGroupElem}[]
  for poss in it
    is_hom = true
    for w in words
      if eval_word(poss, w) != idH
        is_hom = false
        break
      end
    end

    if is_hom
      cposs = collect(poss)
      push!(homs, cposs)
    end
  end
  return homs
end

function inner_automorphisms(G::MultTableGroup)
  Ggens = gens(G)
  inner = [ _spin_up_morphism(Ggens, [h * g * inv(h) for g in gens(G)]) for h in G]
  I = unique!(inner)
  return I
end

function outer_automorphisms(G::MultTableGroup)
  A = automorphism_list(G)
  I = inner_automorphisms(G)
  res = eltype(A)[]
  tmp = Set{eltype(A)}()
  for a in A
    if a in tmp
      continue
    end
    push!(res, a )
    for i in I
      push!(tmp, i * a)
    end
    if length(tmp) == length(A)
      break
    end
  end
  return res
end

multiples(n::Int64, b::Int64) =  [i * n for i in 1:Int64(floor(b/n))]

function is_isomorphic_with_map(G::MultTableGroup, H::MultTableGroup)
  idG, A, AtoG = find_small_group(G)
  idH, B, BtoH = find_small_group(H)
  if idG != idH
    return false, id_hom(G) # I am too lazy
  else
    h = _spin_up_morphism(gens(A), gens(B)) # they must be equal
    return true, _spin_up_morphism(gens(G), [ BtoH(h(preimage(AtoG, g))) for g in gens(G)])
  end
end
