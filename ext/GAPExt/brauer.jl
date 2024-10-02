################################################################################
#
#  Obstruction Interface
#
################################################################################

function Hecke.check_obstruction(list::Vector{FieldsTower}, L::GAP.GapObj,
           i::Int, invariants::Vector{Int})

  d = degree(list[1])
  common_degree = ppio(invariants[end], d)[1]
  @vprintln :BrauerObst 1 "Computing cocycles"
  cocycles = cocycles_computation(L, i)
  @vprintln :BrauerObst 1 "Computing isomorphisms"
  G = GAP.Globals.ImagesSource(cocycles[1].projection)
  if isone(common_degree)
    for F in list
      assure_isomorphism(F, G)
    end
    lproj = projections(cocycles[1].projection)
    for i = 1:length(list)
      list[i].projections_for_conductors = lproj
    end
    return list
  end
  if length(cocycles) > 1500
    #Try to do something about it.
    #The good thing would be to reduce to a subextension. Is this possible?
    #Of course!
    fl, Lnew = find_subgroup(L, i)
    if fl
      new_invariants = GAP.gap_to_julia(Vector{Int}, GAP.Globals.AbelianInvariants(GAP.Globals.FactorGroup(Lnew[2], Lnew[3])))
      new_invariants = map(Int, snf(abelian_group(new_invariants))[1].snf)
      list = check_obstruction(list, Lnew, 2, new_invariants)
    end
    for F in list
      assure_isomorphism(F, G)
    end
    lproj = projections(cocycles[1].projection)
    for i = 1:length(list)
      list[i].projections_for_conductors = lproj
      list[i].admissible_cocycles = cocycles
    end
    return list
  end
  for F in list
    assure_isomorphism(F, G)
  end
  fac = factor(common_degree)
  obstructions = Vector{Vector{Bool}}(undef, length(list))
  for i = 1:length(obstructions)
    obstructions[i] = falses(length(cocycles))
  end
  for (p, v) in fac
    @vprintln :BrauerObst 1 "Checking obstructions at $p"
    cocycles_p_start = cocycle_ctx[_to_prime_power_kernel(x, Int(p)) for x in cocycles]
    indices_non_split = Int[]
    for i = 1:length(cocycles_p_start)
      @vprintln :BrauerObst 1 "Checking if cocycle $i splits"
      if !iszero(cocycles_p_start[i])
        push!(indices_non_split, i)
      end
    end
    if isempty(indices_non_split)
      continue
    end
    cocycles_p = cocycles_p_start[indices_non_split]
    if length(invariants) == 1 || is_coprime(invariants[end-1], p)
      for i = 1:length(list)
        @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())Fields to test: $(length(list)-i+1)"
        if !all(obstructions[i])
          obstructions_i = check_obstruction(list[i], cocycles_p, Int(p), obstructions[i])
          for j = 1:length(obstructions_i)
            obstructions[i][indices_non_split[j]] = obstructions_i[j]
          end
        end
      end
      @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())"
    else
      all_cocycles = Vector{Vector{cocycle_ctx}}(undef, length(cocycles))
      for i = 1:length(cocycles)
        all_cocycles[i] = _cocycles_with_cyclic_kernel(cocycles_p[i], Int(p))
      end
      for i = 1:length(list)
        @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())Fields to test: $(length(list)-i+1)"
        if !all(obstructions[i])
          obstructions_i = check_obstruction_non_cyclic(list[i], all_cocycles, Int(p), obstructions[i])
          for j = 1:length(obstructions_i)
            obstructions[i][indices_non_split[j]] = obstructions_i[j]
          end
        end
      end
      @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())"
    end
  end
  #Now, extract the list
  new_list = Vector{FieldsTower}()
  for i = 1:length(list)
    indices = Int[j for j = 1:length(obstructions[i]) if !(obstructions[i][j])]
    if isempty(indices)
      continue
    end
    list[i].admissible_cocycles = cocycles[indices]
    list[i].projections_for_conductors = [x.projection for x in list[i].admissible_cocycles]
    push!(new_list, list[i])
  end
  return new_list
end


function Hecke.check_obstruction(F::FieldsTower, cocycles::Vector{cocycle_ctx},
                            p::Int, obstruction_at::Vector{Bool})
  #I assume that the kernel of the embedding problem is a p-group
  @assert is_prime(p)
  indices = [i for i = 1:length(obstruction_at) if !obstruction_at[i]]
  cocycles_to_test = cocycles[indices]
  for i = 1:length(cocycles)
    _cocycle_to_exponent!(cocycles[i])
  end
  obstruction = check_obstruction_cyclic(F, cocycles, p)
  for i = 1:length(obstruction)
    if obstruction[i]
      obstruction_at[indices[i]] = true
    end
  end
  return obstruction_at
end

################################################################################
#
#  Reduction when there are too many cocycles
#
################################################################################


function find_subgroup(L::GAP.GapObj, level::Int)
  GG = L[1]
  HH = L[level+1]
  KK = L[level]
  proj = GAP.Globals.NaturalHomomorphismByNormalSubgroup(GG, HH)
  target_grp = GAP.Globals.ImagesSource(proj)
  Ke = GAP.Globals.Image(proj, KK)
  lS = GAP.Globals.CharacteristicSubgroups(target_grp)
  candidate = L[1]
  found = false
  for i = 1:length(lS)
    if !GAP.Globals.IsSubgroup(Ke, lS[i])
      continue
    end
    if GAP.Globals.Size(lS[i]) == GAP.Globals.Size(Ke) || GAP.Globals.Size(lS[i]) == 1
      continue
    end
    if !found
      found = true
      candidate = lS[i]
    elseif GAP.Globals.Size(lS[i]) < GAP.Globals.Size(candidate)
      candidate = lS[i]
    end
  end
  if !found
    return found, GAP.GapObj([candidate])
  end
  #I need to change the series...
  L1 = GAP.GapObj[]
  proj1 = GAP.Globals.NaturalHomomorphismByNormalSubgroup(target_grp, candidate)
  push!(L1, GAP.Globals.ImagesSource(proj1))
  proj_comp = proj*proj1
  for i = level:length(L)
    push!(L1, GAP.Globals.Image(proj_comp, L[i]))
  end
  return found, GAP.GapObj(L1)
end

################################################################################
#
#  IsZero for a cocycle
#
################################################################################

function Base.iszero(c::cocycle_ctx)
  E = GAP.Globals.Source(c.projection)
  A = GAP.Globals.Image(c.inclusion)
  return !iszero(length(GAP.Globals.ComplementClassesRepresentatives(E, A)))
end


################################################################################
#
#  Non cyclic kernel case
#
################################################################################

function check_obstruction_non_cyclic(F::FieldsTower, cocycles::Vector{Vector{cocycle_ctx}},
                                       p::Int, obstruction_at::Vector{Bool})

  indices = Int[i for i = 1:length(obstruction_at) if !obstruction_at[i]]
  new_cocycles = cocycles[indices]
  for j = 1:length(new_cocycles)
    for i = 1:length(new_cocycles[j])
      if check_obstruction_cyclic(F, [new_cocycles[j][i]], p)[1]
        obstruction_at[indices[j]] = true
        break
      end
    end
  end
  return obstruction_at
end


function _to_prime_power_groups(cocycle::cocycle_ctx, p::Int)
  #the kernel is already of prime power order.
  #I need to work with the projection.
  proj = cocycle.projection
  E = GAP.Globals.Source(proj)
  n = GAP.Globals.Size(E)
  np, nq = ppio(n, p)
  if isone(nq)
    return cocycle
  end
  inc = cocycle.inclusion
  A = GAP.Globals.Source(inc)
  G = GAP.Globals.ImagesSource(proj)
  Ep = GAP.Globals.SylowSubgroup(E, p)
  gensEp = GAP.Globals.GeneratorsOfGroup(Ep)
  inj_Ep = GAP.Globals.GroupHomomorphismByImages(Ep, E, gensEp, gensEp)
  imgs_new_proj = []
  for i = 1:length(gensEp)
    push!(imgs_new_proj, GAP.Globals.Image(proj, gensEp[i]))
  end
  imgs_proj = GAP.GapObj(imgs_new_proj)
  Gp = GAP.Globals.Subgroup(G, imgs_proj)
  #I need the inclusion of Gp into G for strange (GAP) reasons.
  gensGp = GAP.Globals.GeneratorsOfGroup(Gp)
  inclusion_Gp = GAP.Globals.GroupHomomorphismByImages(Gp, G, gensGp, gensGp)
  #now the maps.
  new_proj = GAP.Globals.GroupHomomorphismByImages(Ep, Gp, gensEp, imgs_proj)
  images_inclusion = []
  gensA = GAP.Globals.GeneratorsOfGroup(A)
  for i = 1:length(gensA)
    el = GAP.Globals.Image(inc, gensA[i])
    prel = GAP.Globals.PreImagesRepresentative(inj_Ep, el)
    push!(images_inclusion, prel)
  end
  imgs_inclusion = GAP.GapObj(images_inclusion)
  new_incl = GAP.Globals.GroupHomomorphismByImages(A, Ep, gensA, imgs_inclusion)
  res =  cocycle_ctx(new_proj, new_incl, cocycle.cocycle)
  res.inclusion_of_pSylow = inclusion_Gp
  return res
end


#Careful, I am discarding the cocycles that represent split extensions
function  _cocycles_with_cyclic_kernel(old_cocycle::cocycle_ctx, p::Int)
  cocycle = _to_prime_power_groups(old_cocycle, p)
  proj = cocycle.projection
  inc = cocycle.inclusion
  E = GAP.Globals.Source(proj)
  normal_subgroups = GAP.Globals.NormalSubgroups(E)
  G = GAP.Globals.ImagesSource(proj)
  K = GAP.Globals.Source(inc)
  oK = GAP.Globals.Size(K)
  normal_cyclic_and_contained = GAP.GapObj[]
  for i = 1:length(normal_subgroups)
    g = normal_subgroups[i]
    oG = GAP.Globals.Size(g)
    if !GAP.Globals.IsSubgroup(K, g) || oG == oK
      continue
    end
    prmg = GAP.Globals.PreImage(inc, g)
    fg = GAP.Globals.FactorGroup(K, prmg)
    order = ZZRingElem(GAP.gap_to_julia(Int, GAP.Globals.Size(fg)))
    np = remove(order, p)[2]
    if isone(np) && GAP.Globals.IsCyclic(fg)
      push!(normal_cyclic_and_contained, prmg)
    end
  end
  #Almost done. I only want the minimal ones, so I need to sieve.
  res = GAP.GapObj[]
  for i = 1:length(normal_cyclic_and_contained)
    g = normal_cyclic_and_contained[i]
    found = false
    for j = 1:length(normal_cyclic_and_contained)
      if j != i && GAP.Globals.IsSubgroup(g, normal_cyclic_and_contained[j])
        found = true
        break
      end
    end
    if !found
      push!(res, g)
    end
  end
  #Great! Now, create the corresponding cocycles.
  res_coc =  [_to_subgroup_of_kernel(cocycle, x) for x in res]
  final_res = Vector{cocycle_ctx}()
  for c in res_coc
    if !iszero(c)
      _cocycle_to_exponent!(c)
      push!(final_res, c)
    end
  end
  return final_res
end

function _to_subgroup_of_kernel(cocycle::cocycle_ctx, S)
  A = GAP.Globals.Source(cocycle.inclusion)
  E = GAP.Globals.Source(cocycle.projection)
  G = GAP.Globals.ImagesSource(cocycle.projection)
  sizeG = GAP.Globals.Size(G)
  pr = GAP.Globals.NaturalHomomorphismByNormalSubgroup(A, S)
  #I still need to create the maps.
  pr1 = GAP.Globals.NaturalHomomorphismByNormalSubgroup(E, GAP.Globals.Image(cocycle.inclusion, S))
  E_new = GAP.Globals.ImagesSource(pr1)
  A_new = GAP.Globals.ImagesSource(pr)
  gensA_new = GAP.Globals.GeneratorsOfGroup(A_new)
  images_inclusion = GAP.GapObj[]
  for i = 1:length(gensA_new)
    el_A = GAP.Globals.PreImagesRepresentative(pr, gensA_new[i])
    el_E = GAP.Globals.Image(cocycle.inclusion, el_A)
    push!(images_inclusion, GAP.Globals.Image(pr1, el_E))
  end
  inclusion = GAP.Globals.GroupHomomorphismByImages(A_new, E_new, gensA_new, GAP.GapObj(images_inclusion))
  gensE_new = GAP.Globals.GeneratorsOfGroup(E_new)
  images_proj = []
  for i = 1:length(gensE_new)
    el = GAP.Globals.PreImagesRepresentative(pr1, gensE_new[i])
    push!(images_proj, GAP.Globals.Image(cocycle.projection, el))
  end
  projection = GAP.Globals.GroupHomomorphismByImages(E_new, G, gensE_new, GAP.GapObj(images_proj))
  local new_coc
  let cocycle = cocycle, pr = pr
    function new_coc(x::GAP.GapObj, y::GAP.GapObj)
      return GAP.Globals.Image(pr, cocycle.cocycle(x, y))
    end
  end
  res = cocycle_ctx(projection, inclusion, new_coc)
  if isdefined(cocycle, :inclusion_of_pSylow)
    res.inclusion_of_pSylow = cocycle.inclusion_of_pSylow
  end
  return res
end


function _to_prime_power_kernel(cocycle::cocycle_ctx, p::Int)
  A = GAP.Globals.Source(cocycle.inclusion)
  n = GAP.Globals.Size(A)
  np, nq = ppio(n, p)
  if isone(nq)
    return cocycle
  end
  gens = GAP.Globals.MinimalGeneratingSet(A)
  gens_sub = []
  for i = 1:length(gens)
    push!(gens_sub, gens[i]^np)
  end
  E = GAP.Globals.Source(cocycle.projection)
  G = GAP.Globals.ImagesSource(cocycle.projection)
  sizeG = GAP.Globals.Size(G)
  S = GAP.Globals.Subgroup(A, GAP.GapObj(gens_sub))
  pr = GAP.Globals.NaturalHomomorphismByNormalSubgroup(A, S)
  #I still need to create the maps.
  S1 = GAP.Globals.Image(cocycle.inclusion, S)
  pr1 = GAP.Globals.NaturalHomomorphismByNormalSubgroup(E, S1)
  E_new = GAP.Globals.ImagesSource(pr1)
  A_new = GAP.Globals.ImagesSource(pr)
  gensA_new = GAP.Globals.GeneratorsOfGroup(A_new)
  images_inclusion = []
  for i = 1:length(gensA_new)
    el_A = GAP.Globals.PreImagesRepresentative(pr, gensA_new[i])
    el_E = GAP.Globals.Image(cocycle.inclusion, el_A)
    push!(images_inclusion, GAP.Globals.Image(pr1, el_E))
  end
  inclusion = GAP.Globals.GroupHomomorphismByImages(A_new, E_new, gensA_new, GAP.GapObj(images_inclusion))
  gensE_new = GAP.Globals.GeneratorsOfGroup(E_new)
  images_proj = []
  for i = 1:length(gensE_new)
    el = GAP.Globals.PreImagesRepresentative(pr1, gensE_new[i])
    push!(images_proj, GAP.Globals.Image(cocycle.projection, el))
  end
  projection = GAP.Globals.GroupHomomorphismByImages(E_new, G, gensE_new, GAP.GapObj(images_proj))
  local new_coc
  let cocycle = cocycle, pr = pr
    function new_coc(x::GAP.GapObj, y::GAP.GapObj)
      return GAP.Globals.Image(pr, cocycle.cocycle(x, y))
    end
  end
  return cocycle_ctx(projection, inclusion, new_coc)
end

################################################################################
#
#  Isomorphism computation
#
################################################################################

function assure_isomorphism(F::FieldsTower, G)
  assure_automorphisms(F)
  K = F.field
  autsK = automorphism_list(K, copy = false)
  permGC = _from_autos_to_perm(autsK)
  Gperm = _perm_to_gap_grp(permGC)
  iso = GAP.Globals.IsomorphismGroups(Gperm, G)
  D = Dict{Hecke.morphism_type(AbsSimpleNumField, AbsSimpleNumField), GAP.GapObj}()
  for i = 1:length(autsK)
    permgap = _perm_to_gap_perm(permGC[i])
    k = GAP.Globals.Image(iso, permgap)
    D[autsK[i]] = k
  end
  F.isomorphism = D
  return nothing
end

################################################################################
#
#  Enumerate embedding problems
#
################################################################################

function _autos_to_check(G::GAP.GapObj, K::GAP.GapObj, E::GAP.GapObj, mG::GAP.GapObj)
  AutG = GAP.Globals.AutomorphismGroup(G)
  AutK = GAP.Globals.AutomorphismGroup(K)
  AutE = GAP.Globals.AutomorphismGroup(E)
  @vprintln :BrauerObst 1 "Automorphism Groups computed"
  isoAutG = GAP.Globals.IsomorphismPermGroup(AutG)
  isoAutK = GAP.Globals.IsomorphismPermGroup(AutK)

  permAutG = GAP.Globals.ImagesSource(isoAutG)
  permAutK = GAP.Globals.ImagesSource(isoAutK)
  #I want to construct the map between the automorphism groups. The kernel is characteristic!
  gens = GAP.Globals.GeneratorsOfGroup(AutE)
  ind_auts_quo = Vector{GAP.GapObj}(undef, length(gens))
  ind_auts_sub = Vector{GAP.GapObj}(undef, length(gens))
  gK = GAP.Globals.GeneratorsOfGroup(K)
  for s = 1:length(gens)
    ind_auts_quo[s] = GAP.Globals.Image(isoAutG, GAP.Globals.InducedAutomorphism(mG, gens[s]))
    igK = GAP.GapObj([GAP.Globals.Image(gens[s], gK[i]) for i = 1:length(gK)])
    h = GAP.Globals.GroupHomomorphismByImages(K, K, gK, igK)
    ind_auts_sub[s] = GAP.Globals.Image(isoAutK, h)
  end
  GProd = GAP.Globals.DirectProduct(permAutG, permAutK)
  EmbAutG = GAP.Globals.Embedding(GProd, 1)
  EmbAutK = GAP.Globals.Embedding(GProd, 2)
  gensubs = Vector{GAP.GapObj}(undef, length(gens))
  for s = 1:length(gens)
    gensubs[s] = GAP.Globals.Image(EmbAutG, ind_auts_quo[s]) * GAP.Globals.Image(EmbAutK, ind_auts_sub[s])
  end
  S = GAP.Globals.Subgroup(GProd, GAP.GapObj(gensubs))
  @vprintln :BrauerObst 1 "Map constructed. Enumerating cosets..."
  Transv = GAP.Globals.RightTransversal(GProd, S)
  Tperm = GAP.Globals.List(Transv)
  #Now, I have to recover the automorphisms in AutG and AutK
  ProjAutG = GAP.Globals.Projection(GProd, 1)
  ProjAutK = GAP.Globals.Projection(GProd, 2)
  res = Vector{Tuple{GAP.GapObj, GAP.GapObj}}(undef, length(Tperm))
  for i = 1:length(Tperm)
    res[i] = (GAP.Globals.PreImagesRepresentative(isoAutG, GAP.Globals.Image(ProjAutG, Tperm[i])), GAP.Globals.PreImagesRepresentative(isoAutK, GAP.Globals.Image(ProjAutK,  Tperm[i])))
  end
  return res
end


function projections(mG::GAP.GapObj)
  G = GAP.Globals.ImagesSource(mG)
  E = GAP.Globals.Source(mG)
  AutG = GAP.Globals.AutomorphismGroup(G)
  AutE = GAP.Globals.AutomorphismGroup(E)
  @vprintln :BrauerObst 1 "Automorphism Groups computed"
  isoAutG = GAP.Globals.IsomorphismPermGroup(AutG)
  permAutG = GAP.Globals.ImagesSource(isoAutG)
  #I want to construct the map between the automorphism groups. The kernel is characteristic!
  gens = GAP.Globals.GeneratorsOfGroup(AutE)
  gens_img = Vector{GAP.GapObj}(undef, length(gens))
  for s = 1:length(gens)
    gens_img[s] = GAP.Globals.Image(isoAutG, GAP.Globals.InducedAutomorphism(mG, gens[s]))
  end
  S = GAP.Globals.Subgroup(permAutG, GAP.GapObj(gens_img))
  @vprintln :BrauerObst 1 "Map constructed. Enumerating cosets..."
  Transv = GAP.Globals.RightTransversal(permAutG, S)
  Tperm = GAP.Globals.List(Transv)
  #Now, I have to recover the automorphisms in AutG and AutK
  res = Vector{GAP.GapObj}(undef, length(Tperm))
  for i = 1:length(Tperm)
    res[i] = mG*GAP.Globals.PreImagesRepresentative(isoAutG, Tperm[i])
  end
  return res
end

function cocycles_computation(L::GAP.GapObj, level::Int)
  return cocycles_computation(L[1], L[level+1], L[level])
end


function cocycles_computation(GG, HH, KK)

  proj = GAP.Globals.NaturalHomomorphismByNormalSubgroup(GG, HH)
  target_grp = GAP.Globals.ImagesSource(proj)
  mH1 = GAP.Globals.NaturalHomomorphismByNormalSubgroup(target_grp, GAP.Globals.Image(proj, KK))
  H1 = GAP.Globals.ImagesSource(mH1)
  K = GAP.Globals.Kernel(mH1)

  Elems = GAP.Globals.Elements(H1)
  MatCoc = Matrix{GAP.GapObj}(undef, length(Elems), length(Elems))
  Preimags = Vector{GAP.GapObj}(undef, length(Elems))
  for i = 1:length(Elems)
    Preimags[i] = GAP.Globals.PreImagesRepresentative(mH1, Elems[i])
  end
  for i = 1:length(Elems)
    x1 = Preimags[i]
    for j = 1:length(Elems)
      y1 = Preimags[j]
      xy = Elems[i] * Elems[j]
      k = 1
      while Elems[k] != xy
        k += 1
      end
      xy1 = Preimags[k]
      MatCoc[i, j] = x1*y1*GAP.Globals.Inverse(xy1)
    end
  end

  @vprintln :BrauerObst 1 "Listing automorphisms"
  autos = _autos_to_check(H1, K, target_grp, mH1)
  cocycles = Vector{cocycle_ctx}(undef, length(autos))
  for i = 1:length(autos)
    aut1, aut2 = autos[i]
    local cocycle
    let Elems = Elems, MatCoc = MatCoc, aut1 = aut1, aut2 = aut2, Elems = Elems
      function cocycle(x::GAP.GapObj, y::GAP.GapObj)
        new_x = GAP.Globals.PreImagesRepresentative(aut1, x)
        new_y = GAP.Globals.PreImagesRepresentative(aut1, y)
        ind1 = 1
        while Elems[ind1] != new_x
          ind1 += 1
        end
        ind2 = 1
        while Elems[ind2] != new_y
          ind2 += 1
        end
        return GAP.Globals.PreImagesRepresentative(aut2, MatCoc[ind1, ind2])
      end
    end
    #I change aut2 so that its codomain is really target_grp
    new_aut2 = aut2*GAP.Globals.GroupHomomorphismByImages(K, target_grp, GAP.Globals.GeneratorsOfGroup(K), GAP.Globals.GeneratorsOfGroup(K))
    cocycles[i] = cocycle_ctx(mH1*aut1, new_aut2, cocycle)
  end
  return cocycles

end

function _cocycle_to_exponent!(cocycle::cocycle_ctx)
  if isdefined(cocycle, :gen_kernel)
    return nothing
  end
  gen = GAP.Globals.MinimalGeneratingSet(GAP.Globals.Source(cocycle.inclusion))[1]
  local cocycle_val
  let cocycle = cocycle, gen = gen
    function cocycle_val(x::GAP.GapObj, y::GAP.GapObj)
      return _find_exp(gen, cocycle.cocycle(x, y))
    end
  end
  cocycle.values_cyclic = cocycle_val
  cocycle.gen_kernel = gen
  return nothing
end

function _find_exp(x::GAP.GapObj, y::GAP.GapObj)
  if GAP.Globals.One(x) == y
    return 0
  end
  # I want to find i such that x^i = y
  i = 1
  z = GAP.Globals.ShallowCopy(x)
  while z != y
    z = z*x
    i += 1
  end
  #@assert x^i == y
  return i
end

###############################################################################
#
#  P-Sylow subgroup
#
###############################################################################

function pSylow(Gperm::GAP.GapObj, permGAP::Vector{GAP.GapObj}, G::Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, p::Int)
  p2 = is_perfect_power_with_data(length(G))[2]
  if p == p2
    return G
  end
  H = GAP.Globals.SylowSubgroup(Gperm, p)
  lGp = GAP.Globals.Size(H)
  Gp = Vector{Hecke.Hecke.morphism_type(AbsSimpleNumField, AbsSimpleNumField)}(undef, lGp)
  j = 1
  for ind = 1:length(G)
    if j > lGp
      break
    end
    if GAP.Globals.IN(permGAP[ind], H)
      Gp[j] = G[ind]
      j += 1
    end
  end
  return Gp
end

function pSylow(G::Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, p::Int)
  com, uncom = ppio(length(G), p)
  if uncom == 1
    return G
  end
  permGC = _from_autos_to_perm(G)
  Gperm = _perm_to_gap_grp(permGC)
  PermGAP = Vector{GAP.GapObj}(undef, length(permGC))
  for w = 1:length(permGC)
    PermGAP[w] = _perm_to_gap_perm(permGC[w])
  end
  return pSylow(Gperm, PermGAP, G, p)
end

################################################################################
#
#  Setup of cyclotomic extension
#
################################################################################

function _ext_cycl(G::Vector{<:Hecke.NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, d::Int)
  K = domain(G[1])
  Kc = cyclotomic_extension(K, d, compute_maximal_order = true, compute_LLL_basis = false, cached = false)
  automorphism_list(Kc; gens = G, copy = false)
  return Kc
end


################################################################################
#
#  Obstruction cyclic prime case
#
################################################################################

function check_obstruction_prime(F::FieldsTower, cocycles::Vector{cocycle_ctx}, p::Int)
  if p == 2
    return _obstruction_prime_no_extend(F, cocycles, p)
  end
  K = F.field
  OK = maximal_order(K)
  T, mT = torsion_unit_group(OK)
  if is_divisible_by(order(T), ZZRingElem(p))
    return _obstruction_prime_no_extend(F, cocycles, p)
  end
  lp = ramified_primes(F)
  if all(x -> (isone(mod(x, p)) || x == p), lp)
     return _obstruction_prime_no_extend(F, cocycles, p)
  end
  #bad case.
  return _obstruction_prime(F, cocycles, p)
end

function _obstruction_prime_no_extend(x::FieldsTower, cocycles, p::Int)
  K = x.field
  OK = maximal_order(K)
  GC = automorphism_list(K, copy = false)
  D = x.isomorphism
  Pcomp = 2
  R = Native.GF(Pcomp, cached = false)
  Rx = polynomial_ring(R, "x", cached = false)[1]
  ff = Rx(K.pol)
  while iszero(mod(p, Pcomp)) || iszero(discriminant(ff))
    Pcomp = next_prime(Pcomp)
    R = Native.GF(Pcomp, cached = false)
    Rx = polynomial_ring(R, "x", cached = false)[1]
    ff = Rx(K.pol)
  end
  permGC = _from_autos_to_perm(GC)
  Gperm = _perm_to_gap_grp(permGC)
  PermGAP = Vector{GAP.GapObj}(undef, length(permGC))
  for w = 1:length(permGC)
    PermGAP[w] = _perm_to_gap_perm(permGC[w])
  end
  #Restrict to the p-Sylow
  H = GAP.Globals.ImagesSource(cocycles[1].projection)
  if p != 2 || GAP.Globals.Size(H) != degree(K)
    Gp = pSylow(Gperm, PermGAP, GC, p)
  else
    Gp = GC
  end
  D1 = Dict{fpPolyRingElem, GAP.GapObj}()
  for g in GC
    pol = Rx(image_primitive_element(g))
    el = D[g]
    D1[pol] = el
  end
  obstruction = falses(length(cocycles))
  for i = 1:length(obstruction)
    if isdefined(cocycles[i], :inclusion_of_pSylow)
      #I need to assert that I took the right pSylow.
      Gp1 = Hecke.morphism_type(AbsSimpleNumField, AbsSimpleNumField)[]
      for g in GC
        el = D1[Rx(image_primitive_element(g))]
        if GAP.Globals.IN(el, GAP.Globals.Image(cocycles[i].inclusion_of_pSylow))
          push!(Gp1, g)
        end
      end
      Gp = Gp1
    end
    #I create the cocycle
    local cocycle
    let D1 = D1, i = i, p = p
      function cocycle(aut1::fpPolyRingElem, aut2::fpPolyRingElem)
        el1 = D1[aut1]
        el2 = D1[aut2]
        if isdefined(cocycles[i], :inclusion_of_pSylow)
          el1 = GAP.Globals.PreImagesRepresentative(cocycles[i].inclusion_of_pSylow, el1)
          el2 = GAP.Globals.PreImagesRepresentative(cocycles[i].inclusion_of_pSylow, el2)
        end
        res = cocycles[i].values_cyclic(el1, el2)
        return mod(res, p)::Int
      end
    end
    #Now, we have to see if it splits
    if !issplit_cpa(x, Gp, cocycle, p, 1, Rx)
      obstruction[i] = true
    end
  end
  return obstruction
end

function _obstruction_prime(x::FieldsTower, cocycles::Vector{cocycle_ctx}, p)
  K = x.field
  lp = ramified_primes(x)
  Kc = _ext_cycl(x.generators_of_automorphisms, p)
  K1 = Kc.Ka
  D = x.isomorphism
  autsK = automorphism_list(K, copy = false)
  autsK1 = automorphism_list(K1, copy = false)
  restr = restriction(autsK1, autsK, Kc.mp[2])
  #I construct the group and the isomorphisms between the automorphisms and the gap group.
  permGC = _from_autos_to_perm(autsK)
  Gperm = _perm_to_gap_grp(permGC)
  Pcomp = 2
  R = Native.GF(Pcomp, cached = false)
  Rx = polynomial_ring(R, "x", cached = false)[1]
  ff1 = Rx(K.pol)
  ff2 = Rx(K1.pol)
  while iszero(mod(p, Pcomp)) || iszero(discriminant(ff1)) || iszero(discriminant(ff2))
    Pcomp = next_prime(Pcomp)
    R = Native.GF(Pcomp, cached = false)
    Rx = polynomial_ring(R, "x", cached = false)[1]
    ff1 = Rx(K.pol)
    ff2 = Rx(K1.pol)
  end
  fmod = Rx(K.pol)
  dautsK1 = Dict{fpPolyRingElem, Int}()
  for w = 1:length(autsK1)
    dautsK1[Rx(image_primitive_element(autsK1[w]))] = w
  end
  #Restrict to the p-Sylow
  #Unfortunately, I need to compute the group structure.
  Gp = pSylow(autsK1, p)
  D1 = Dict{fpPolyRingElem, GAP.GapObj}()
  for g in Gp
    pol = Rx(image_primitive_element(g))
    indg = restr[dautsK1[pol]]
    el = D[autsK[indg]]
    D1[pol] = el
  end
  obstruction = falses(length(cocycles))
  for i = 1:length(obstruction)
    #I create the cocycle
    local cocycle
    let D1 = D1, cocycles = cocycles, p = p
      function cocycle(aut1::fpPolyRingElem, aut2::fpPolyRingElem)
        s1 = D1[aut1]
        s2 = D1[aut2]
        if isdefined(cocycles[i], :inclusion_of_pSylow)
          s1 = GAP.Globals.PreImagesRepresentative(cocycles[i].inclusion_of_pSylow, s1)
          s2 = GAP.Globals.PreImagesRepresentative(cocycles[i].inclusion_of_pSylow, s2)
        end
        rescoc = cocycles[i].values_cyclic(s1, s2)
        return mod(rescoc, p)::Int
      end
    end

    if !issplit_cpa(x, Gp, cocycle, p, 1, Rx)
      obstruction[i] = true
    end
  end
  return obstruction
end



################################################################################
#
#  Obstruction cyclic prime power
#
################################################################################

function action_on_roots(G::Vector{<: NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, zeta::AbsSimpleNumFieldElem, pv::Int)
  act_on_roots = Vector{Int}(undef, length(G))
  p = 11
  K = domain(G[1])
  Qx = parent(K.pol)
  R = Native.GF(p, cached = false)
  Rx, x = polynomial_ring(R, "x", cached = false)
  fmod = Rx(K.pol)
  while iszero(discriminant(fmod)) || iszero(mod(pv, p))
    p = next_prime(p)
    R = Native.GF(p, cached = false)
    Rx, x = polynomial_ring(R, "x", cached = false)
    fmod = Rx(K.pol)
  end
  polsG = fpPolyRingElem[Rx(image_primitive_element(g)) for g in G]
  zetaP = Rx(zeta)
  units = Vector{fpPolyRingElem}(undef, pv-1)
  units[1] = zetaP
  for i = 2:pv-1
    units[i] = mod(units[i-1]*zetaP, fmod)
  end
  for w = 1:length(G)
    act = Hecke.compose_mod(zetaP, polsG[w], fmod)
    s = 1
    while act != units[s]
      s += 1
    end
    act_on_roots[w] = s
    #@assert G[w](zeta) == zeta^s
  end
  return act_on_roots
end

function restriction(autsK1::Vector{<: NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, autsK::Vector{<: NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, mp::NumFieldHom{AbsSimpleNumField, AbsSimpleNumField})
  K = domain(mp)
  K1 = codomain(mp)
  p = 11
  R = Native.GF(p, cached = false)
  Rx, x = polynomial_ring(R, "x", cached = false)
  ff1 = Rx(K.pol)
  fmod = Rx(K1.pol)
  while iszero(discriminant(ff1)) || iszero(discriminant(fmod))
    p = next_prime(p)
    R = Native.GF(p, cached = false)
    Rx, x = polynomial_ring(R, "x", cached = false)
    ff1 = Rx(K.pol)
    fmod = Rx(K1.pol)
  end
  mp_pol = Rx(image_primitive_element(mp))
  imgs = Vector{fpPolyRingElem}(undef, length(autsK))
  for i = 1:length(imgs)
    imgs[i] = Hecke.compose_mod(Rx(image_primitive_element(autsK[i])), mp_pol, fmod)
  end
  res = Vector{Int}(undef, length(autsK1))
  for i = 1:length(res)
    img = Hecke.compose_mod(mp_pol, Rx(image_primitive_element(autsK1[i])), fmod)
    for j = 1:length(autsK)
      if img == imgs[j]
        res[i] = j
        break
      end
    end
    #@assert mp(image_primitive_element(autsK[res[i]])) == autsK1[i](image_primitive_element(mp))
  end
  return res
end


function check_obstruction_cyclic(F::FieldsTower, cocycles::Vector{cocycle_ctx}, p::Int)
  n = GAP.Globals.Size(GAP.Globals.Source(cocycles[1].inclusion))
  obstruction = check_obstruction_prime(F, cocycles, p)
  if n == p || all(obstruction)
    return obstruction
  end
  indices = [i for i = 1:length(obstruction) if !obstruction[i]]
  new_cocycles = cocycles[indices]
  obstruction_new = check_obstruction_pp(F, new_cocycles, n)
  for i = 1:length(indices)
    if obstruction_new[i]
      obstruction[indices[i]] = true
    end
  end
  return obstruction
end

function check_obstruction_pp(F::FieldsTower, cocycles::Vector{cocycle_ctx}, n::Int)
  #=
  lp = ramified_primes(F)
  assure_automorphisms(F)

  v, p = is_perfect_power_with_data(n)
  if all(x -> (isone(mod(x, n)) || x == p), lp)
    return _obstruction_pp_no_extend(F, cocycles, n)
  end
  K = F.field
  OK = maximal_order(K)
  T, mT = torsion_unit_group(OK)
  if is_divisible_by(order(T), n)
    return _obstruction_pp_no_extend(F, cocycles, n)
  end
  =#
  return _obstruction_pp(F, cocycles, n)
end


function _obstruction_pp(F::FieldsTower, cocycles::Vector{cocycle_ctx}, pv::Int)
  v, p = is_perfect_power_with_data(pv)
  Kc = _ext_cycl(F.generators_of_automorphisms, pv)
  K = F.field
  K1 = Kc.Ka
  D = F.isomorphism
  autsK = automorphism_list(K, copy = false)
  autsK1 = automorphism_list(K1, copy = false)
  restr = restriction(autsK1, autsK, Kc.mp[2])
  #I construct the group and the isomorphisms between the automorphisms and the gap group.
  permGC = _from_autos_to_perm(autsK)
  Gperm = _perm_to_gap_grp(permGC)
  Pcomp = 7
  R = Native.GF(Pcomp, cached = false)
  Rx, x = polynomial_ring(R, "x", cached = false)
  ff1 = Rx(K.pol)
  ff2 = Rx(K1.pol)
  while iszero(discriminant(ff1)) || iszero(discriminant(ff2))
    Pcomp = next_prime(Pcomp)
    R = Native.GF(Pcomp, cached = false)
    Rx, x = polynomial_ring(R, "x", cached = false)
    ff1 = Rx(K.pol)
    ff2 = Rx(K1.pol)
  end
  dautsK1 = Dict{fpPolyRingElem, Int}()
  for w = 1:length(autsK1)
    dautsK1[Rx(image_primitive_element(autsK1[w]))] = w
  end
  #Restrict to the p-Sylow
  #Unfortunately, I need to compute the group structure.
  Gp = pSylow(autsK1, p)
  D1 = Dict{fpPolyRingElem, GAP.GapObj}()
  for g in autsK1
    pol = Rx(image_primitive_element(g))
    mp = autsK[restr[dautsK1[pol]]]
    el = D[mp]
    D1[pol] = el
  end
  act_on_roots = action_on_roots(Gp, Kc.mp[1]\(gen(Kc.Kr)), pv)
  obstruction = falses(length(cocycles))
  Fext = FieldsTower(K1, autsK1, [id_hom(K1)])
  for i = 1:length(obstruction)
    #I create the cocycle
    if isdefined(cocycles[i], :inclusion_of_pSylow)
      Gp1 = Hecke.morphism_type(AbsSimpleNumField, AbsSimpleNumField)[]
      for g in autsK1
        el = D1[Rx(image_primitive_element(g))]
        if GAP.Globals.IN(el, GAP.Globals.Image(cocycles[i].inclusion_of_pSylow))
          push!(Gp1, g)
        end
      end
      Gp = Gp1
    end
    local cocycle
    let D1 = D1, cocycles = cocycles, pv = pv, i = i
      function cocycle(aut1::fpPolyRingElem, aut2::fpPolyRingElem)
        s1 = D1[aut1]
        s2 = D1[aut2]
        if isdefined(cocycles[i], :inclusion_of_pSylow)
          s1 = GAP.Globals.PreImagesRepresentative(cocycles[i].inclusion_of_pSylow, s1)
          s2 = GAP.Globals.PreImagesRepresentative(cocycles[i].inclusion_of_pSylow, s2)
        end
        rescoc = cocycles[i].values_cyclic(s1, s2)
        return mod(rescoc, pv)::Int
      end
    end
    #I have to find the subgroup of Gp such that the action of Gp on the roots of unity
    #coincides with the action on the kernel
    Stab = Hecke.morphism_type(AbsSimpleNumField, AbsSimpleNumField)[]
    inclusion = cocycles[i].inclusion
    projection = cocycles[i].projection
    inc_gen = GAP.Globals.Image(inclusion, cocycles[i].gen_kernel)
    for w = 1:length(Gp)
      if image_primitive_element(Gp[w]) == gen(K1)
        push!(Stab, Gp[w])
        continue
      end
      ss1 = D1[Rx(image_primitive_element(Gp[w]))]
      if isdefined(cocycles[i], :inclusion_of_pSylow)
        ss1 = GAP.Globals.PreImagesRepresentative(cocycles[i].inclusion_of_pSylow, ss1)
      end
      img_el = GAP.Globals.PreImagesRepresentative(projection, ss1)
      conj_elem = img_el*inc_gen*GAP.Globals.Inverse(img_el)
      ex = _find_exp(inc_gen, conj_elem)
      if ex == act_on_roots[w]
        push!(Stab, Gp[w])
      end
    end
    fl = issplit_cpa(Fext, Stab, cocycle, p, v, Rx)
    if !fl
      obstruction[i] = true
    end

  end
  return obstruction
end

function _obstruction_pp_no_extend(F::FieldsTower, cocycles::Vector{cocycle_ctx}, pv::Int)
  v, p = is_perfect_power_with_data(pv)
  K = F.field
  autsK = automorphism_list(K, copy = false)
  #I construct the group and the isomorphisms between the automorphisms and the gap group.
  permGC = _from_autos_to_perm(autsK)
  Gperm = _perm_to_gap_grp(permGC)
  Pcomp = 7
  R = Native.GF(Pcomp, cached = false)
  Rx, x = polynomial_ring(R, "x", cached = false)
  ff1 = Rx(K.pol)
  while iszero(discriminant(ff1))
    Pcomp = next_prime(Pcomp)
    R = Native.GF(Pcomp, cached = false)
    Rx, x = polynomial_ring(R, "x", cached = false)
    ff1 = Rx(K.pol)
  end
  dautsK = Dict{fpPolyRingElem, Int}()
  for w = 1:length(autsK)
    dautsK[Rx(image_primitive_element(autsK[w]))] = w
  end
  H = GAP.Globals.ImagesSource(cocycles[1].projection)
  iso = GAP.Globals.IsomorphismGroups(Gperm, H)
  ElemGAP = Vector{GAP.GapObj}(undef, length(permGC))
  for w = 1:length(permGC)
    ElemGAP[w] = GAP.Globals.Image(iso, _perm_to_gap_perm(permGC[w]))
  end
  #Restrict to the p-Sylow
  Gp = pSylow(autsK, p)
  obstruction = falses(length(cocycles))
  for i = 1:length(obstruction)
    #I create the cocycle
    local cocycle
    let ElemGAP = ElemGAP, dautsK = dautsK, cocycles = cocycles, pv = pv
      function cocycle(aut1::fpPolyRingElem, aut2::fpPolyRingElem)
        s1 = ElemGAP[dautsK[aut1]]
        s2 = ElemGAP[dautsK[aut2]]
        rescoc = cocycles[i].values_cyclic(s1, s2)
        return mod(rescoc, pv)::Int
      end
    end
    #I have to find the subgroup of Gp such that the action of Gp on the roots of unity
    #coincides with the action on the kernel
    Stab = Hecke.morphism_type(AbsSimpleNumField, AbsSimpleNumField)[]
    inclusion = cocycles[i].inclusion
    projection = cocycles[i].projection
    inc_gen = GAP.Globals.Image(inclusion, cocycles[i].gen_kernel)
    for w = 1:length(Gp)
      if image_primitive_element(Gp[w]) == gen(K)
        push!(Stab, Gp[w])
        continue
      end
      s1 = dautsK[Rx(image_primitive_element(Gp[w]))]
      img_el = GAP.Globals.PreImagesRepresentative(projection, ElemGAP[s1])
      el1 = img_el*inc_gen
      el2 = inc_gen*img_el
      if el1 == el2
        push!(Stab, Gp[w])
      end
    end
    if !issplit_cpa(F, Stab, cocycle, p, v, Rx)
      obstruction[i] = true
    end

  end

  return obstruction
end

################################################################################
#
#  IsSplit function for a crossed product algebra
#
################################################################################

function issplit_cpa(F::FieldsTower, G::Vector{<: NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, Coc::Function, p::Int, v::Int, Rx::fpPolyRing)
  K = F.field
  @vtime :BrauerObst 1 if p == 2 && is_totally_complex(K) && !is_split_at_infinity(K, G, Coc, Rx)
    return false
  end
  # Now, the finite primes.
  # The crossed product algebra is ramified at the ramified primes of the field (and at the primes dividing the values
  # of the cocycle, but our cocycle has values in the roots of unity...
  # I only need to check the tame ramification.
  # The exact sequence on Brauer groups and completion tells me that I have one degree of freedom! :)
  O = maximal_order(K)
  lp = ramified_primes(F)
  if p in lp || !(F.is_abelian || (length(G) == degree(K)))
    for q in lp
      if q != p
        @vtime :BrauerObst 1 fl = issplit_at_p(F, G, Coc, Int(q), p^v, Rx)
        if !fl
          return false
        end
      end
    end
  else
    for i = 1:length(lp)-1
      q = lp[i]
      @vtime :BrauerObst 1 fl = issplit_at_p(F, G, Coc, Int(q), p^v, Rx)
      if !fl
        return false
      end
    end
  end
  return true
end

function is_split_at_infinity(K::AbsSimpleNumField, G::Vector{<: NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, Coc::Function, Rx::fpPolyRing)
  fl, aut = _find_complex_conjugation(K, G)
  if !fl
    return true
  end
  @assert aut in G
  return !isone(Coc(Rx(image_primitive_element(aut)), Rx(image_primitive_element(aut))))
end

function issplit_at_p(F::FieldsTower, G::Vector{<: NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, Coc::Function, p::Int, n::Int, Rx::fpPolyRing)
  K = domain(G[1])
  O = maximal_order(K)
  lp = prime_decomposition(O, p, cached = true)
  if degree(O) == length(G)
    if !is_coprime(length(G), p)
      q = is_perfect_power_with_data(n)[2]
      Gq = pSylow(G, q)
      return issplit_at_P(O, Gq, Coc, lp[1][1], n, Rx)
    else
      return issplit_at_P(O, G, Coc, lp[1][1], n, Rx)
    end
  else
    for i = 1:length(lp)
      if !issplit_at_P(O, G, Coc, lp[i][1], n, Rx)
         return false
      end
    end
    return true
  end
end


function _find_theta(G::Vector{<: NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, F::fqPolyRepField, mF::Hecke.NfOrdToFqNmodMor, e::Int)
  #G is the decomposition group of a prime ideal P
  # F is the quotient, mF the map
  K = domain(G[1])
  O = maximal_order(K)
  p = is_perfect_power_with_data(e)[2]
  t = div(e, p)
  gF = gen(F)
  igF = K(mF\gF)
  q = 2
  R = residue_ring(FlintZZ, q, cached = false)[1]
  Rt = polynomial_ring(R, "t", cached = false)[1]
  fmod = Rt(K.pol)
  while iszero(discriminant(fmod))
    q = next_prime(q)
    R = residue_ring(FlintZZ, q, cached = false)[1]
    Rt = polynomial_ring(R, "t", cached = false)[1]
    fmod = Rt(K.pol)
  end
  theta = G[1]
  for i = 1:length(G)
    theta = G[i]
    res = O(theta(igF), false)
    #img = compose_mod(theta_q, igFq, fmod)
    #res = O(lift(K, img), false)
    #I make sure that the element is a generator of the inertia subgroup
    if mF(res) == gF
      theta_q = Rt(image_primitive_element(theta))
      pp = theta_q
      for i = 2:t
        pp = compose_mod(theta_q, pp, fmod)
      end
      if pp != gen(Rt)
        break
      end
    end
  end
  return theta
end


function _find_frob(G::Vector{<: NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, F::fqPolyRepField, mF::Hecke.NfOrdToFqNmodMor, e::Int, f::Int, q::Int, theta::NumFieldHom{AbsSimpleNumField, AbsSimpleNumField})
  K = domain(G[1])
  O = maximal_order(K)
  q1 = 2
  R = residue_ring(FlintZZ, q1, cached = false)[1]
  Rt = polynomial_ring(R, "t", cached = false)[1]
  fmod = Rt(K.pol)
  while iszero(discriminant(fmod))
    q1 = next_prime(q1)
    R = residue_ring(FlintZZ, q1, cached = false)[1]
    Rt = polynomial_ring(R, "t", cached = false)[1]
    fmod = Rt(K.pol)
  end
  gK = gen(K)
  p = is_perfect_power_with_data(e)[2]
  t = div(e, p)
  expo = mod(q, e)
  gF = gen(F)
  igF = K(mF\gF)
  rhs = gF^q
  theta_q = Rt(image_primitive_element(theta))
  for i = 1:length(G)
    frob = G[i]
    if frob == theta
      continue
    end
    if mF(O(frob(igF), false)) != rhs
      continue
    end
    frob_q = Rt(image_primitive_element(frob))
    #Now, I check the relation
    #gc = frob * theta
    gc = compose_mod(frob_q, theta_q, fmod)
    #gq = (theta^expo) * frob
    #TODO: Binary powering
    gq = theta_q
    for i = 2:expo
      gq = compose_mod(gq, theta_q, fmod)
    end
    gq = compose_mod(gq, frob_q, fmod)
    fl = gc == gq
    @hassert :Fields 1 fl == ((theta^expo) * frob == frob * theta)
    if fl
      return frob
    end
  end
  error("something went wrong!")
end

function _pow_as_comp(f::fpPolyRingElem, b::Int, fmod::fpPolyRingElem)
  Rx = base_ring(f)
  if b == 0
    error("what is that?!")
  elseif b == 1
    return f
  else
    bit = ~((~UInt(0)) >> 1)
    while (UInt(bit) & b) == 0
      bit >>= 1
    end
    z = f
    bit >>= 1
    while bit != 0
      z = Hecke.compose_mod(z, z, fmod)
      if (UInt(bit) & b) != 0
        z = Hecke.compose_mod(f, z, fmod)
      end
      bit >>= 1
    end
    return z
  end
end



function issplit_at_P(O::AbsSimpleNumFieldOrder, G::Vector{<: NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, Coc::Function, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, n::Int, Rx::fpPolyRing)
  e = gcd(length(G), ramification_index(P))
  if e == 1
    return true
  end
  f = gcd(length(G), degree(P))
  if is_divisible_by(norm(P)-1, e)
    c = divexact(norm(P)-1, e)
    if f == 1 && iszero(mod(c, n))
      return true
    end
  end
  @vtime :BrauerObst 1  Gp = decomposition_group(P, G = G, orderG = e*f)
  InGrp = inertia_subgroup(P, G = Gp)
  e = length(InGrp)
  if e == 1
    return true
  end
  fl, f = divides(length(Gp), e)
  @assert fl
  c = divexact(norm(P)-1, e)
  if f == 1 && iszero(mod(c, n))
    return true
  end
  p = Int(minimum(P))
  @assert mod(degree(P), f) == 0
  f1 = divexact(degree(P), f)
  q = p^f1 #Cardinality of the residue field

  F, mF = Hecke.ResidueFieldSmall(O, P)
  theta1 = _find_theta(InGrp, F, mF, e)

  theta = Rx(image_primitive_element(theta1))
  fmod = Rx(Hecke.nf(O).pol)
  #I have found my generators. Now, we find the elements to test if it splits.
  if !iszero(mod(c, n))
    powtheta = theta
    zeta = 0
    for k = 1:e-1
      zeta += Coc(powtheta, theta)
      powtheta = compose_mod(powtheta, theta, fmod)
    end
    zeta = mod(zeta * c, n)
    if !iszero(zeta)
      return false
    end
  end

  if f == 1
    return true
  end
  frob1 = _find_frob(Gp, F, mF, e, f, q, theta1)
  frob = Rx(image_primitive_element(frob1))

  if iszero(mod(q-1, e*n))
    lambda = mod(Coc(frob, theta)- Coc(theta, frob), n)
    return iszero(lambda)
  end
  lambda = Coc(frob, theta)
  powtheta = theta
  s, t = divrem(q-1, e)
  if !iszero(mod(s+1, n))
    for k = 1:t
      lambda -= (s+1) * Coc(powtheta, theta)
      powtheta = compose_mod(powtheta, theta, fmod)
    end
  else
    powtheta = _pow_as_comp(theta, t+1, fmod)
  end
  if !iszero(mod(s, n))
    for k = t+1:(e-1)
      lambda -= s * Coc(powtheta, theta)
      powtheta = compose_mod(powtheta, theta, fmod)
    end
  end
  powtheta = _pow_as_comp(theta, mod(q, e), fmod)
  lambda = mod(lambda - Coc(powtheta, frob), n)
  return iszero(lambda)

end
