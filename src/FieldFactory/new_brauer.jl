################################################################################
#
#  Obstruction Interface
# 
################################################################################

function check_obstruction(list::Vector{FieldsTower}, L::Main.ForeignGAP.MPtr,
           i::Int, invariants::Vector{Int})
           
  d = degree(list[1])
  common_degree = ppio(invariants[end], d)[1]
  cocycles = cocycles_computation(L, i)
  G = GAP.Globals.ImagesSource(cocycles[1].projection)
  for F in list
    assure_isomorphism(F, G)
  end
  if isone(common_degree)
    for i = 1:length(list)
      list[i].admissible_cocycles = cocycles
    end
    return list
  end
  obstructions = Vector{Vector{Bool}}(undef, length(list))
  for i = 1:length(obstructions)
    obstructions[i] = falses(length(cocycles))
  end
  fac = factor(common_degree)
  for (p, v) in fac
    cocycles_p = [_to_prime_power_kernel(x, Int(p)) for x in cocycles] 
    if length(fac) > 1
      if iszero(cocycles_p[1])
        continue
      end
    end
    if length(invariants) == 1 || iscoprime(invariants[end-1], p)
      for i = 1:length(list)
        @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())Fields to test: $(length(list)-i+1)"
        if !all(obstructions[i])
          obstructions[i] = check_obstruction(list[i], cocycles_p, Int(p), obstructions[i]) 
        end
      end
      @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())"
    else
      all_cocycles = Vector{Vector{cocycle_ctx}}(undef, length(cocycles))
      for i = 1:length(cocycles)
        all_cocycles[i] = _cocycles_with_cyclic_kernel(cocycles[i], Int(p))
      end
      for i = 1:length(list)
        @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())Fields to test: $(length(list)-i+1)"
        if !all(obstructions[i])
          obstructions[i] = check_obstruction_non_cyclic(list[i], all_cocycles, Int(p), obstructions[i]) 
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
    push!(new_list, list[i])
  end
  return new_list
end


function check_obstruction(F::FieldsTower, cocycles::Vector{cocycle_ctx}, 
                            p::Int, obstruction_at::Vector{Bool})
  #I assume that the kernel of the embedding problem is a p-group
  @assert isprime(p)  
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
#  IsZero for a cocycle
#
################################################################################

function iszero(c::cocycle_ctx)
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
  imgs_proj = GAP.julia_to_gap(imgs_new_proj)
  Gp = GAP.Globals.Subgroup(G, imgs_proj)
  #I need the inclusion of Gp into G for strange (GAP) reasons.
  gensGp = GAP.Globals.GeneratorsOfGroup(Gp)
  inclusion_Gp = GAP.Globals.GroupHomomorphismByImages(Gp, G, gensGp, gensGp)
  #now the maps.
  new_proj = GAP.Globals.GroupHomomorphismByImages(Ep, Gp, gensEp, imgs_proj)
  images_inclusion = []
  gensA = GAP.Globals.GeneratorsOfGroup(A)
  for i = 1:length(gensA)
    push!(images_inclusion, GAP.Globals.PreImagesRepresentative(inj_Ep, GAP.Globals.Image(inc, gensA[i])))
  end
  imgs_inclusion = GAP.julia_to_gap(images_inclusion)
  new_incl = GAP.Globals.GroupHomomorphismByImages(A, Ep, gensA, imgs_inclusion)
  res =  cocycle_ctx(new_proj, new_incl, cocycle.cocycle)
  res.inclusion_of_pSylow = inclusion_Gp
  return res
end


#Careful, I am discarding the cocycles that represent split extensions
function  _cocycles_with_cyclic_kernel(old_cocycle::cocycle_ctx, p::Int)
  cocycle = _to_prime_power_groups(old_cocycle, p)
  proj = cocycle.projection
  E = GAP.Globals.Source(proj)
  normal_subgroups = GAP.Globals.NormalSubgroups(E)
  G = GAP.Globals.ImagesSource(proj)
  K = GAP.Globals.Source(cocycle.inclusion)
  oK = GAP.Globals.Size(K)
  normal_cyclic_and_contained = Main.ForeignGAP.MPtr[]
  for i = 1:length(normal_subgroups)
    g = normal_subgroups[i]
    oG = GAP.Globals.Size(g)
    if !GAP.Globals.IsSubgroup(K, g) || oG == oK
      continue
    end
    fg = GAP.Globals.FactorGroup(K, g)
    order = fmpz(GAP.gap_to_julia(Int, GAP.Globals.Size(fg)))
    np = remove(order, p)[2]
    if isone(np) && GAP.Globals.IsCyclic(fg)
      push!(normal_cyclic_and_contained, g)
    end  
  end
  #Almost done. I only want the minimal ones, so I need to sieve.
  res = Main.ForeignGAP.MPtr[]
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
  pr1 = GAP.Globals.NaturalHomomorphismByNormalSubgroup(E, S)
  E_new = GAP.Globals.ImagesSource(pr1)
  A_new = GAP.Globals.ImagesSource(pr)
  gensA_new = GAP.Globals.GeneratorsOfGroup(A_new)
  images_inclusion = []
  for i = 1:length(gensA_new)
    el_A = GAP.Globals.PreImagesRepresentative(pr, gensA_new[i])
    el_E = GAP.Globals.Image(cocycle.inclusion, el_A)
    push!(images_inclusion, GAP.Globals.Image(pr1, el_E)) 
  end
  inclusion = GAP.Globals.GroupHomomorphismByImages(A_new, E_new, gensA_new, GAP.julia_to_gap(images_inclusion))
  gensE_new = GAP.Globals.GeneratorsOfGroup(E_new)
  images_proj = []
  for i = 1:length(gensE_new)
    el = GAP.Globals.PreImagesRepresentative(pr1, gensE_new[i])
    push!(images_proj, GAP.Globals.Image(cocycle.projection, el))
  end
  projection = GAP.Globals.GroupHomomorphismByImages(E_new, G, gensE_new, GAP.julia_to_gap(images_proj))
  local new_coc
  let cocycle = cocycle, pr = pr 
    function new_coc(x::Main.ForeignGAP.MPtr, y::Main.ForeignGAP.MPtr)
      return GAP.Globals.Image(pr, cocycle.cocycle(x, y))
    end
  end
  return cocycle_ctx(projection, inclusion, new_coc)
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
  S = GAP.Globals.Subgroup(A, GAP.julia_to_gap(gens_sub))
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
  inclusion = GAP.Globals.GroupHomomorphismByImages(A_new, E_new, gensA_new, GAP.julia_to_gap(images_inclusion))
  gensE_new = GAP.Globals.GeneratorsOfGroup(E_new)
  images_proj = []
  for i = 1:length(gensE_new)
    el = GAP.Globals.PreImagesRepresentative(pr1, gensE_new[i])
    push!(images_proj, GAP.Globals.Image(cocycle.projection, el))
  end
  projection = GAP.Globals.GroupHomomorphismByImages(E_new, G, gensE_new, GAP.julia_to_gap(images_proj))
  local new_coc
  let cocycle = cocycle, pr = pr 
    function new_coc(x::Main.ForeignGAP.MPtr, y::Main.ForeignGAP.MPtr)
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
  if isdefined(F, :isomorphism)
    return nothing
  end
  assure_automorphisms(F)
  K = F.field
  autsK = automorphisms(K, copy = false)
  permGC = _from_autos_to_perm(autsK)
  Gperm = _perm_to_gap_grp(permGC)
  iso = GAP.Globals.IsomorphismGroups(Gperm, G)
  D = Dict{NfToNfMor, Main.ForeignGAP.MPtr}()
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

function cocycles_computation(L::Main.ForeignGAP.MPtr, level::Int)

  proj = GAP.Globals.NaturalHomomorphismByNormalSubgroup(L[1], L[level+1])
  target_grp = GAP.Globals.ImagesSource(proj)
  mH1 = GAP.Globals.NaturalHomomorphismByNormalSubgroup(target_grp, GAP.Globals.Image(proj, L[level]))
  H1 = GAP.Globals.ImagesSource(mH1)
  K = GAP.Globals.Kernel(mH1)
    
  Elems = GAP.Globals.Elements(H1)
  MatCoc = Array{Main.ForeignGAP.MPtr, 2}(undef, length(Elems), length(Elems))
  Preimags = Vector{Main.ForeignGAP.MPtr}(undef, length(Elems))
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
  
  autos = _autos_to_check(H1, K, target_grp, mH1)
  cocycles = Vector{cocycle_ctx}(undef, length(autos))
  for i = 1:length(autos)
    aut1, aut2 = autos[i]
    local cocycle
    let Elems = Elems, MatCoc = MatCoc, aut1 = aut1, aut2 = aut2, Elems = Elems
      function cocycle(x::Main.ForeignGAP.MPtr, y::Main.ForeignGAP.MPtr)  
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
    new_aut2 = GAP.Globals.GroupHomomorphismByImages(K, target_grp, GAP.Globals.GeneratorsOfGroup(K), GAP.Globals.GeneratorsOfGroup(K))
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
    function cocycle_val(x::Main.ForeignGAP.MPtr, y::Main.ForeignGAP.MPtr)
      return _find_exp(gen, cocycle.cocycle(x, y))
    end
  end
  cocycle.values_cyclic = cocycle_val
  cocycle.gen_kernel = gen
  return nothing
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
  if divisible(order(T), fmpz(p))
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
  GC = automorphisms(K, copy = false)
  D = x.isomorphism
  Pcomp = 2
  R = GF(Pcomp, cached = false)
  Rx = PolynomialRing(R, "x", cached = false)[1]
  ff = Rx(K.pol)
  while iszero(mod(p, Pcomp)) || iszero(discriminant(ff))
    Pcomp = next_prime(Pcomp)
    R = GF(Pcomp, cached = false)
    Rx = PolynomialRing(R, "x", cached = false)[1]
    ff = Rx(K.pol)
  end
  permGC = _from_autos_to_perm(GC)
  Gperm = _perm_to_gap_grp(permGC)
  PermGAP = Vector{Main.ForeignGAP.MPtr}(undef, length(permGC))
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
  D1 = Dict{gfp_poly, Main.ForeignGAP.MPtr}()
  for g in Gp
    pol = Rx(g.prim_img)
    el = D[g]
    D1[pol] = el
  end 
  obstruction = falses(length(cocycles)) 
  for i = 1:length(obstruction)
    #I create the cocycle
    local cocycle
    let D1 = D1, i = i, p = p
      function cocycle(aut1::gfp_poly, aut2::gfp_poly)
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
  autsK = automorphisms(K, copy = false)
  autsK1 = automorphisms(K1, copy = false)
  restr = restriction(autsK1, autsK, Kc.mp[2])
  #I construct the group and the isomorphisms between the automorphisms and the gap group.
  permGC = _from_autos_to_perm(autsK) 
  Gperm = _perm_to_gap_grp(permGC)
  Pcomp = 2
  R = GF(Pcomp, cached = false)
  Rx = PolynomialRing(R, "x", cached = false)[1]
  ff1 = Rx(K.pol)
  ff2 = Rx(K1.pol)
  while iszero(mod(p, Pcomp)) || iszero(discriminant(ff1)) || iszero(discriminant(ff2))
    Pcomp = next_prime(Pcomp)
    R = GF(Pcomp, cached = false)
    Rx = PolynomialRing(R, "x", cached = false)[1]
    ff1 = Rx(K.pol)
    ff2 = Rx(K1.pol)
  end
  fmod = Rx(K.pol)
  dautsK1 = Dict{gfp_poly, Int}()
  for w = 1:length(autsK1)
    dautsK1[Rx(autsK1[w].prim_img)] = w
  end 
  #Restrict to the p-Sylow
  #Unfortunately, I need to compute the group structure.
  Gp = pSylow(autsK1, p)
  D1 = Dict{gfp_poly, Main.ForeignGAP.MPtr}()
  for g in Gp
    pol = Rx(g.prim_img)
    mp = autsK[restr[dautsK1[aut1]]]
    el = D[g]
    D1[pol] = el
  end
  obstruction = falses(length(cocycle))
  for i = 1:length(obstruction)
    #I create the cocycle
    local cocycle
    let restr = restr, dautsK1 = dautsK1, ElemGAP = ElemGAP, p = p
      function cocycle(aut1::gfp_poly, aut2::gfp_poly)
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
    
    if !cpa_issplit(x, Gp, cocycle, p, 1, Rx)
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
  
  v, p = ispower(n)
  if all(x -> (isone(mod(x, n)) || x == p), lp)
    return _obstruction_pp_no_extend(F, cocycles, n)
  end
  K = F.field
  OK = maximal_order(K)
  T, mT = torsion_unit_group(OK)
  if divisible(order(T), n)
    return _obstruction_pp_no_extend(F, cocycles, n)
  end
  =#
  return _obstruction_pp(F, cocycles, n)
end


function _obstruction_pp(F::FieldsTower, cocycles::Vector{cocycle_ctx}, pv::Int)
  v, p = ispower(pv)
  Kc = _ext_cycl(F.generators_of_automorphisms, pv)
  K = F.field
  K1 = Kc.Ka
  D = F.isomorphism
  autsK = automorphisms(K, copy = false)
  autsK1 = automorphisms(K1, copy = false)
  restr = restriction(autsK1, autsK, Kc.mp[2])
  #I construct the group and the isomorphisms between the automorphisms and the gap group.
  permGC = _from_autos_to_perm(autsK) 
  Gperm = _perm_to_gap_grp(permGC)
  Pcomp = 7
  R = GF(Pcomp, cached = false)
  Rx, x = PolynomialRing(R, "x", cached = false)
  ff1 = Rx(K.pol)
  ff2 = Rx(K1.pol)
  while iszero(discriminant(ff1)) || iszero(discriminant(ff2))
    Pcomp = next_prime(Pcomp)
    R = GF(Pcomp, cached = false)
    Rx, x = PolynomialRing(R, "x", cached = false)
    ff1 = Rx(K.pol)
    ff2 = Rx(K1.pol)
  end
  dautsK1 = Dict{gfp_poly, Int}()
  for w = 1:length(autsK1)
    dautsK1[Rx(autsK1[w].prim_img)] = w
  end 
  #Restrict to the p-Sylow
  #Unfortunately, I need to compute the group structure.
  Gp = pSylow(autsK1, p)
  D1 = Dict{gfp_poly, Main.ForeignGAP.MPtr}()
  for g in Gp
    pol = Rx(g.prim_img)
    mp = autsK[restr[dautsK1[pol]]]
    el = D[mp]
    D1[pol] = el
  end
  act_on_roots = action_on_roots(Gp, Kc.mp[1]\(gen(Kc.Kr)), pv)
  obstruction = falses(length(cocycles))
  Fext = FieldsTower(K1, autsK1, [id_hom(K1)])
  for i = 1:length(obstruction)
    #I create the cocycle
    local cocycle
    let D1 = D1, cocycles = cocycles, pv = pv, i = i
      function cocycle(aut1::gfp_poly, aut2::gfp_poly)
        s1 = D1[aut1]
        s2 = D1[aut2]
        if isdefined(cocycles[i], :inclusion_of_pSylow)
          s1 = GAP.Globals.PreImagesRepresentative(cocycles[i].inclusion_of_pSylow, el1)
          s2 = GAP.Globals.PreImagesRepresentative(cocycles[i].inclusion_of_pSylow, el2)
        end
        rescoc = cocycles[i].values_cyclic(s1, s2)
        return mod(rescoc, pv)::Int
      end
    end
    #I have to find the subgroup of Gp such that the action of Gp on the roots of unity 
    #coincides with the action on the kernel
    Stab = NfToNfMor[]
    inclusion = cocycles[i].inclusion
    projection = cocycles[i].projection
    inc_gen = GAP.Globals.Image(inclusion, cocycles[i].gen_kernel)
    for w = 1:length(Gp)
      if Gp[w].prim_img == gen(K1)
        push!(Stab, Gp[w])
        continue
      end
      s1 = D1[Rx(Gp[w].prim_img)]
      img_el = GAP.Globals.PreImagesRepresentative(projection, s1)
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
  v, p = ispower(pv)
  K = F.field
  autsK = automorphisms(K, copy = false)
  #I construct the group and the isomorphisms between the automorphisms and the gap group.
  permGC = _from_autos_to_perm(autsK) 
  Gperm = _perm_to_gap_grp(permGC)
  Pcomp = 7
  R = GF(Pcomp, cached = false)
  Rx, x = PolynomialRing(R, "x", cached = false)
  ff1 = Rx(K.pol)
  while iszero(discriminant(ff1))
    Pcomp = next_prime(Pcomp)
    R = GF(Pcomp, cached = false)
    Rx, x = PolynomialRing(R, "x", cached = false)
    ff1 = Rx(K.pol)
  end
  dautsK = Dict{gfp_poly, Int}()
  for w = 1:length(autsK)
    dautsK[Rx(autsK[w].prim_img)] = w
  end 
  H = GAP.Globals.ImagesSource(cocycles[1].projection)
  iso = GAP.Globals.IsomorphismGroups(Gperm, H)
  ElemGAP = Vector{Main.ForeignGAP.MPtr}(undef, length(permGC))
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
      function cocycle(aut1::gfp_poly, aut2::gfp_poly)
        s1 = ElemGAP[dautsK[aut1]]
        s2 = ElemGAP[dautsK[aut2]]
        rescoc = cocycles[i].values_cyclic(s1, s2)
        return mod(rescoc, pv)::Int
      end
    end
    #I have to find the subgroup of Gp such that the action of Gp on the roots of unity 
    #coincides with the action on the kernel
    Stab = NfToNfMor[]
    inclusion = cocycles[i].inclusion
    projection = cocycles[i].projection
    inc_gen = GAP.Globals.Image(inclusion, cocycles[i].gen_kernel)
    for w = 1:length(Gp)
      if Gp[w].prim_img == gen(K)
        push!(Stab, Gp[w])
        continue
      end
      s1 = dautsK[Rx(Gp[w].prim_img)]
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

function issplit_cpa(F::FieldsTower, G::Vector{NfToNfMor}, Coc::Function, p::Int, v::Int, Rx::GFPPolyRing)
  K = F.field
  @vtime :BrauerObst 1 if p == 2 && istotally_complex(K) && !is_split_at_infinity(K, G, Coc, Rx)
    return false    
  end
  # Now, the finite primes.
  # The crossed product algebra is ramified at the ramified primes of the field (and at the primes dividing the values
  # of the cocycle, but our cocycle has values in the roots of unity...
  # I only need to check the tame ramification.
  # The exact sequence on Brauer groups and completion tells me that I have one degree of freedom! :)
  O = maximal_order(K)
  lp = ramified_primes(F)
  if p in lp || !(F.isabelian || (length(G) == degree(K)))
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

function is_split_at_infinity(K::AnticNumberField, G::Vector{NfToNfMor}, Coc::Function, Rx::GFPPolyRing)
  fl, aut = _find_complex_conjugation(K, G)
  if !fl
    return true
  end
  return !isone(Coc(Rx(aut.prim_img), Rx(aut.prim_img)))
end

function issplit_at_p(F::FieldsTower, G::Vector{NfToNfMor}, Coc::Function, p::Int, n::Int, Rx::GFPPolyRing)
  K = F.field
  O = maximal_order(K)
  lp = prime_decomposition(O, p, cached = true)
  if degree(O) == length(G) || F.isabelian
    return issplit_at_P(O, G, Coc, lp[1][1], n, Rx)
  else
    for i = 1:length(lp)
      if !issplit_at_P(O, G, Coc, lp[i][1], n, Rx)
         return false
      end
    end
    return true
  end
end


function issplit_at_P(O::NfOrd, G::Vector{NfToNfMor}, Coc::Function, P::NfOrdIdl, n::Int, Rx::GFPPolyRing)
 
  e = gcd(length(G), ramification_index(P))
  if e == 1
    return true
  end
  @assert divisible(norm(P)-1, e)
  c = divexact(norm(P)-1, e)
  f = gcd(length(G), degree(P))
  if f == 1 && iszero(mod(c, n))
    return true
  end 
  @vtime :BrauerObst 1  Gp = decomposition_group(P, G = G, orderG = e*f)
  InGrp = inertia_subgroup(P, G = Gp)
  e = length(InGrp)
  if e == 1
    return true
  end
  f = divexact(length(Gp), e)
  c = divexact(norm(P)-1, e)
  if f == 1 && iszero(mod(c, n))
    return true
  end 
  p = Int(minimum(P))
  f1 = divexact(degree(P), f)
  q = p^f1 #Cardinality of the residue field

  F, mF = Hecke.ResidueFieldSmall(O, P)
  theta1 = _find_theta(InGrp, F, mF, e)

  theta = Rx(theta1.prim_img)
  fmod = Rx(nf(O).pol)
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
  frob = Rx(frob1.prim_img)

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
