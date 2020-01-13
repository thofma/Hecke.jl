################################################################################
#
#  Cocycle type
#
################################################################################

mutable struct cocycle_ctx
  projection::Main.ForeignGAP.MPtr
  inclusion::Main.ForeignGAP.MPtr
  cocycle::Function
  values_cyclic::Function
  gen_kernel::Main.ForeignGAP.MPtr
  
  function cocycle_ctx(proj::Main.ForeignGAP.MPtr, incl::Main.ForeignGAP.MPtr, cocycle::Function)
    z = new()
    z.projection = proj
    z.inclusion = incl
    z.cocycle = cocycle
    return z
  end
end

################################################################################
#
#  Obstruction Interface
# 
################################################################################

function check_obstruction(list::Vector{FieldsTower}, L::Main.ForeignGAP.MPtr,
           i::Int, invariants::Vector{Int})
           
  d = degree(list[1])
  common_degree = ppio(invariants[end], d)[1]
  if isone(common_degree)
    return list
  end
  cocycles = cocycles_computation(L, i)
  obstructions = Vector{Vector{Bool}}(undef, length(list))
  for i = 1:length(obstructions)
    obstructions[i] = falses(length(cocycles))
  end
  fac = factor(common_degree)
  for (p, v) in fac
    cocycles_p = [_to_prime_power_case(x, Int(p)) for x in cocycles] 
    if length(invariants) == 1 || iscoprime(invariants[end-1], p)
      for i = 1:length(list)
        if !all(obstructions[i])
          obstructions[i] = check_obstruction(list[i], cocycles_p, Int(p), obstructions[i]) 
        end
      end
    end
  end
  #Now, extract the list
  indices = [i for i = 1:length(obstructions) if !all(obstructions[i])]
  return list[indices]
end



function check_obstruction(F::FieldsTower, cocycles::Vector{cocycle_ctx}, 
                            p::Int, obstruction_at::Vector{Bool})
  #I assume that the kernel of the embedding problem is a p-group
  @assert isprime(p)  
  indices = [i for i = 1:length(obstruction_at) if !obstruction_at[i]]
  cocycles_to_test = cocycles[indices]
  if GAP.Globals.IsCyclic(GAP.Globals.Source(cocycles[1].inclusion))
    #Nice case
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
  else
    #I restrict to the p-Sylow of G and check the corresponding obstruction.
    error("Not yet implemented")
  end
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
    cocycles[i] = cocycle_ctx(mH1*aut1, aut2, cocycle)
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

function _to_prime_power_case(cocycle::cocycle_ctx, p::Int)
  A = GAP.Globals.Source(cocycle.inclusion)
  n = GAP.Globals.Size(A)
  np, nq = ppio(n, p)
  if isone(nq)
    return cocycle
  end
  gens = GAP.gap_to_julia(GAP.Globals.MinimalGeneratingSet(A))
  gens_sub = []
  for i = 1:length(gens)
    push!(gens_sub, gens[i]^nq)
  end
  E = GAP.Globals.ImagesSource(cocycle.inclusion)
  G = GAP.Globals.ImagesSource(cocycle.projection)
  sizeG = GAP.Globals.Size(G)
  S = GAP.Globals.Subgroup(A, GAP.julia_to_gap(gens_sub))
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
  DGCvect = Vector{Tuple{gfp_poly, Int}}(undef, length(GC))
  for i = 1:length(GC)
    DGCvect[i] = (Rx(GC[i].prim_img), i)
  end
  DGC = Dict{gfp_poly, Int}(DGCvect)
  permGC = _from_autos_to_perm(GC)
  Gperm = _perm_to_gap_grp(permGC)
  PermGAP = Vector{Main.ForeignGAP.MPtr}(undef, length(permGC))
  for w = 1:length(permGC)
    PermGAP[w] = _perm_to_gap_perm(permGC[w])
  end
  #Restrict to the p-Sylow
  if p != 2
    Gp = pSylow(Gperm, PermGAP, GC, p)
  else
    Gp = GC
  end
  H = GAP.Globals.ImagesSource(cocycles[1].projection)
  iso = GAP.Globals.IsomorphismGroups(Gperm, H)
  ElemGAP = Vector{Main.ForeignGAP.MPtr}(undef, length(permGC))
  for w = 1:length(permGC)
    ElemGAP[w] = GAP.Globals.Image(iso, PermGAP[w])
  end
  obstruction = falses(length(cocycles)) 
  for i = 1:length(obstruction)
    #I create the cocycle
    local cocycle
    let DGC = DGC, ElemGAP = ElemGAP, i = i, p = p
      function cocycle(aut1::gfp_poly, aut2::gfp_poly)
        s1 = ElemGAP[DGC[aut1]]
        s2 = ElemGAP[DGC[aut2]]
        res = cocycles[i].values_cyclic(s1, s2)
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
  assure_automorphisms(x)
  K = x.field
  lp = ramified_primes(x)
  Kc = _ext_cycl(x.generators_of_automorphisms, p)
  K1 = Kc.Ka
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
  H = GAP.Globals.ImagesSource(cocycles[1].projection)
  iso = GAP.Globals.IsomorphismGroups(Gperm, H)
  ElemGAP = Vector{Main.ForeignGAP.MPtr}(undef, length(permGC))
  for w = 1:length(permGC)
    ElemGAP[w] = GAP.Globals.Image(iso, _perm_to_gap_perm(permGC[w]))
  end
  #Restrict to the p-Sylow
  #Unfortunately, I need to compute the group structure.
  Gp = pSylow(autsK1, p)
  obstruction = falses(length(cocycle))
  for i = 1:length(obstruction)
    #I create the cocycle
    local cocycle
    let restr = restr, dautsK1 = dautsK1, ElemGAP = ElemGAP, p = p
      function cocycle(aut1::gfp_poly, aut2::gfp_poly)
        s1 = ElemGAP[restr[dautsK1[aut1]]]
        s2 = ElemGAP[restr[dautsK1[aut2]]]
        rescoc = cocycles[i].values_cyclic(a1, b1)
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
  return _obstruction_pp(F, cocycles, n)
end


function _obstruction_pp(F::FieldsTower, cocycles::Vector{cocycle_ctx}, pv::Int)
  v, p = ispower(pv)
  Kc = _ext_cycl(F.generators_of_automorphisms, pv)
  K = F.field
  K1 = Kc.Ka
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
  H = GAP.Globals.ImagesSource(cocycles[1].projection)
  iso = GAP.Globals.IsomorphismGroups(Gperm, H)
  ElemGAP = Vector{Main.ForeignGAP.MPtr}(undef, length(permGC))
  for w = 1:length(permGC)
    ElemGAP[w] = GAP.Globals.Image(iso, _perm_to_gap_perm(permGC[w]))
  end
  #Restrict to the p-Sylow
  #Unfortunately, I need to compute the group structure.
  Gp = pSylow(autsK1, p)
  act_on_roots = action_on_roots(Gp, Kc.mp[1]\(gen(Kc.Kr)), pv)
  obstruction = falses(length(cocycles))
  for i = 1:length(obstruction)
    #I create the cocycle
    local cocycle
    let restr = restr, ElemGAP = ElemGAP, dautsK1 = dautsK1, cocycles = cocycles, pv = pv
      function cocycle(aut1::gfp_poly, aut2::gfp_poly)
        s1 = ElemGAP[restr[dautsK1[aut1]]]
        s2 = ElemGAP[restr[dautsK1[aut2]]]
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
      s1 = restr[dautsK1[Rx(Gp[w].prim_img)]]
      img_el = GAP.Globals.PreImagesRepresentative(projection, ElemGAP[s1])
      conj_elem = img_el*inc_gen*GAP.Globals.Inverse(img_el)
      ex = _find_exp(inc_gen, conj_elem)
      if ex == act_on_roots[w]
        push!(Stab, Gp[w])
      end
    end
    if !issplit_cpa(F, Stab, cocycle, p, v, Rx)
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
  @vtime :BrauerObst 1 if p == 2 && istotally_complex(K) && !is_split_at_infinity(K, Coc, Rx)
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
