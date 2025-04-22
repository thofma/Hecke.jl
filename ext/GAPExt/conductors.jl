################################################################################
#
#  Contained in the alternating group
#
################################################################################

function is_discriminant_square(IdG::GAP.GapObj)
  G = GAP.Globals.SmallGroup(IdG)
  mp = GAP.Globals.RegularActionHomomorphism(G)
  S = GAP.Globals.ImagesSource(mp)
  lg = GAP.Globals.GeneratorsOfGroup(S)
  for i = 1:length(lg)
    s = GAP.Globals.SignPerm(lg[i])
    if !isone(s)
      return false
    end
  end
  return true
end

################################################################################
#
#  Check if an extension must be ramified
#
################################################################################

function must_be_ramified(L::GAP.GapObj, i::Int)
  GG = L[1]
  HH = L[i+1]
  KK = L[i]
  proj = GAP.Globals.NaturalHomomorphismByNormalSubgroup(GG, HH)
  target_grp = GAP.Globals.ImagesSource(proj)
  mH1 = GAP.Globals.NaturalHomomorphismByNormalSubgroup(target_grp, GAP.Globals.Image(proj, KK))
  H = GAP.Globals.ImagesSource(mH1)
  #I need to consider the conjgacy classes of cyclic subgroups
  #As far as I know, there is no way of getting only the cyclic ones...
  lS = GAP.Globals.ConjugacyClassesSubgroups(H)
  found_one = false
  found_all = true
  for i = 1:length(lS)
    S = GAP.Globals.Representative(lS[i])
    if !GAP.Globals.IsCyclic(S) || isone(GAP.Globals.Size(S))
      continue
    end
    g = GAP.Globals.MinimalGeneratingSet(S)[1]
    n = GAP.Globals.Order(g)
    preimgs = GAP.Globals.List(GAP.Globals.PreImages(mH1, g))
    fl = true
    for x in preimgs
      m = GAP.Globals.Order(x)
      if m == n
        fl = false
        found_all = false
        break
      end
    end
    if fl
      found_one = true
    end
    if !found_all && found_one
      break
    end
  end
  return found_all, found_one
end

################################################################################
#
#  Conductors
#
################################################################################

function _conductors_using_cocycles(F::FieldsTower, st::Vector{Int}, l_cond::Vector)
  lp = ramified_primes(F)
  auts = automorphism_list(F.field, copy = false)
  projections = F.projections_for_conductors
  G = GAP.Globals.ImagesSource(projections[1])
  E = GAP.Globals.Source(projections[1])
  D = F.isomorphism
  n = prod(st)
  O = maximal_order(F)
  inertia_subgroups = Dict{ZZRingElem, Vector{Hecke.morphism_type(AbsSimpleNumField, AbsSimpleNumField)}}()
  for p in lp
    lP = prime_decomposition(O, p)
    Hp = inertia_subgroup(lP[1][1])
    gHp = small_generating_set(Hp)
    inertia_subgroups[p] = gHp
  end
  must_ramify = Vector{Vector{ZZRingElem}}(undef, length(projections))
  cant_ramify = Vector{Vector{ZZRingElem}}(undef, length(projections))
  for s = 1:length(projections)
    proj = projections[s]
    ramify_here = Vector{ZZRingElem}()
    not_ramify_here = Vector{ZZRingElem}()
    for p in lp
      gHp = inertia_subgroups[p]
      els = [D[g] for g in gHp]
      sub = GAP.Globals.Subgroup(G, GAP.GapObj(els))
      ord = GAP.Globals.Size(sub)
      subgs = Vector{GAP.GapObj}()
      preimages = Vector{Vector{GAP.GapObj}}(undef, length(els))
      for j = 1:length(els)
        preimages[j] = Vector{GAP.GapObj}(GAP.Globals.List(GAP.Globals.PreImages(proj, els[j])))
      end
      #Now, I need to check all the possible subgroups.
      it = cartesian_product_iterator(UnitRange{Int}[1:n for i = 1:length(els)], inplace = true)
      sizes_preimages = Int[]
      for I in it
        sub = GAP.Globals.Subgroup(E, GAP.GapObj([preimages[i][I[i]] for i = 1:length(els)]))
        push!(sizes_preimages, GAP.Globals.Size(sub))
        if maximum(sizes_preimages) != ord && minimum(sizes_preimages) == ord
          break
        end
      end
      if minimum(sizes_preimages) != ord
        push!(ramify_here, p)
      elseif maximum(sizes_preimages) == ord && !divides(ZZRingElem(n), p)[1]
        push!(not_ramify_here, p)
      end
    end
    if isempty(ramify_here) && isempty(not_ramify_here)
      return l_cond
    end
    must_ramify[s] = ramify_here
    cant_ramify[s] = not_ramify_here
  end
  #Now, we use what we found.
  l_new = typeof(l_cond)()
  for i = 1:length(l_cond)
    tp, wp = l_cond[i]
    satisfies_emb = trues(length(projections))
    for j = 1:length(projections)
      possible_emb = true
      for p in must_ramify[j]
        if divides(ZZRingElem(tp), p)[1]
          continue
        end
        if divides(ZZRingElem(n), p)[1]
          found = false
          for (q, w) in wp
            if minimum(q, copy = false) == p
              found = true
              break
            end
          end
          if !found
            possible_emb = false
            break
          end
        else
          possible_emb = false
        end
        if !possible_emb
          break
        end
      end
      if !possible_emb
        satisfies_emb[j] = false
        continue
      end
      for p in cant_ramify[j]
        if divides(ZZRingElem(tp), p)[1]
          possible_emb = false
          continue
        end
        if divides(ZZRingElem(n), p)[1]
          found = false
          for (q, w) in wp
            if minimum(q, copy = false) == p
              found = true
              break
            end
          end
          if found
            possible_emb = false
            break
          end
        end
        if !possible_emb
          break
        end
      end
      if !possible_emb
        satisfies_emb[j] = false
      else
        break
      end
    end
    if any(satisfies_emb)
      push!(l_new, l_cond[i])
    end
  end
  return l_new
end

function conductors_with_restrictions(F::FieldsTower, st::Vector{Int}, IdG::GAP.GapObj, bound::ZZRingElem; unramified_outside::Vector{ZZRingElem} = ZZRingElem[])

  O = maximal_order(F)
  l_cond = Hecke.conductors(O, st, bound, unramified_outside = unramified_outside)
  G = GAP.Globals.SmallGroup(IdG)
  new_conds = _conductors_using_cocycles(F, st, l_cond)
  if length(st) != 1 || !is_prime(st[1]) || isempty(new_conds)
    return new_conds
  end
  #If the extension is cyclic, I take care of the discriminant being a square or not for the wild ramification
  is_square = is_discriminant_square(IdG)
  p = st[1]
  v = valuation(discriminant(O), p)
  is_square_disc_base_field = iszero(mod(v*p, 2))
  td = prime_decomposition_type(O, p)
  if iseven(length(td)) || iseven(td[1][1]) || isodd(p)
    #Regardless of the exponents, the norm of the discriminant will be a square
    if is_square && is_square_disc_base_field
      return new_conds
    elseif is_square
      return typeof(new_conds)()
    else
      return new_conds
    end
  end
  #Now, p must be 2.
  if is_square && is_square_disc_base_field
    #Only the even exponents are allowed!
    newer_conds = typeof(new_conds)()
    for i = 1:length(new_conds)
      if isempty(new_conds[i][2])
        push!(newer_conds, new_conds[i])
        continue
      end
      if iszero(mod(first(values(new_conds[i][2])), 2))
        push!(newer_conds, new_conds[i])
      end
    end
  elseif is_square
    #Only the odd exponents are allowed!
    newer_conds = typeof(new_conds)()
    for i = 1:length(new_conds)
      if !isempty(new_conds[i][2]) && !iszero(mod(first(values(new_conds[i][2])), 2))
        push!(newer_conds, new_conds[i])
      end
    end
  else
    newer_conds = new_conds
  end

  #Now, tame ramification.
  list_tame = Int[x[1] for x in newer_conds]
  list_tame = coprime_base(list_tame)
  l = length(list_tame)
  for i = 1:length(list_tame)
    x = list_tame[i]
    if !isone(x) && !is_prime(x)
      append!(list_tame, Hecke.divisors(x))
    end
  end
  list_tame = coprime_base(list_tame)
  for q in list_tame
    q == 1 && continue
    #@assert is_prime(q)
    v = valuation(discriminant(O), q)
    is_square_disc_base_field = iszero(mod(v*p, 2))
    td = prime_decomposition_type(O, q)
    if iszero(mod(length(td) * td[1][1] * (p-1), 2))
      #Regardless of the exponents, the norm of the discriminant will be a square
      if is_square && is_square_disc_base_field
        continue
      elseif is_square || is_square_disc_base_field
        return typeof(new_conds)()
      else
        continue
      end
    end
    #Now, p must be 2.
    if is_square && is_square_disc_base_field
      #Only the even exponents are allowed!
      #Therefore the prime can't ramify
      newest_conds = typeof(new_conds)()
      for i = 1:length(newer_conds)
        if !iszero(mod(newer_conds[i][1], q))
          push!(newer_conds, newer_conds[i])
        end
      end
    elseif is_square
      #Only the odd exponents are allowed!
      #Therefore the prime must ramify
      newest_conds = typeof(new_conds)()
      for i = 1:length(newer_conds)
        if iszero(mod(newer_conds[i][1], q))
          push!(newest_conds, newer_conds[i])
        end
      end
    else
      newest_conds = newer_conds
    end
    newer_conds = newest_conds
  end
  return newer_conds
end
