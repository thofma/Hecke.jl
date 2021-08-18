function get_chain(G::GAP.GapObj)
  @assert GAP.Globals.IsSolvable(G)
  if GAP.Globals.IsAbelian(G)
    return [GAP.Globals.TrivialSubgroup(G), G]
  end
  lN = GAP.Globals.CharacteristicSubgroups(G)
  acceptable = trues(length(lN))
  orders = [GAP.Globals.Size(lN[i]) for i = 1:length(lN)]
  for i = 1:length(lN)
    if !acceptable[i]
      continue
    end
    for j = i+1:length(lN)
      if orders[j] == orders[i]
        id_i = GAP.Globals.IdGroup(lN[i])
        id_j = GAP.Globals.IdGroup(lN[j])
        if id_i == id_j
          id_fi = GAP.Globals.IdGroup(GAP.Globals.FactorGroup(G, lN[i]))
          id_fj = GAP.Globals.IdGroup(GAP.Globals.FactorGroup(G, lN[j]))
          if id_fi == id_fj
            acceptable[i] = false
            acceptable[j] == false
            break
          end
        end
      end
    end
  end
  subs_for_series = [lN[i] for i = 1:length(lN) if acceptable[i]]
  res = [GAP.Globals.TrivialSubgroup(G)]
  while res[end] != G
    contain = [x for x in subs_for_series if GAP.Globals.IsSubset(x, res[end])]
    abelian_subgroups = [x for x in contain if GAP.Globals.IsAbelian(GAP.Globals.FactorGroup(x, res[end]))]
    j = 0
    ord = 0
    for i = 1:length(abelian_subgroups)
      x = abelian_subgroups[i]
      sx = GAP.Globals.Size(x)
      if sx > ord
        j = i
        ord = sx
      end
    end
    push!(res, abelian_subgroups[j])
  end
  return res
end

function get_chain(G::GAP.GapObj, H::GAP.GapObj)
  lN = GAP.Globals.NormalSubgroups(G)
  possible_subs = []
  idH = GAP.Globals.IdGroup(H)
  for i = 1:length(lN)
    if GAP.Globals.IdGroup(GAP.Globals.FactorGroup(G, lN[i])) == idH
      push!(possible_subs, lN[i])
    end
  end
  if isempty(possible_subs)
    error("The field can't be extended!")
  end
  res = possible_subs[1]
  if length(possible_subs) > 1
    csubs = [GAP.Globals.IdGroup(x) for x in possible_subs]
    best_occ = length(csubs)
    for i = 1:length(csubs)
      occ = 0
      for j = 1:length(csubs)
        if csubs[i] == csubs[j]
          occ += 1
        end
      end
      if occ == 1
        res = possible_subs[i]
        break
      elseif occ < best_occ
        res = possible_subs[i]
      end
    end
  end
  mp = GAP.Globals.NaturalHomomorphismByNormalSubgroup(G, res)
  K = GAP.Globals.Kernel(mp)
  return get_chain(K)
end
