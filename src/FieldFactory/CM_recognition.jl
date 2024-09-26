function defines_CM_field(F::FieldsTower)
  K = F.field
  if isodd(degree(K)) || !is_totally_complex(K)
    return false, id_hom(K)
  end
  autsK = F.generators_of_automorphisms
  permGC = GAP.GapObj([_perm_to_gap_perm(x) for x in permutations(autsK)])
  perm_group = GAP.Globals.GroupByGenerators(permGC)
  Z = GAP.Globals.Center(perm_group)
  if isodd(GAP.Globals.Size(Z))
    return false, id_hom(K)
  end
  els = GAP.Globals.Elements(Z)
  for i = 1:length(els)
    @show i
    el = els[i]
    if GAP.Globals.Order(els[i]) != 2
      continue
    end
    word = GAP.Globals.Factorization(perm_group, el)
    rep_of_word = GAP.Globals.ExtRepOfObj(word)
    aut = autsK[rep_of_word[1]]^rep_of_word[2]
    for j = 2:div(length(rep_of_word), 2)
      aut *= autsK[rep_of_word[2*j-1]]^rep_of_word[2*j]
    end
    if is_complex_conjugation(aut)
      return true, aut
    end
  end
  return false, id_hom(K)
end
