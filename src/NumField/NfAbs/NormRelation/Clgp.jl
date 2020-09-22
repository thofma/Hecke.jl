function _class_group(O::NfOrd; saturate::Bool = true, redo::Bool = false)
  if !redo
    c = Hecke._get_ClassGrpCtx_of_order(O, false)
    if c !== nothing
      c::Hecke.ClassGrpCtx{SMat{fmpz}}
      @assert c.finished
      return class_group(c, O)
    end
  end
  K = nf(O)
  G, mG = automorphism_group(K)
  if degree(K) > 25 && has_useful_brauer_relation(G) 
    lll(O)
    fl, N = norm_relation(K, small_degree = false)
    @assert fl
    return class_group_via_brauer(O, N, recursive = true, compact = false, saturate = saturate)
  end
  return class_group(O, use_aut = true)
end


function get_sunits_from_subfield_data(OK, N; recursive::Bool = false, compact::Bool = true)
  K = nf(OK)
  fbbound = Hecke.factor_base_bound_grh(OK)
  S = prime_ideals_up_to(OK, fbbound)
  @vprint :NormRelation 1 "Factor base bound: $fbbound\n"
  c, UZK = _setup_for_norm_relation_fun(K, S)

  docompact = false
  onlyp = 0

  if Hecke.isprime_power(index(N)) && compact
    docompact = true
    _, onlyp = ispower(index(N))
  end

  if recursive
    for i = 1:length(N.subfields)
      if !(i in N.nonredundant)
        continue
      end
      L = N.subfields[i][1]
      if N.isnormal[i] && degree(L) > 25
        @vprint :NormRelation 1 "Computing class group of $(L.pol)\n"
        _class_group(lll(maximal_order(L)), saturate = false)
      end
    end
  end

  @vprint :NormRelation 1 "Doing something in the subfields\n"
  if !docompact
    _add_sunits_from_brauer_relation!(c, UZK, N)
  else
    @vprint :NormRelation 1 "Using the compact presentation\n"
    _add_sunits_from_brauer_relation!(c, UZK, N, compact = onlyp)
  end
  return c, UZK
end 


function class_group_via_brauer(O::NfOrd, N::NormRelation; saturate::Bool = true, recursive::Bool = false, do_lll::Bool = true, compact::Bool = true, stable = 3.5)
  K = N.K
  if do_lll
    OK = lll(maximal_order(nf(O)))
  else
    OK = O
  end
  
  c, UZK = get_sunits_from_subfield_data(OK, N, recursive = recursive, compact = compact)
  #auts = automorphisms(K)
  #c.aut_grp = Hecke.class_group_add_auto(c, auts)
 
  if saturate || isone(index(N))
    for (p, e) in factor(index(N))
      @vprint :NormRelation 1 "Saturating at $p \n"
      b = Hecke.saturate!(c, UZK, Int(p), stable)
      while b
        idx = Hecke._validate_class_unit_group(c, UZK)[1]
        @vprint :NormRelation 1 "Index bound from analysis $idx\n"
        b = Hecke.saturate!(c, UZK, Int(p), stable)
      end
    end
    idx = Hecke._validate_class_unit_group(c, UZK)[1]
    @vprint :NormRelation 1 "Index is $idx (should be 1)!\n"
    if idx != 1
      @vprint :NormRelation 1 "Index is $idx (should be 1)!\n"
    end
    @assert idx == 1
  
    @vprint :NormRelation 1 "\n"
    c, _ = simplify(c)
  
    c.finished = true
    UZK.finished = true
    Hecke._set_ClassGrpCtx_of_order(OK, c)
    Hecke._set_UnitGrpCtx_of_order(OK, UZK)
    return class_group(c, O)
  else
    # We finish off the computation by a relation search in OK
    Hecke._set_ClassGrpCtx_of_order(OK, c)
    Hecke._set_UnitGrpCtx_of_order(OK, UZK)
    c, UZK, d = Hecke._class_unit_group(OK, saturate_at_2 = false)
    @assert isone(d)

    return Hecke.class_group(c, O)
  end
end