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


  @vprint :NormRelation 1 "Doing something in the subfields\n"
  if !docompact
    _add_sunits_from_brauer_relation!(c, UZK, N)
  else
    @vprint :NormRelation 1 "Using the compact presentation\n"
    _add_sunits_from_brauer_relation!(c, UZK, N, compact = onlyp)
  end
  return c, UZK
end 

function class_group_via_brauer(O::NfOrd, N::NormRelation; compact::Bool = true)
  K = N.K
  OK = lll(maximal_order(nf(O)))
 
  c, UZK = get_sunits_from_subfield_data(OK, N, compact = compact)
  for (p, e) in factor(index(N))
    @vprint :NormRelation 1 "Saturating at $p \n"
    b = Hecke.saturate!(c, UZK, Int(p), 3.5, easy_root = true)
    while b
      idx = Hecke._validate_class_unit_group(c, UZK)[1]
      @vprint :NormRelation 1 "Index bound from analysis $idx\n"
      b = Hecke.saturate!(c, UZK, Int(p), 3.5, easy_root = true)
    end
  end
  idx = Hecke._validate_class_unit_group(c, UZK)[1]
  @vprint :NormRelation 1 "Index is $idx (should be 1)!\n"
  if idx != 1
    @vprint :NormRelation 1 "Index is $idx (should be 1)!\n"
  end
  @assert idx == 1
  @vprint :NormRelation 1 "\n"
  c.finished = true
  UZK.finished = true
  Hecke._set_ClassGrpCtx_of_order(OK, c)
  Hecke._set_UnitGrpCtx_of_order(OK, UZK)
  return class_group(c, O)
end