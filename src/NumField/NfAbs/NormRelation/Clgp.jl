function get_sunits_from_subfield_data!(c::Hecke.ClassGrpCtx, UZK::Hecke.UnitGrpCtx, N::NormRelation; compact::Bool = true)
  docompact = false
  onlyp = 0

  if Hecke.is_prime_power(index(N)) && compact
    docompact = true
    _, onlyp = is_power(index(N))
  end


  @vprintln :NormRelation 1 "Doing something in the subfields"
  if !docompact
    _add_sunits_from_brauer_relation!(c, UZK, N)
  else
    @vprintln :NormRelation 1 "Using the compact presentation"
    _add_sunits_from_brauer_relation!(c, UZK, N, compact = onlyp)
  end
end

function class_group_via_brauer(O::AbsSimpleNumFieldOrder, N::NormRelation; compact::Bool = true)
  K = N.K
  OK = lll(maximal_order(nf(O)))

  bound = Hecke.factor_base_bound_grh(OK)
  @vprintln :NormRelation 1 "Factor base bound: $bound"
  S = prime_ideals_up_to(OK, bound)
  #First, we try with a smaller factor base.

  Sfirst = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]
  primes_added = ZZRingElem[]
  threshold = min(200, div(length(S), 2))
  i = 1
  while length(Sfirst) < threshold
    p = minimum(S[i], copy = false)
    if p in primes_added
      i += 1
      continue
    end
    push!(primes_added, p)
    push!(Sfirst, S[i])
    for j = i+1:length(S)
      if minimum(S[j], copy = false) == p
        push!(Sfirst, S[j])
      end
    end
    i += 1
  end
  @vprintln :NormRelation 1 "Length of the first factor base: $(length(Sfirst))"
  c, UZK = _setup_for_norm_relation_fun(K, Sfirst)
  get_sunits_from_subfield_data!(c, UZK, N, compact = compact)
  for (p, e) in factor(index(N))
    @vprintln :NormRelation 1 "Saturating at $p"
    b = Hecke.saturate!(c, UZK, Int(p), 3.5, easy_root = degree(K) < 30)
    while b
      idx = Hecke._validate_class_unit_group(c, UZK)[1]
      @vprintln :NormRelation 1 "Index bound from analysis $idx"
      b = Hecke.saturate!(c, UZK, Int(p), 3.5, easy_root = degree(K) < 30)
    end
  end
  UZK.finished = true
  idx = Hecke._validate_class_unit_group(c, UZK)[1]
  if !isone(idx)
    c = _setup_for_norm_relation_fun(K, S)[1]
    get_sunits_from_subfield_data!(c, UZK, N, compact = compact)
    for (p, e) in factor(index(N))
      @vprintln :NormRelation 1 "Saturating at $p"
      b = Hecke.saturate!(c, UZK, Int(p), 3.5, easy_root = degree(K) < 30)
      while b
        idx = Hecke._validate_class_unit_group(c, UZK)[1]
        @vprintln :NormRelation 1 "Index bound from analysis $idx"
        b = Hecke.saturate!(c, UZK, Int(p), 3.5, easy_root = degree(K) < 30)
      end
    end
    idx = Hecke._validate_class_unit_group(c, UZK)[1]
  end
  @vprintln :NormRelation 1 "Index is $idx (should be 1)!"
  @assert idx == 1
  @vprintln :NormRelation 1 ""
  c.finished = true
  set_attribute!(OK, :ClassGrpCtx => c)
  set_attribute!(OK, :UnitGrpCtx => UZK)
  return class_group(c, O)
end
