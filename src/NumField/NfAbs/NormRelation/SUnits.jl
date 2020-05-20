export norm_relation

function _add_sunits_from_norm_relation!(c, UZK, N)
  cp = sort!(collect(Set(minimum(x) for x = c.FB.ideals)))
  K = N.K
  for i = 1:length(N)
    k, mk = subfield(N, i)
    @vprint :NormRelation 1 "Computing maximal order ..."
    zk = maximal_order(k)
    @vprint :NormRelation 1 "Computing lll basis ... "
    zk = lll(zk)
    @vprint :NormRelation 1 "Computing class group of $k... "
    class_group(zk, use_aut = true)
    @vprint :NormRelation 1 "done"
    lpk = NfOrdIdl[ P[1] for p in cp for P = prime_decomposition(zk, p)]
    @vprint :NormRelation 1 "Now computing the S-unit group for lp of length $(length(lpk))"
    @assert length(lpk) > 0
    Szk, mS = Hecke.sunit_mod_units_group_fac_elem(lpk)

    D = Dict{nf_elem, nf_elem}()
    function N_mk(x, D, i)
      if haskey(D, x)
        return D[x]
      else
        y = N(x, i)
        D[x] = y
        return y
      end
    end


    #D = Dict{nf_elem, nf_elem}()
    cc = Vector{Tuple{Int, fmpz}}[]
    for j in 1:length(N.coefficients_gen[i])
      @vprint :NormRelation 1 "Inducing the action ... "
      z = induce_action(N, i, j, lpk, c.FB, cc)

      @vprint :NormRelation "Feeding in the S-units of the small field ... "


      for l=1:ngens(Szk)
        u = mS(Szk[l])  #do compact rep here???
        valofnewelement = mul(mS.valuations[l], z)
        el_to_add = FacElem(Dict{nf_elem, AnticNumberField}((N(x, i, j), v) for (x,v) = u.fac))
        Hecke.class_group_add_relation(c, el_to_add, valofnewelement)#, always = false)
      end
    end

    # Skipping the units
    U, mU = unit_group_fac_elem(zk)
    for j=2:ngens(U) # I cannot add a torsion unit. He will hang forever.
      u = mU(U[j])
      Hecke._add_unit(UZK, FacElem(Dict((N_mk(x, D, i), v) for (x,v) = u.fac)))
    end
    UZK.units = Hecke.reduce(UZK.units, UZK.tors_prec)
  end
end

function _compute_sunit_and_unit_group!(c, U, N, saturate = true)
  cp = sort!(collect(Set(minimum(x) for x = c.FB.ideals)))
  K = N.K
  skipped_units = FacElem{nf_elem, AnticNumberField}[]
  autos = automorphisms(field(N), copy = false)

  for i = 1:length(N)
    k, mk = subfield(N, i)
    zk = lll(maximal_order(k))
    print("Computing class group of $k... ")
    @time class_group(zk, redo = true, use_aut = true)
    println("done")
    lpk = NfOrdIdl[ P[1] for p in cp for P = prime_decomposition(zk, p)]
    println("Now computing the S-unit group for lp of length $(length(lpk))")
    @assert length(lpk) > 0
    @time Szk, mS = Hecke.sunit_mod_units_group_fac_elem(lpk)
    @show length(N.coefficients_gen[i])

    #D = Dict{nf_elem, nf_elem}()
    cc = Vector{Tuple{Int, fmpz}}[]
    induced = induce_action_from_subfield(N, i, lpk, c.FB, cc)
    for l in 1:ngens(Szk)
      u = mS(Szk[l])
      for j in 1:length(induced)
        aut = autos[j]
        valofnewelement = mul(mS.valuations[l], induced[j])
        el_to_add = FacElem(Dict{nf_elem, AnticNumberField}((aut(embedding(N, i)(x)), v) for (x,v) = u.fac))
        Hecke.class_group_add_relation(c, el_to_add, valofnewelement)#, always = false)
      end
    end


    #for j in 1:length(N.coefficients_gen[i])
    #  println("Inducing the action ... ")
    #  @time z = induce_action(N, i, j, lpk, c.FB, cc)

    #  print("Feeding in the S-units of the small field ... ")

    #  for l=1:ngens(Szk)
    #    u = mS(Szk[l])  #do compact rep here???
    #    valofnewelement = mul(mS.valuations[l], z)
    #    Hecke.class_group_add_relation(c, FacElem(Dict((N(x, i, j), v) for (x,v) = u.fac)), valofnewelement)
    #  end
    #end

    println("done")

    u, mu = unit_group_fac_elem(zk)
    for n=2:ngens(u) # I cannot add a torsion unit. He will hang forever.
      uelem = mu(u[n])
      for j in 1:length(induced)
        aut = autos[j]
        lifted_unit = FacElem(Dict((aut(embedding(N, i)(x)), v) for (x,v) = uelem.fac))
        bb = Hecke._add_unit(U, lifted_unit)
        @show bb
        if !bb
          push!(skipped_units, lifted_unit)
        end
      end
      U.units = Hecke.reduce(U.units, U.tors_prec)
    end

    #for j in 1:length(N.coefficients_gen[i])
    #  for n=2:ngens(u) # I cannot add a torsion unit. He will hang forever.
    #    uelem = mu(u[n])
    #    lifted_unit = FacElem(Dict((N(x, i, j), v) for (x,v) = uelem.fac))
    #    bb = Hecke._add_unit(U, lifted_unit)
    #    @show bb
    #    if !bb
    #      push!(skipped_units, lifted_unit)
    #    end
    #  end
    #  U.units = Hecke.reduce(U.units, U.tors_prec)
    #end
  end


  @show length(skipped_units)

  for lifted_unit in skipped_units
    @show Hecke.regulator(U.units, 64)
    Hecke._add_dependent_unit(U, lifted_unit)
  end

  U.tentative_regulator = Hecke.regulator(U.units, 64)

  println("Now saturating ... ")

  if saturate
    for (p, e) in factor(index(N))
      b = Hecke.saturate!(c, U, Int(p))
      while b
        b = Hecke.saturate!(c, U, Int(p))
      end
    end
  end
  return c, U
end

################################################################################
#
#  Redo the S-unit computation for Brauer norm relation
#
################################################################################

function _embed(N::NormRelation, i::Int, a::nf_elem)
  b = get(N.embed_cache_triv[i], a, nothing)
  if b === nothing
    _, mk = subfield(N, i)
    c = mk(a)
    N.embed_cache_triv[i][a] = c
    return c
  else
    return b
  end
end

# pure

function _add_sunits_from_brauer_relation!(c, UZK, N; invariant = false, compact::Int = 0)
  # I am assuming that c.FB.ideals is invariant under the action of the Galois group
  cp = sort!(collect(Set(minimum(x) for x = c.FB.ideals)))
  K = N.K
  for i = 1:length(N)
    if isdefined(N, :nonredundant) && !(i in N.nonredundant)
      continue
    end
    k, mk = subfield(N, i)
    @vprint :NormRelation 1 "Looking at the subfield $i / $(length(N)) with defining equation $(k.pol) \n"
    @vprint :NormRelation 1 "Computing lll basis of maximal order ...\n"
    zk = maximal_order(k)
    zk = lll(zk)
    @vprint :NormRelation 1 "Computing class group ... \n"
    class_group(zk, redo = false, use_aut = true)
    lpk = NfOrdIdl[ P[1] for p in cp for P = prime_decomposition(zk, p)]
	  #lpk = unique!(NfOrdIdl[ intersect_prime(mk, P) for P in c.FB.ideals])
    @assert length(lpk) > 0
    @vprint :NormRelation 1 "Computing sunit group for set of size $(length(lpk)) ... \n"
    Szk, mS = Hecke.sunit_mod_units_group_fac_elem(lpk)

    @vprint :NormRelation 1 "Coercing the sunits into the big field ...\n"
    z = induce_action_just_from_subfield(N, i, lpk, c.FB, invariant)

    for l=1:ngens(Szk)
      @vprint :NormRelation 3 "Sunits $l / $(ngens(Szk))\n"
      u = mS(Szk[l])  #do compact rep here???
      if compact != 0
        @vprint :NormRelation 3 "  Compact presentation ...\n"
        u = Hecke.compact_presentation(u, compact)
      end
      valofnewelement = mul(mS.valuations[l], z)
      @hassert :NormRelation 1 begin zz = mk(evaluate(u)); true; end
      @hassert :NormRelation 1 sparse_row(FlintZZ, [ (i, valuation(zz, p)) for (i, p) in enumerate(c.FB.ideals) if valuation(zz, p) != 0]) == valofnewelement
      @vtime :NormRelation 4 img_u = FacElem(Dict{nf_elem, fmpz}((_embed(N, i, x), v) for (x,v) = u.fac))
      @vtime :NormRelation 4 Hecke.class_group_add_relation(c, img_u, valofnewelement)#, always = false)
    end

    @vprint :NormRelation 1 "Coercing the units into the big field ... \n"
    U, mU = unit_group_fac_elem(zk)
    for j=2:ngens(U) # I cannot add a torsion unit. He will hang forever.
      @vprint :NormRelation 3 "Unit $j / $(ngens(U))\n"
      u = mU(U[j])
      if compact != 0
        @vprint :NormRelation 3 "  Compact presentation ...\n"
        u = Hecke.compact_presentation(u, compact)
      end
      @vtime :NormRelation 4 img_u = FacElem(Dict{nf_elem, fmpz}((_embed(N, i, x), v) for (x,v) = u.fac))
      @vtime :NormRelation 4 Hecke._add_unit(UZK, img_u)
    end
    @vprint :NormRelation 4 "Reducing the units\n"
    @vtime :NormRelation 4 UZK.units = Hecke.reduce(UZK.units, UZK.tors_prec)
  end
  return nothing
end

# TODO: Encode that the i-th field is normal over Q
function induce_action_just_from_subfield(N::NormRelation, i, s, FB, invariant = false)
  S = FB.ideals
  ZK = order(S[1])

  z = zero_matrix(SMat, FlintZZ, 0, length(S))

  mk = embedding(N, i)
  zk = order(s[1])

  @assert mod(degree(ZK), degree(zk)) == 0
  reldeg = divexact(degree(ZK), degree(zk))

  for l in 1:length(s)
    v = Tuple{Int, fmpz}[]
    P = s[l]
    genofsl = elem_in_nf(_embed(N, i, P.gen_two.elem_in_nf))
    pmin = minimum(P, copy = false)
    # Compute the number of ideals
    # Assume that L/K and L/Q are normal
    rele = divexact(ramification_index((FB.fb[pmin].lp)[1][2]), ramification_index(P))
    relf = divexact(degree((FB.fb[pmin].lp)[1][2]), degree(P))
    @assert mod(reldeg, rele * relf) == 0
    numb_ideal = divexact(reldeg, rele * relf)
    found = 0
    for k in 1:length(S)
      Q = S[k]
      if minimum(Q, copy = false) == pmin
        if genofsl in Q
          found += 1
          @assert mod(ramification_index(Q), ramification_index(s[l])) == 0
          push!(v, (k, divexact(ramification_index(Q), ramification_index(s[l]))))
        end
      end
      if invariant && N.isnormal[i]
				if found == numb_ideal
					break
				end
			end
    end
    sort!(v, by = x -> x[1])
    push!(z, sparse_row(FlintZZ, v))
  end
  return z
end

function norm_relation(K::AnticNumberField, coprime::Int = 0; small_degree = true)
  if !small_degree
    @assert coprime == 0
    N = _norm_relation_setup_generic(K, pure = true, small_degree = false)
    return true, N
  end
  local N
  try
    N = _get_nf_norm_relation(K)::Vector{NormRelation{Int}}
    if coprime == 0
      return true, N[1]::NormRelation{Int}
    else
      for i in 1:length(N)
        if coprime == N[i].isoptimal
          return true, N[i]::NormRelation{Int}
        end
      end
      fl, M = has_coprime_norm_relation(K, fmpz(coprime))
      if fl
        push!(N, M)
        return true, M
      end
      return false, NormRelation{Int}()
    end
  catch e
    if !isa(e, AccessorNotSetError)
      rethrow(e)
    end
    if coprime == 0
      M = _norm_relation_setup_generic(K, pure = true, small_degree = true)
      _set_nf_norm_relation(K, NormRelation{Int}[M])
      return true, M::NormRelation{Int}
    else
      fl, M = has_coprime_norm_relation(K, fmpz(coprime))
      if fl
        _set_nf_norm_relation(K, NormRelation{Int}[M])
        return true, M::NormRelation{Int}
      end
      return false, NormRelation{Int}()
    end
  end
end

function _sunit_group_fac_elem_quo_via_brauer(K::AnticNumberField, S, n::Int, invariant::Bool = false)
  @vprint :NormRelation 1 "Setting up the norm relation context ... \n"
  fl, N = norm_relation(K, n)
  if !fl
    fl, N = norm_relation(K, 0)
  end
  @assert fl
  @vprint :NormRelation 1 "Using norm relation $N\n"
  return __sunit_group_fac_elem_quo_via_brauer(N, S, n, invariant)
end

function sunit_group_fac_elem_via_brauer(N::NormRelation, S, invariant::Bool = false)
  return _sunit_group_fac_elem_quo_via_brauer(N, S, 0, invariant)
end


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
 
  if saturate
    for (p, e) in factor(index(N))
      @vprint :NormRelation 1 "Saturating at $p \n"
      b = Hecke.saturate!(c, UZK, Int(p), stable)
      while b
        idx = Hecke._validate_class_unit_group(c, UZK)
        @vprint :NormRelation 1 "Index bound from analysis $idx\n"
        b = Hecke.saturate!(c, UZK, Int(p), stable)
      end
    end
    idx = Hecke._validate_class_unit_group(c, UZK)
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
  end

  Hecke._set_ClassGrpCtx_of_order(OK, c)
  Hecke._set_UnitGrpCtx_of_order(OK, UZK)
  c, UZK, d = Hecke._class_unit_group(OK)
  @assert isone(d)

  return Hecke.class_group(c, O)
end

function __sunit_group_fac_elem_quo_via_brauer(N::NormRelation, S, n::Int, invariant::Bool = false)
  O = order(S[1])

  K = N.K


  if invariant
    c, UZK = Hecke._setup_for_norm_relation_fun(K, S)
    _add_sunits_from_brauer_relation!(c, UZK, N, invariant = true)
  else
    cp = sort!(collect(Set(minimum(x) for x = S)))
    Sclosed = NfOrdIdl[]
    for p in cp
      lp = prime_decomposition(O, p)
      for (P, _) in lp
        push!(Sclosed, P)
      end
    end
    if length(Sclosed) == length(S)
      invariant = true
      Sclosed = S
    end
    @vprint :NormRelation 1 "I am not Galois invariant. Working with S of size $(length(Sclosed))\n"
    c, UZK = _setup_for_norm_relation_fun(K, Sclosed)
    _add_sunits_from_brauer_relation!(c, UZK, N, invariant = true)
  end

  if gcd(index(N), n) != 1
    # I need to saturate
    @vprint :NormRelation 1 "Saturating at "
    for (p, e) in factor(index(N))
      @vprint :NormRelation 1 "$p "
      b = Hecke.saturate!(c, UZK, Int(p))
      while b
        b = Hecke.saturate!(c, UZK, Int(p))
      end
    end
  end
  @vprint :NormRelation 1 "\n"

  # This makes c.R.gen be a basis of the S-units (modulo torsion)
  c, _ = simplify(c)

  if invariant
    sunitsmodunits = c.R_gen # These are generators for the S-units (mod units, mod n)
  else
    # I need to extract the S-units from the Sclosed-units
    # Now I need to find the correct indices in the c.FB.ideals
    sunitsmodunits = typeof(c.R_gen)()
    ind = Int[]
    for P in S
      for i in 1:length(c.FB.ideals)
        if P == c.FB.ideals[i]
          push!(ind, i)
          break
        end
      end
    end
    sort!(ind)
    # ind = indices of S inside c.FB.ideals
    @assert length(Sclosed) == length(c.FB.ideals)
    @assert length(ind) == length(S)
    z = zero_matrix(FlintZZ, length(c.R_gen), length(Sclosed) - length(S))
    for i in 1:length(c.R_gen)
      k = 1
      for j in 1:length(Sclosed)
        if !(j in ind)
          z[i, k] = c.M.bas_gens[i, j]
          if k == ncols(z)
            break
          end
          k = k + 1
        end
      end
    end
    k, K = left_kernel(z)
    for i in 1:nrows(K)
      if iszero_row(K, i)
        continue
      end
      push!(sunitsmodunits, FacElem(c.R_gen, fmpz[K[i, j] for j in 1:ncols(K)]))
    end
  end

  unitsmodtorsion = UZK.units # These are generators for the units (mod n)
  T, mT = torsion_unit_group(O)
  Q, mQ = quo(T, n)
  @assert issnf(Q)
  @assert ngens(Q) == 1
  m = order(Q)

  if !isone(m)
    tomodn = FacElem(elem_in_nf(mT(mQ\Q[1])))
    res_group = abelian_group(append!(fmpz[m], [fmpz(n) for i in 1:(length(sunitsmodunits) + length(unitsmodtorsion))]))

    exp = function(a::GrpAbFinGenElem)
      @assert parent(a) == res_group
      zz = FacElem(convert(Vector{Hecke.nf_elem_or_fac_elem}, unitsmodtorsion), fmpz[a[1 + i] for i in 1:length(unitsmodtorsion)])
      z = mul!(zz, zz, tomodn^a[1])
      zzz = FacElem(convert(Vector{Hecke.nf_elem_or_fac_elem}, sunitsmodunits), fmpz[a[1 + length(unitsmodtorsion) + i] for i in 1:length(sunitsmodunits)])
      mul!(z, z, zzz)
      
      for (k, v) in z.fac
        if iszero(v)
          delete!(z.fac, k)
        end
      end

      return z
    end

    disclog = function(a)
      throw(NotImplemented())
    end
  else # torsion part is one
    res_group = abelian_group([fmpz(n) for i in 1:(length(sunitsmodunits) + length(unitsmodtorsion))])

    exp = function(a::GrpAbFinGenElem)
      @assert parent(a) == res_group
      z = FacElem(convert(Vector{nf_elem_or_fac_elem}, unitsmodtorsion), fmpz[a[i] for i in 1:length(unitsmodtorsion)])
      # This is madness
      zz = FacElem(convert(Vector{nf_elem_or_fac_elem}, sunitsmodunits), fmpz[a[length(unitsmodtorsion) + i] for i in 1:length(sunitsmodunits)])
      z = mul!(z, z, zz)

      for (k, v) in z.fac
        if iszero(v)
          delete!(z.fac, k)
        end
      end

      return z
    end

    disclog = function(a)
      throw(NotImplemented())
    end
  end

  r = Hecke.MapSUnitGrpFacElem()
  r.idl = S
  r.isquotientmap = n

  r.header = Hecke.MapHeader(res_group, FacElemMon(nf(O)), exp, disclog)
  @hassert :NormRelation 9000 begin
    _S, _mS = sunit_group_fac_elem(S)
    _Q, _mQ = quo(_S, n)
    V = quo(_Q, [_mQ(_mS\(r(res_group[i]))) for i in 1:ngens(res_group)])
    order(_Q) == order(res_group) && order(V[1]) == 1
  end
  return res_group, r
end
