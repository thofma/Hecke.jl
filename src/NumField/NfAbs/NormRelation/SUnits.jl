export norm_relation

function _add_sunits_from_norm_relation!(c, UZK, N)
  cp = sort!(collect(Set(minimum(x) for x = c.FB.ideals)))
  K = N.K
  for i = 1:length(N)
    k, mk = subfield(N, i)
    @vprintln :NormRelation 1 "Computing maximal order ..."
    zk = maximal_order(k)
    @vprintln :NormRelation 1 "Computing lll basis ... "
    zk = lll(zk)
    @vprintln :NormRelation 1 "Computing class group of $k... "
    class_group(zk)
    @vprintln :NormRelation 1 "done"
    lpk = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[ P[1] for p in cp for P = prime_decomposition(zk, p)]
    @vprintln :NormRelation 1 "Now computing the S-unit group for lp of length $(length(lpk))"
    @assert length(lpk) > 0
    Szk, mS = Hecke.sunit_mod_units_group_fac_elem(lpk)

    D = Dict{AbsSimpleNumFieldElem, AbsSimpleNumFieldElem}()
    function N_mk(x, D, i)
      if haskey(D, x)
        return D[x]
      else
        y = N(x, i)
        D[x] = y
        return y
      end
    end



    cc = Vector{Tuple{Int, ZZRingElem}}[]
    for j in 1:length(N.coefficients_gen[i])
      @vprintln :NormRelation 1 "Inducing the action ... "
      z = induce_action(N, i, j, lpk, c.FB, cc)

      @vprintln :NormRelation 1 "Feeding in the S-units of the small field ... "


      for l=1:ngens(Szk)
        u = mS(Szk[l])  #do compact rep here???
        valofnewelement = mS.valuations[l] * z
        el_to_add = FacElem(Dict{AbsSimpleNumFieldElem, AbsSimpleNumField}((N(x, i, j), v) for (x,v) = u.fac))
        Hecke.class_group_add_relation(c, el_to_add, valofnewelement)#, always = false)
      end
    end

    # Skipping the units
    U, mU = unit_group_fac_elem(zk)
    for j=2:ngens(U) # I cannot add a torsion unit. He will hang forever.
      u = mU(U[j])
      Hecke.add_unit!(UZK, FacElem(Dict((N_mk(x, D, i), v) for (x,v) = u.fac)))
    end
    UZK.units = Hecke.reduce(UZK.units, UZK.tors_prec)
  end
end

function _compute_sunit_and_unit_group!(c, U, N, saturate = true)
  cp = sort!(collect(Set(minimum(x) for x = c.FB.ideals)))
  K = N.K
  skipped_units = FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}[]
  autos = automorphism_list(field(N), copy = false)

  for i = 1:length(N)
    k, mk = subfield(N, i)
    zk = lll(maximal_order(k))
    print("Computing class group of $k... ")
    @time class_group(zk, redo = true, use_aut = true)
    println("done")
    lpk = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[ P[1] for p in cp for P = prime_decomposition(zk, p)]
    println("Now computing the S-unit group for lp of length $(length(lpk))")
    @assert length(lpk) > 0
    @time Szk, mS = Hecke.sunit_mod_units_group_fac_elem(lpk)
    @show length(N.coefficients_gen[i])

    #D = Dict{AbsSimpleNumFieldElem, AbsSimpleNumFieldElem}()
    cc = Vector{Tuple{Int, ZZRingElem}}[]
    induced = induce_action_from_subfield(N, i, lpk, c.FB, cc)
    for l in 1:ngens(Szk)
      u = mS(Szk[l])
      for j in 1:length(induced)
        aut = autos[j]
        valofnewelement = mS.valuations[l] * induced[j]
        el_to_add = FacElem(Dict{AbsSimpleNumFieldElem, AbsSimpleNumField}((aut(embedding(N, i)(x)), v) for (x,v) = u.fac))
        Hecke.class_group_add_relation(c, el_to_add, valofnewelement)#, always = false)
      end
    end
    println("done")

    u, mu = unit_group_fac_elem(zk)
    for n=2:ngens(u) # I cannot add a torsion unit. He will hang forever.
      uelem = mu(u[n])
      for j in 1:length(induced)
        aut = autos[j]
        lifted_unit = FacElem(Dict((aut(embedding(N, i)(x)), v) for (x,v) = uelem.fac))
        bb = Hecke.add_unit!(U, lifted_unit)
        @show bb
        if !bb
          push!(skipped_units, lifted_unit)
        end
      end
      U.units = Hecke.reduce(U.units, U.tors_prec)
    end
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

function _embed(N::NormRelation, i::Int, a::AbsSimpleNumFieldElem)
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

function _get_sunits(N, i, lp)
  k = subfield(N, i)[1]
  if degree(k) > 10
    Gk, mGk = automorphism_group(k)
    if has_useful_brauer_relation(Gk)
      Szk, mS = _sunit_group_fac_elem_via_brauer(k, lp, true, index(N) == 1 ? 0 : index(N))
    else
      Szk, mS = Hecke.sunit_group_fac_elem(lp)
    end
  else
    Szk, mS = Hecke.sunit_group_fac_elem(lp)
  end
  return Szk, mS
end

# pure

function _add_sunits_from_brauer_relation!(c, UZK, N; invariant::Bool = false, compact::Int = 0, saturate_units::Bool = false)
  # I am assuming that c.FB.ideals is invariant under the action of the automorphism group used by N
  cp = sort!(collect(Set(minimum(x) for x = c.FB.ideals)))
  K = N.K
  add_unit_later = FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}[]
  @vprintln :NormRelation 1 "Adding trivial relations"
  for I in c.FB.ideals
    a = I.gen_one
    Hecke.class_group_add_relation(c, K(a), QQFieldElem(abs(a)^degree(K)), ZZRingElem(1), orbit = false)
    b = I.gen_two.elem_in_nf
    bn = Hecke.norm_div(b, ZZRingElem(1), 600)
    if nbits(numerator(bn)) < 550
      Hecke.class_group_add_relation(c, b, abs(bn), ZZRingElem(1), orbit = false)
    end
  end
  for i = 1:length(N)
    if isdefined(N, :nonredundant) && !(i in N.nonredundant)
      continue
    end
    k, mk = subfield(N, i)
    @vprintln :NormRelation 1 "Looking at the subfield $i / $(length(N)) with defining equation $(k.pol)"
    @vprintln :NormRelation 1 "Computing lll basis of maximal order ..."
    zk = maximal_order(k)
    zk = lll(zk)
    lpk = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]
    for p in cp
      append!(lpk, prime_ideals_over(zk, p))
    end
    @assert length(lpk) > 0
    @vprintln :NormRelation 1 "Computing sunit group for set of size $(length(lpk)) ..."
    Szk, mS = _get_sunits(N, i, lpk)
    @vprintln :NormRelation 1 "Coercing the sunits into the big field ..."
    z = induce_action_just_from_subfield(N, i, lpk, c.FB, invariant)

    #found_torsion = false
    #CAREFUL! I AM ASSUMING THAT THE FIRST ELEMENT IS A TORSION UNIT!
    for l=2:ngens(Szk)
      @vprintln :NormRelation 3 "Sunits $l / $(ngens(Szk))"
      u = mS(Szk[l])  #do compact rep here???
      if iszero(mS.valuations[l])
        if UZK.finished
          continue
        end
        if compact != 0
          @vprintln :NormRelation 3 "  Compact presentation ..."
          @vtime :NormRelation 4 u = Hecke.compact_presentation(u, compact, decom = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}())
        elseif saturate_units
          @vprintln :NormRelation 3 "  Compact presentation ..."
          @vtime :NormRelation 4 u = Hecke.compact_presentation(u, is_power(index(N))[2], decom = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}())
        end
        @vtime :NormRelation 4 img_u = FacElem(Dict{AbsSimpleNumFieldElem, ZZRingElem}((_embed(N, i, x), v) for (x,v) = u.fac))
        #=
        if !found_torsion
          fl = Hecke.is_torsion_unit(img_u, false, 16)[1]
          if fl
            found_torsion = true
            continue
          end
        end
        =#
        has_full_rk = Hecke.has_full_rank(UZK)
        @vtime :NormRelation 4 ff = Hecke.add_unit!(UZK, img_u)
        if !has_full_rk && !ff
          push!(add_unit_later, img_u)
        end
      else
        valofnewelement = mS.valuations[l] * z
        #=
        if isdefined(c.M, :basis)
          push!(deb_rr, (deepcopy(c.M.basis), deepcopy(valofnewelement)))
          rr = Hecke.reduce_right!(c.M.basis, deepcopy(valofnewelement))
          MM = matrix(c.M.basis)
          vv = zero_matrix(FlintZZ, 1, ncols(MM))
          for (jj, vvv) in valofnewelement
            vv[1, jj] = vvv
          end
          Hecke.reduce_mod_hnf_ur!(vv, MM)
          @assert iszero(rr) == iszero(vv)
          if iszero(rr)
            continue
          end
        end
        =#
        if compact != 0
          sup = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}((lpk[w], t) for (w, t) in mS.valuations[l])
          @vprintln :NormRelation 3 "  Compact presentation ..."
          @vtime :NormRelation 4 u = Hecke.compact_presentation(u, compact, decom = sup)
        end
        @vtime :NormRelation 4 img_u = FacElem(Dict{AbsSimpleNumFieldElem, ZZRingElem}((_embed(N, i, x), v) for (x, v) = u.fac if !iszero(v)))
        @hassert :NormRelation 1 sparse_row(FlintZZ, [ (j, valuation(img_u, p)) for (j, p) in enumerate(c.FB.ideals) if valuation(img_u, p) != 0]) == valofnewelement
        @vtime :NormRelation 4 Hecke.class_group_add_relation(c, img_u, valofnewelement)
        #=
        if rank(c.M) == length(c.FB.ideals)
          h, piv = Hecke.class_group_get_pivot_info(c)
        end
        =#
      end
    end
    @vprintln :NormRelation 4 "Reducing the units"
    @vtime :NormRelation 4 UZK.units = Hecke.reduce(UZK.units, UZK.tors_prec)
  end

  if length(add_unit_later) > 0
    for uu in add_unit_later
      Hecke.add_unit!(UZK, uu)
    end
    UZK.units = Hecke.reduce(UZK.units, UZK.tors_prec)
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
    v = Tuple{Int, ZZRingElem}[]
    P = s[l]
    genofsl = elem_in_nf(_embed(N, i, P.gen_two.elem_in_nf))
    pmin = minimum(P, copy = false)
    # Compute the number of ideals
    # We use this to speed things up if L/K and L/Q are normal.
    # We are checking this below.
    local numb_ideal::Int
    if is_normal(number_field(ZK))
      rele = divexact(ramification_index((FB.fb[pmin].lp)[1][2]), ramification_index(P))
      relf = divexact(degree((FB.fb[pmin].lp)[1][2]), degree(P))
      @assert mod(reldeg, rele * relf) == 0
      numb_ideal = divexact(reldeg, rele * relf)
    else
      numb_ideal = -1
    end
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
      if invariant && N.is_normal[i] && is_normal(number_field(ZK))
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

function norm_relation(K::AbsSimpleNumField, coprime::Int = 0; small_degree = true, cached = true)
  local N
  if cached
    if has_attribute(K, :norm_relation)
      N = get_attribute(K, :norm_relation)::Vector{NormRelation{Int}}
      if coprime == 0
        return true, N[1]::NormRelation{Int}
      else
        for i in 1:length(N)
          if coprime == N[i].isoptimal
            return true, N[i]::NormRelation{Int}
          end
        end
        fl, M = has_coprime_norm_relation(K, ZZRingElem(coprime))
        if fl
          push!(N, M)
          return true, M
        end
        return false, NormRelation{Int}()
      end
    end
  end
  if coprime == 0
    if !has_useful_brauer_relation(automorphism_group(K)[1])
      return false, NormRelation{Int}()
    end
    M = _norm_relation_setup_generic(K, pure = true, small_degree = small_degree)
    set_attribute!(K, :norm_relation, NormRelation{Int}[M])
    return true, M::NormRelation{Int}
  else
    fl, M = has_coprime_norm_relation(K, ZZRingElem(coprime))
    if fl
      set_attribute!(K, :norm_relation, NormRelation{Int}[M])
      return true, M::NormRelation{Int}
    end
    return false, NormRelation{Int}()
  end
end

function _sunit_group_fac_elem_quo_via_brauer(K::AbsSimpleNumField, S, n::Int, invariant::Bool = false; saturate_units::Bool = false)
  @vprintln :NormRelation 1 "Setting up the norm relation context ..."
  fl, N = norm_relation(K, n)
  if !fl
    fl, N = norm_relation(K, 0, small_degree = false)
  end
  @assert fl
  @vprintln :NormRelation 1 "Using norm relation $N"
  compact = 0
  g = gcd(index(N), n)
  compact = 0
  if !isone(g)
    compact = is_power(g)[2]
  end
  return __sunit_group_fac_elem_quo_via_brauer(N, S, n, invariant, compact, saturate_units = saturate_units)::Tuple{FinGenAbGroup, Hecke.MapSUnitGrpFacElem}
end

function _sunit_group_fac_elem_via_brauer(K::AbsSimpleNumField, S::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}, invariant::Bool = false, compact::Int = 0)
  @vprintln :NormRelation 1 "Setting up the norm relation context ..."
  fl, N = norm_relation(K, 0, small_degree = false)
  @assert fl
  @vprintln :NormRelation 1 "Using norm relation $N"
  return __sunit_group_fac_elem_quo_via_brauer(N, S, 0, invariant, compact)::Tuple{FinGenAbGroup, Hecke.MapSUnitGrpFacElem}
end


function sunit_group_fac_elem_via_brauer(N::NormRelation, S, invariant::Bool = false)
  return _sunit_group_fac_elem_quo_via_brauer(N, S, 0, invariant)::Tuple{FinGenAbGroup, Hecke.MapSUnitGrpFacElem}
end

function _setup_for_norm_relation_fun(K, S = prime_ideals_up_to(maximal_order(K), Hecke.factor_base_bound_grh(maximal_order(K))))
  ZK = order(S[1])
  FB = NfFactorBase(ZK, S)
  c = Hecke.class_group_init(FB)
  UZK = get_attribute!(ZK, :UnitGrpCtx) do
    return Hecke.UnitGrpCtx{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}(ZK)
  end::Hecke.UnitGrpCtx{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}
  return c, UZK
end

function _find_perm(v::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}, w::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  p = Dict{Int, Int}()
  for i = 1:length(v)
    pi = findfirst(isequal(v[i]), w)
    @assert pi !== nothing
    p[pi] = i
  end
  return p
end

function __sunit_group_fac_elem_quo_via_brauer(N::NormRelation, S::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}, n::Int, invariant::Bool = false, compact::Int = 0; saturate_units::Bool = false)
  O = order(S[1])
  K = N.K
  if invariant
    c, UZK = _setup_for_norm_relation_fun(K, S)
    _add_sunits_from_brauer_relation!(c, UZK, N, invariant = true, compact = compact, saturate_units = saturate_units)
  else
    cp = sort!(collect(Set(minimum(x) for x = S)))
    Sclosed = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]
    # If K is non-normal and N does not use the full automorphism group, we
    # might be enlarging S too much.
    for p in cp
      append!(Sclosed, prime_ideals_over(O, p))
    end
    if length(Sclosed) == length(S)
      invariant = true
      Sclosed = S
    end
    if !invariant
      @vprintln :NormRelation 1 "I am not Galois invariant. Working with S of size $(length(Sclosed))"
    end
    c, UZK = _setup_for_norm_relation_fun(K, Sclosed)
    _add_sunits_from_brauer_relation!(c, UZK, N, invariant = true, compact = compact, saturate_units = saturate_units)
  end

  if gcd(index(N), n) != 1
    # I need to saturate
    for (p, e) in factor(index(N))
      @vprintln :NormRelation 1 "Saturating at $p"
      b = Hecke.saturate!(c, UZK, Int(p), 3.5, easy_root = true, use_LLL = true)
      while b
        b = Hecke.saturate!(c, UZK, Int(p), 3.5, easy_root = true, use_LLL = true)
      end
    end
    UZK.finished = true
  end

  if index(N) == 1
    UZK.finished = true
  end

  if saturate_units && !UZK.finished
    for (p, e) in factor(index(N))
      @vprintln :NormRelation 1 "Saturating at $p"
      b = Hecke.saturate!(UZK, Int(p), 3.5, easy_root = true, use_LLL = true)
      while b
        b = Hecke.saturate!(UZK, Int(p), 3.5, easy_root = true, use_LLL = true)
      end
    end
    UZK.finished = true
  end

  # This makes c.R.gen a basis of the S-units (modulo torsion)
  c = Hecke.RelSaturate.simplify(c, UZK, use_LLL = true)
  perm_ideals = _find_perm(S, c.FB.ideals)
  if invariant
    sunitsmodunits = FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}[x for x in c.R_gen] # These are generators for the S-units (mod units, mod n)
    valuations_sunitsmodunits = Vector{SRow{ZZRingElem}}(undef, length(S))
    for i = 1:length(sunitsmodunits)
      r = Tuple{Int, ZZRingElem}[(perm_ideals[j], v) for (j, v) in c.M.bas_gens[i]]
      sort!(r, lt = (a,b) -> a[1] < b[1])
      valuations_sunitsmodunits[i] = sparse_row(FlintZZ, r)
    end
  else
    # I need to extract the S-units from the Sclosed-units
    # Now I need to find the correct indices in the c.FB.ideals
    sunitsmodunits = FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}[]
    valuations_sunitsmodunits = SRow{ZZRingElem}[]
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
    K = kernel(z, side = :left)
    for i in 1:nrows(K)
      if is_zero_row(K, i)
        continue
      end
      push!(sunitsmodunits, FacElem(c.R_gen, ZZRingElem[K[i, j] for j in 1:ncols(K)]))
      v_c = sum(SRow{ZZRingElem}[K[i, j]*c.M.bas_gens[j] for j = 1:ncols(K)])
      r = Tuple{Int, ZZRingElem}[(perm_ideals[j], v) for (j, v) in v_c]
      sort!(r, lt = (a,b) -> a[1] < b[1])
      push!(valuations_sunitsmodunits, sparse_row(FlintZZ, r))
    end
  end

  unitsmodtorsion = UZK.units # These are generators for the units (mod n)
  T, mT = torsion_unit_group(O)
  Q, mQ = quo(T, n, false)
  # Q need not be in SNF, but we need that it is generated by one element.
  @assert ngens(Q) == 1
  m = order(Q)
  if !isone(m)
    units = Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}(undef, length(unitsmodtorsion)+1)
    units[1] = FacElem(elem_in_nf(mT(mQ\Q[1])))
    for i = 2:length(units)
      units[i] = unitsmodtorsion[i-1]
    end
    res_group = abelian_group(append!(ZZRingElem[m], [ZZRingElem(n) for i in 1:(length(sunitsmodunits) + length(unitsmodtorsion))]))
  else
    units = unitsmodtorsion
    res_group = abelian_group([ZZRingElem(n) for i in 1:(length(sunitsmodunits) + length(unitsmodtorsion))])
  end
  local exp
  let res_group = res_group, units = units
    function exp(a::FinGenAbGroupElem)
      @assert parent(a) == res_group
      z = prod(units[i]^a[i] for i = 1:length(units))
      if !isempty(sunitsmodunits)
        zz = prod(sunitsmodunits[i]^a[length(units) + i] for i in 1:length(sunitsmodunits))
        mul!(z, z, zz)
      end

      for (k, v) in z.fac
        if iszero(v)
          delete!(z.fac, k)
        end
      end
      return z
    end
  end


  disclog = function(a)
    throw(NotImplemented())
  end

  r = Hecke.MapSUnitGrpFacElem()
  r.valuations = Vector{SRow{ZZRingElem}}(undef, ngens(res_group))
  for i = 1:length(units)
    r.valuations[i] = sparse_row(FlintZZ)
  end
  for i = 1:length(sunitsmodunits)
    r.valuations[i+length(units)] = valuations_sunitsmodunits[i]
  end
  r.idl = S
  r.isquotientmap = n

  r.header = Hecke.MapHeader(res_group, FacElemMon(nf(O)), exp, disclog)
  @hassert :NormRelation 9001 begin
    _S, _mS = Hecke.sunit_group_fac_elem(S)
    @show _S
    @show res_group
    _Q, _mQ = quo(_S, n)
    V = quo(_Q, [_mQ(_mS\(r(res_group[i]))) for i in 1:ngens(res_group)])
    order(_Q) == order(res_group) && order(V[1]) == 1
  end
  @hassert :NormRelation 9000 begin
    fl = true
    for i = 1:ngens(res_group)
      el = r(res_group[i])
      if sparse_row(FlintZZ, [ (j, valuation(el, S[j])) for j = 1:length(S) if valuation(el, S[j]) != 0]) != r.valuations[i]
        fl = false
        break
      end
    end
    fl
  end
  return (res_group, r)::Tuple{FinGenAbGroup, Hecke.MapSUnitGrpFacElem}
end
