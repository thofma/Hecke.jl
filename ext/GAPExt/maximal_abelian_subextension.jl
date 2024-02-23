###############################################################################
#
#  Maximal abelian subfield for fields function
#
###############################################################################

function check_abelian_extensions(class_fields::Vector{Tuple{ClassField{MapRayClassGrp, FinGenAbGroupHom}, Vector{FinGenAbGroupHom}}}, F::FieldsTower, IdExtension::GAP.GapObj)
  K = F.field
  autos = F.generators_of_automorphisms
  i = 1
  while codomain(F.subfields[i]) != K
    i += 1
  end
  #=
  E = GAP.Globals.SmallGroup(IdExtension)
  oE = GAP.gap_to_julia(Int, GAP.Globals.Size(E))
  #I need to compute the degree of the maximal abelian subextension over this subfield.
  deg_mas = Set{Int}()
  if degree(domain(F.subfields[i])) == 1
    idH = GAP.julia_to_gap([1, 1])
  else
    idH = IdGroup(automorphism_list(domain(F.subfields[i])))
  end
  oH = GAP.gap_to_julia(Int, idH[1])
  order_sub = divexact(oE, oH)
  lN = GAP.Globals.NormalSubgroups(E)
  for s = 1:length(lN)
    if GAP.Globals.Size(lN[s]) != order_sub
      continue
    end
    if GAP.Globals.IdGroup(GAP.Globals.FactorGroup(E, lN[s])) == idH
      dS = GAP.gap_to_julia(Vector{Int}, GAP.Globals.AbelianInvariants(lN[s]))
      push!(deg_mas, prod(dS)
    end
  end
  return check_abelian_extensions(class_fields[indices], autos, F.subfields[i], deg_mas)
  =#
  return check_abelian_extensions(class_fields, autos, F.subfields[i])
end

function check_abelian_extensions(class_fields::Vector{Tuple{ClassField{MapRayClassGrp,FinGenAbGroupHom}, Vector{FinGenAbGroupHom}}}, autos::Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, emb_sub::NumFieldHom{AbsSimpleNumField, AbsSimpleNumField})#, deg_mas::Set{Int})
  @vprintln :MaxAbExt 3 "Starting checking abelian extension"
  K = base_field(class_fields[1][1])
  d = degree(K)
  G = domain(class_fields[1][2][1])
  expo = G.snf[end]
  com, uncom = ppio(Int(expo), d)
  if com == 1
    return trues(length(class_fields))
  end
  #I extract the generators that restricted to the domain of emb_sub are the identity.
  #Notice that I can do this only because I know the way I am constructing the generators of the group.
  expG_arr = Int[]
  act_indices = Int[]
  p = 11
  d1 = discriminant(domain(emb_sub))
  d2 = discriminant(K)
  while iszero(mod(d1, p)) || iszero(mod(d2, p))
    p = next_prime(p)
  end
  R = Native.GF(p, cached = false)
  Rx, x = polynomial_ring(R, "x", cached = false)
  fmod = Rx(K.pol)
  mp_pol = Rx(image_primitive_element(emb_sub))
  for i = 1:length(autos)
    pol = Rx(image_primitive_element(autos[i]))
    if mp_pol ==  Hecke.compose_mod(mp_pol, pol, fmod)
      push!(act_indices, i)
      #I compute the order of the automorphisms. I need the exponent of the relative extension!
      push!(expG_arr, _order(autos[i]))
    end
  end
  expG = lcm(expG_arr)
  expG1 = ppio(expG, com)[1]
  @vprintln :MaxAbExt 3 "Context for ray class groups"

  OK = maximal_order(K)
  rcg_ctx = Hecke.rayclassgrp_ctx(OK, com*expG1)

  cfields = trues(length(class_fields))
  for i = 1:length(class_fields)
    @vprintln :MaxAbExt 3 "Class Field $i"
    C, res_act = class_fields[i]
    res_act_new = Vector{FinGenAbGroupHom}(undef, length(act_indices))
    for i = 1:length(act_indices)
      res_act_new[i] = res_act[act_indices[i]]
    end
    cfields[i] = check_abelian_extension(C, res_act_new, emb_sub, rcg_ctx, expG)
  end
  return cfields

end


function check_abelian_extension(C::Hecke.ClassField, res_act::Vector{FinGenAbGroupHom}, emb_sub::NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}, rcg_ctx::Hecke.ctx_rayclassgrp, exponent_extension::Int)
  #I consider the action on every P-sylow and see if it is trivial
  G = codomain(C.quotientmap)
  expG = Int(exponent(G))
  fac = factor(rcg_ctx.n)
  prime_to_test = Int[]
  new_prime = false
  for (P, v) in fac
    # I check that the action of the P-Sylow has no fixed points.
    PS, mPS = sylow_subgroup(G, P, false)
    s, ms = snf(PS)
    act_sub = induce_action_on_subgroup(ms*mPS, res_act)
    if !is_fixed_point_free(act_sub)
      push!(prime_to_test, P)
    end
  end
  if isempty(prime_to_test)
    return true
  end
  n = prod(prime_to_test)
  n1, m = ppio(Int(G.snf[end]), n)
  if m != 1
    # Now, I compute the maximal abelian subextension of the n-part of C
    Q, mQ = quo(G, n1, false)
    C1 = ray_class_field(C.rayclassgroupmap, C.quotientmap*mQ)
    #@vtime :MaxAbExt 1
    fl = _maximal_abelian_subfield(C1, emb_sub, rcg_ctx, exponent_extension)
  else
    #@vtime :MaxAbExt 1
    fl = _maximal_abelian_subfield(C, emb_sub, rcg_ctx, exponent_extension)
  end
  return fl

end

function _bound_exp_conductor_wild(O::AbsSimpleNumFieldOrder, n::Int, q::Int, bound::ZZRingElem)
  d = degree(O)
  lp = prime_decomposition_type(O, q)
  f_times_r = divexact(d, lp[1][2])
  sq = ZZRingElem(q)^f_times_r
  nbound = n+n*lp[1][2]*valuation(n,q)-div(ZZRingElem(n), q^(valuation(n,q)))
  obound = flog(bound, sq)
  bound_max_ap = min(nbound, obound)  #bound on ap
  return div(q*bound_max_ap, n*(q-1)) #bound on the exponent in the conductor
end

function minimumd(D::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}, deg_ext::Int)
  primes_done = Int[]
  res = 1
  for (P, e) in D
    p = Int(minimum(P))
    if p in primes_done
      continue
    else
      push!(primes_done, p)
    end
    ram_index = P.splitting_type[1]
    s, t = divrem(e, ram_index)
    if iszero(t)
      d = min(s, valuation(deg_ext, p)+2)
      res *= p^d
    else
      d = min(s+1, valuation(deg_ext, p)+2)
      res *= p^d
    end
  end
  return res
end

function _maximal_abelian_subfield(A::Hecke.ClassField, mp::Hecke.NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}, ctx::Hecke.ctx_rayclassgrp, exp_extension::Int)
  K = base_field(A)
  k = domain(mp)
  ZK = maximal_order(K)
  zk = maximal_order(k)
  expected_order = Int(ppio(div(degree(K), degree(k)), ctx.n)[1])
  if gcd(expected_order, degree(A)) == 1
    return false
  end
  # disc(ZK/Q) = N(disc(ZK/zk)) * disc(zk)^deg
  # we need the disc ZK/k, well a conductor.
  d = abs(divexact(discriminant(ZK), discriminant(zk)^expected_order))
  mR1 = A.rayclassgroupmap
  expo = Int(exponent(codomain(A.quotientmap)))
  deg = expected_order
  #First, a suitable modulus for A over k
  #I take the discriminant K/k times the norm of the conductor A/K
  fm0 = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}()
  for (P, e) in mR1.fact_mod
    p = intersect_prime(mp, P)
    if !haskey(fm0, p)
      if !is_coprime(minimum(P, copy = false), expo)
        if e > 1
          fm0[p] = e
        end
      else
        fm0[p] = 1
      end
    end
  end
  lp = factor(ideal(zk, d))
  for (P, e) in lp
    if haskey(fm0, P)
      if !is_coprime(minimum(P, copy = false), deg*expo)
        fm0[P] = max(e, fm0[P])
      end
    else
      if !is_coprime(minimum(P, copy = false), deg*expo)
        fm0[P] = e
      else
        fm0[P] = 1
      end
    end
  end
  #Now, I extend this modulus to K
  fM0 = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}()
  for (p, v) in fm0
    lp = prime_decomposition(mp, p)
    if is_coprime(minimum(p, copy = false), expo*deg)
      for (P, e) in lp
        fM0[P] = 1
      end
    else
      for (P, e) in lp
        fM0[P] = e*v
      end
    end
  end
  ind = 0
  if isdefined(ctx, :computed)
    flinf = isempty(defining_modulus(mR1)[2])
    for i = 1:length(ctx.computed)
      idmr, ifmr, mRRR = ctx.computed[i]
      if flinf != ifmr
        continue
      end
      contained = true
      for (P, v) in fM0
        if !haskey(idmr, P) || idmr[P] < v
          contained = false
        end
      end
      if contained
        ind = i
        break
      end
    end
  end
  if iszero(ind)
    @vtime :MaxAbExt 1 R, mR = Hecke.ray_class_group_quo(ZK, fM0, defining_modulus(mR1)[2], ctx, check = false)
    if isdefined(ctx, :computed)
      push!(ctx.computed, (fM0, isempty(defining_modulus(mR1)[2]), mR))
    else
      ctx.computed = [(fM0, isempty(defining_modulus(mR1)[2]), mR)]
    end
  else
    mR = ctx.computed[ind][3]
    R = domain(mR)
  end
  if degree(zk) != 1
    if is_totally_real(K) && isempty(defining_modulus(mR1)[2])
      inf_plc = InfPlc[]
    else
      inf_plc = real_places(k)
    end
    @vtime :MaxAbExt 1  r, mr = Hecke.ray_class_group(zk, fm0, inf_plc, n_quo = ctx.n)
  else
    rel_plc = true
    if is_totally_real(K) && isempty(defining_modulus(mR1)[2])
      rel_plc = false
    end
    modulo = minimumd(fm0, expo * expected_order)
    wrp, trp = ppio(modulo, ctx.n)
    ftrp = factor(trp)
    for (pf, vpf) in ftrp
      if !is_coprime(pf-1, ctx.n)
        wrp *= pf
      end
    end
    @vtime :MaxAbExt 1  r, mr = Hecke.ray_class_groupQQ(zk, Int(wrp), rel_plc, ctx.n)
  end
  @vtime :MaxAbExt 1 lP, gS = Hecke.find_gens(mR, coprime_to = minimum(defining_modulus(mR1)[1]))
  listn = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[norm(mp, x) for x in lP]
  # Create the map between R and r by taking norms
  preimgs = Vector{FinGenAbGroupElem}(undef, length(listn))
  for i = 1:length(preimgs)
    preimgs[i] = mr\listn[i]
  end
  proj = hom(gS, preimgs)
  #compute the norm group of A in R
  prms = Vector{FinGenAbGroupElem}(undef, length(lP))
  for i = 1:length(lP)
    if haskey(mR1.prime_ideal_preimage_cache, lP[i])
      f = mR1.prime_ideal_preimage_cache[lP[i]]
    else
      f = mR1\lP[i]
      mR1.prime_ideal_preimage_cache[lP[i]] = f
    end
    prms[i] = A.quotientmap(f)
  end
  proj1 = hom(gS, prms)
  S, mS = kernel(proj1, false)
  mS1 = mS*proj
  G, mG = Hecke.cokernel(mS1, false)
  return (order(G) == expected_order)::Bool

end
