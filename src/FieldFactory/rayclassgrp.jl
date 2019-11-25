###############################################################################
#
#  Ray Class Group: Ctx
#
###############################################################################

mutable struct ctx_rayclassgrp
  order::NfOrd
  class_group_map::MapClassGrp #The class group mod n map 
  n::Int #the n for n_quo
  diffC::fmpz #exponent of the full class group, divided by n
  units::Vector{FacElem{nf_elem, AnticNumberField}}
  princ_gens::Vector{FacElem{nf_elem, AnticNumberField}}
  
  computed::Vector{Tuple{Dict{NfOrdIdl, Int}, Bool, MapRayClassGrp}}
  
  function ctx_rayclassgrp()
    z = new()
    return z
  end
end

function rayclassgrp_ctx(O::NfOrd, expo::Int)

  C1, mC1 = class_group(O)
  valclass = ppio(exponent(C1), fmpz(expo))[1]
  C, mC = Hecke.n_part_class_group(mC1, expo)
  ctx = ctx_rayclassgrp()
  ctx.order = O
  ctx.class_group_map = mC
  ctx.n = expo
  ctx.diffC = Int(divexact(exponent(C1), exponent(C)))
  return ctx

end

function assure_elements_to_be_eval(ctx::ctx_rayclassgrp)
  if isdefined(ctx, :units)
    return nothing
  end
  OK = ctx.order
  U, mU = unit_group_fac_elem(OK)
  mC = ctx.class_group_map
  _assure_princ_gen(mC)
  n = ctx.n
  units = FacElem{nf_elem, AnticNumberField}[_preproc(mU(U[i]), fmpz(n)) for i = 1:ngens(U)]
  princ_gens = FacElem{nf_elem, AnticNumberField}[_preproc(mC.princ_gens[i][2], fmpz(n)) for i = 1:length(mC.princ_gens)]
  ctx.units = units
  ctx.princ_gens = princ_gens
  return nothing
end

###############################################################################
#
#  Ray Class Group: Fields function
#
###############################################################################

function empty_ray_class(m::NfOrdIdl)
  O = order(parent(m))
  X = DiagonalGroup(Int[])
  
  local exp
  let O = O
    function exp(a::GrpAbFinGenElem)
      return FacElem(Dict(ideal(O,1) => fmpz(1)))
    end
  end
  
  local disclog
  let X = X
    function disclog(J::Union{NfOrdIdl, FacElem{NfOrdIdl}})
      return X(Int[])
    end
  end
  
  mp = Hecke.MapRayClassGrp()
  mp.header = Hecke.MapHeader(X, FacElemMon(parent(m)) , exp, disclog)
  mp.defining_modulus = (m, InfPlc[])
  return X,mp

end

function ray_class_group_quo(m::NfOrdIdl, y1::Dict{NfOrdIdl,Int}, y2::Dict{NfOrdIdl,Int}, inf_plc::Vector{InfPlc}, ctx::ctx_rayclassgrp; check::Bool = true, GRH::Bool = true)

  mC = ctx.class_group_map
  C = domain(mC)
  diffC = ctx.diffC

  if isempty(y1) && isempty(y2) && isempty(inf_plc)
    local exp_c
    let mC = mC
      function exp_c(a::GrpAbFinGenElem)
        return FacElem(Dict(mC(a) => 1))
      end
    end
    return class_as_ray_class(quo(C, ctx.n, false)[1], mC, exp_c, m)
  end
  
  O = ctx.order
  K = nf(O)
  n_quo = ctx.n

  lp = merge(max, y1, y2)
  
  powers = Vector{Tuple{NfOrdIdl, NfOrdIdl}}()
  quo_rings = Tuple{NfOrdQuoRing, Hecke.AbsOrdQuoMap{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem}}}[]
  groups_and_maps = Tuple{GrpAbFinGen, Hecke.GrpAbFinGenToAbsOrdQuoRingMultMap{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem}}}[]
  for (PP, ee) in lp
    if isone(ee)
      dtame = Dict{NfOrdIdl, Int}(PP => 1)
      dwild = Dict{NfOrdIdl, Int}()
    else
      dwild = Dict{NfOrdIdl, Int}(PP => ee)
      if haskey(y1, PP)
        dtame = Dict{NfOrdIdl, Int}(PP => 1)
      else
        dtame = Dict{NfOrdIdl, Int}()
      end
    end
    QQ = PP^ee
    
    push!(powers, (PP, QQ))
    QQQ, mQQQ = quo(O, QQ)
    if ee == 1
      QQQ.factor = dtame
    else
      QQQ.factor = dwild
    end
    push!(quo_rings, (QQQ, mQQQ))
    push!(groups_and_maps, _mult_grp_mod_n(quo_rings[end][1], dtame, dwild, n_quo))
  end
  
  if isempty(groups_and_maps)
    nG = 0
    expon = fmpz(1)
  else  
    nG = sum(ngens(x[1]) for x in groups_and_maps)
    expon = lcm([exponent(x[1]) for x in groups_and_maps])
  end
  
  
  if iseven(n_quo)
    p = InfPlc[ x for x in inf_plc if isreal(x) ]
  else
    p = InfPlc[]
  end
  H, lH = log_infinite_primes(O, p)
  expon = lcm(expon, exponent(H))
  
  if exponent(C)*expon < n_quo && check
    return empty_ray_class(m)
  end
  
  assure_elements_to_be_eval(ctx)
  exp_class, Kel = find_coprime_representatives(mC, m, lp)
  
  
  nU = length(ctx.units) 
  # We construct the relation matrix and evaluate units and relations with the class group in the quotient by m
  # Then we compute the discrete logarithms  
  
  R = zero_matrix(FlintZZ, 2*(ngens(C)+nG+ngens(H))+nU, ngens(C)+ngens(H)+nG)
  for i = 1:ncols(R)
    R[i+ngens(C)+nG+ngens(H)+nU, i] = n_quo
  end
  for i=1:ngens(C)
    R[i, i] = C.snf[i]
  end
  ind = 1
  for s = 1:length(quo_rings) 
    G = groups_and_maps[s][1]
    @assert issnf(G)
    for i = 1:ngens(G)
      R[i+ngens(C)+ind-1, i+ngens(C)+ind-1] = G.snf[i]
    end
    ind += ngens(G)
  end
  for i = 1:ngens(H)
    R[ngens(C)+nG+i, ngens(C)+nG+i] = 2
  end


  @vprint :RayFacElem 1 "Collecting elements to be evaluated; first, units \n"
  tobeeval = Vector{FacElem{nf_elem, AnticNumberField}}(undef, nU+ngens(C))
  for i = 1:nU
    tobeeval[i] = ctx.units[i]
  end
  for i = 1:ngens(C)
    tobeeval[i+nU] = _preproc(ctx.princ_gens[i]*FacElem(Dict(Kel[i] => C.snf[i])), expon)
  end

  ind = 1
  for i = 1:length(groups_and_maps)
    exp_q = gcd(expon, norm(powers[i][2])- divexact(norm(powers[i][2]), norm(powers[i][1])))
    evals = fac_elems_eval(powers[i][1], powers[i][2], tobeeval, exp_q)
    Qr = quo_rings[i][1]
    mG = groups_and_maps[i][2]
    for j = 1:nU
      a = (mG\Qr(evals[j])).coeff
      for s = 1:ncols(a)
        R[j+nG+ngens(H)+ngens(C), ngens(C)+s+ind-1] = a[1, s]
      end
    end
    
    for j = 1:ngens(C)
      a = (mG\Qr(evals[j+nU])).coeff
      for s = 1:ncols(a)
        R[j, ngens(C)+ind+s-1] = -a[1, s]
      end
    end
    ind += ngens(groups_and_maps[i][1])
  end 
  
  if !isempty(p)
    for j = 1:nU
      aa = lH(tobeeval[j])::GrpAbFinGenElem
      for s = 1:ngens(H)
        R[j+nG+ngens(C)+ngens(H), ngens(C)+ind-1+s] = aa[s] 
      end
    end
    for j = 1:ngens(C)
      aa = lH(tobeeval[j+nU])::GrpAbFinGenElem
      for s = 1:ngens(H)
        R[j, ngens(C)+ind-1+s] = -aa[s] 
      end
    end
  end  
  
  X = AbelianGroup(R)
  
  invd = invmod(fmpz(diffC), expon)
  local disclog
  let X = X, mC = mC, invd = invd, C = C, exp_class = exp_class, powers = powers, groups_and_maps = groups_and_maps, quo_rings = quo_rings, lH = lH, diffC = diffC, n_quo = n_quo, m = m, p = p, expon = expon
    
    # Discrete logarithm
    function disclog(J::FacElem{NfOrdIdl, NfOrdIdlSet})
      @vprint :RayFacElem 1 "Disc log of element $J \n"
      a1 = id(X)
      for (f, k) in J
        a1 += k*disclog(f)
      end
      return a1
    end
  
    function disclog(J::NfOrdIdl)
      @hassert :RayFacElem 1 iscoprime(J, m)
      if isone(J)
        @vprint :RayFacElem 1 "J is one \n"
        return id(X)
      end
      coeffs = zero_matrix(FlintZZ, 1, ngens(X))
      if J.is_principal == 1 && isdefined(J, :princ_gen)
        z = FacElem(Dict(J.princ_gen.elem_in_nf => diffC))
      else
        L = mC\J
        for i = 1:ngens(C)
          coeffs[1, i] = L[i]
        end
        @vprint :RayFacElem 1 "Disc log of element J in the Class Group: $(L.coeff) \n"
        eL = exp_class(L)
        inv!(eL)
        add_to_key!(eL.fac, J, 1) 
        pow!(eL, diffC)
        @vprint :RayFacElem 1 "This ideal is principal: $I \n"
        z = principal_gen_fac_elem(eL)
      end
      ii = 1
      z1 = _preproc(z, expon)
      for i = 1:length(powers)
        P, Q = powers[i]
        exponq = gcd(expon, norm(Q)-divexact(norm(Q), norm(P)))
        el = fac_elems_eval(P, Q, FacElem{nf_elem, AnticNumberField}[z1], exponq)
        y = (invd*(groups_and_maps[i][2]\quo_rings[i][1](el[1]))).coeff
        for s = 1:ncols(y)
          coeffs[1, ii-1+ngens(C)+s] = y[1, s]
        end
        ii += ngens(groups_and_maps[i][1])
      end
      if !isempty(p)
        b = lH(z).coeff
        for s = 1:ncols(b)
          coeffs[1, ii-1+s+ngens(C)] = b[1, s]
        end
      end 
      return X(coeffs)
    end 
  end
  
  Dgens = Tuple{NfOrdElem, GrpAbFinGenElem}[]
  ind = 1
  #We need generators of the full multiplicative group
  #In particular, we need the idempotents...
  if !isone(length(powers))
    for i = 1:length(powers)
      P, QQ = powers[i]
      mG = groups_and_maps[i][2]
      J = ideal(O, 1)
      minJ = fmpz(1)
      mins = fmpz(1)
      for j = 1:length(powers)
        if minimum(powers[j][1], copy = false) != minimum(P, copy = false)
          mins = lcm(mins, minimum(powers[j][2], copy = false))
          continue
        end
        if j != i
          J *= powers[j][2]
          minJ = lcm(minJ, minimum(powers[j][2], copy = false))
        end
      end
      J.minimum = minJ
      i1, i2 = idempotents(QQ, J)
      if !isone(mins)
        d, u1, v1 = gcdx(minimum(QQ, copy = false), mins)
        i1 = i1*(u1*minimum(QQ, copy = false) + v1*mins) + u1*minimum(QQ, copy = false) *i2
        i2 = v1*mins*i2
      end   
      @hassert :RayFacElem 1 isone(i1+i2)
      @hassert :RayFacElem 1 i1 in QQ
      @hassert :RayFacElem 1 i2 in J
      @hassert :RayFacElem 1 i2 in ideal(O, mins)
      gens = mG.generators
      if isempty(p)
        if haskey(mG.tame, P)
          gens_tame = mG.tame[P].generators
          for s = 1:length(gens_tame)
            gens_tame[s] = gens_tame[s]*i2 + i1
            @hassert :RayFacElem 1 isone(mod(gens_tame[s], J*ideal(O, mins)))
          end
          mG.tame[P].generators = gens_tame
        end
        if haskey(mG.wild, P)
          gens_wild = mG.wild[P].generators
          for s = 1:length(gens_wild)
            gens_wild[s] = gens_wild[s]*i2 + i1
            @hassert :RayFacElem 1 isone(mod(gens_wild[s], J*ideal(O, mins)))
          end
          mG.wild[P].generators = gens_wild
        end
        for s = 1:length(gens)
          el_to_push = gens[s].elem*i2+i1
          @hassert :RayFacElem 1 isone(mod(el_to_push, J*ideal(O, mins)))
          push!(Dgens, (el_to_push, X[ngens(C)+ind-1+s]))
        end
      else
        if haskey(mG.tame, P)
          gens_tame = mG.tame[P].generators
          for s = 1:length(gens_tame)
            gens_tame[s] = make_positive(gens_tame[s]*i2 + i1, minimum(m, copy = false))
          end
          mG.tame[P].generators = gens_tame
        end
        if haskey(mG.wild, P)
          gens_wild = mG.wild[P].generators
          for s = 1:length(gens_wild)
            gens_wild[s] = make_positive(gens_wild[s]*i2 + i1, minimum(m, copy = false))
          end
          mG.wild[P].generators = gens_wild
        end
        for s = 1:length(gens)
          elgen = make_positive(gens[s].elem*i2 + i1, minimum(m, copy = false))
          push!(Dgens, (elgen, X[ngens(C)+ind-1+s]))
        end
      end
      ind += length(gens)
    end
  else
    mG = groups_and_maps[1][2]
    gens = mG.generators
    if !isempty(p)
      for s = 1:length(gens)
        elgen = make_positive(gens[s].elem, minimum(m, copy = false))
        push!(Dgens, (elgen, X[ngens(C)+s]))
      end
    else
      for s = 1:length(gens)
        elgen = gens[s].elem
        push!(Dgens, (elgen, X[ngens(C)+s]))
      end
    end
  end
    
  ind = 1
  for i = 1:length(powers)
    mG = groups_and_maps[i][2]
    for (prim, mprim) in mG.tame
      dis = zero_matrix(FlintZZ, 1, ngens(X))
      to_be_c = mprim.disc_log.coeff
      for i = 1:length(to_be_c)
        dis[1, ind-1+i+ngens(C)] = to_be_c[1, i]
      end
      mprim.disc_log = X(dis)
    end
    ind += ngens(domain(mG))
  end
  
  disc_log_inf = Dict{InfPlc, GrpAbFinGenElem}()
  for i = 1:length(p)
    eldi = zeros(FlintZZ, ngens(X))
    eldi[ngens(X) - length(inf_plc) + i] = 1
    disc_log_inf[p[i]] = X(eldi)
  end
  
  mp = MapRayClassGrp()
  mp.header = MapHeader(X, FacElemMon(parent(m)))
  mp.header.preimage = disclog
  mp.fact_mod = lp
  mp.defining_modulus = (m, p)
  mp.powers = powers
  mp.groups_and_maps = groups_and_maps
  mp.disc_log_inf_plc = disc_log_inf
  mp.gens_mult_grp_disc_log = Dgens
  mp.clgrpmap = mC
  return X, mp
  
end


function log_infinite_primes(O::NfOrd, p::Array{InfPlc,1})
  if isempty(p)
    S = DiagonalGroup(Int[])
    
    local log1
    let S = S
      function log1(B::T) where T <: Union{nf_elem ,FacElem{nf_elem, AnticNumberField}}
        return id(S)
      end
    end 
    return S, log1
  end
  
  S = DiagonalGroup(Int[2 for i=1:length(p)])
  local log
  let S = S, p = p
    function log(B::T) where T <: Union{nf_elem ,FacElem{nf_elem, AnticNumberField}}
      emb = signs(B, p)
      ar = zero_matrix(FlintZZ, 1, length(p))
      for i = 1:length(p)
        if emb[p[i]] == -1
          ar[1, i] = 1
        end
      end
      return S(ar)
    end
  end 
  return S, log
end


function ray_class_group_quo(O::NfOrd, m::Int, wprimes::Dict{NfOrdIdl,Int}, inf_plc::Array{InfPlc,1}, ctx::ctx_rayclassgrp; GRH::Bool = true)
  
  d1 = Dict{NfOrdIdl, Int}()
  lp = factor(m)
  I = ideal(O, 1)
  minI = fmpz(1)
  for q in keys(lp.fac)
    lq = prime_decomposition(O, q) 
    for (P, e) in lq
      I *= P
      d1[P] = 1
    end   
    minI = q*minI
  end
  if !isempty(wprimes)
    for (p, v) in wprimes
      qq = p^v
      I *= qq
      minI = lcm(minI, minimum(qq, copy = false))
    end
  end
  I.minimum = minI
  return ray_class_group_quo(I, d1, wprimes, inf_plc, ctx, GRH = GRH)
  
end



function ray_class_group_quo(O::NfOrd, y::Dict{NfOrdIdl, Int}, inf_plc::Array{InfPlc, 1}, ctx::ctx_rayclassgrp; GRH::Bool = true, check::Bool = true)
  
  y1=Dict{NfOrdIdl,Int}()
  y2=Dict{NfOrdIdl,Int}()
  n = ctx.n
  for (q,e) in y
    if gcd(norm(q)-1, n) != 1
      y1[q] = Int(1)
      if gcd(norm(q), n) != 1 && e >= 2
        y2[q] = Int(e)
      end
    elseif gcd(norm(q), n) != 1 && e >= 2
      y2[q] = Int(e)
    end
  end
  I=ideal(O,1)
  for (q,vq) in y1
    I*=q
  end
  for (q,vq) in y2
    I*=q^vq
  end
  return ray_class_group_quo(I, y1, y2, inf_plc, ctx, GRH = GRH, check = check)

end

###############################################################################
#
#  Maximal abelian subfield for fields function
#
###############################################################################

function check_abelian_extensions(class_fields::Vector{Tuple{Hecke.ClassField{Hecke.MapRayClassGrp,GrpAbFinGenMap}, Vector{GrpAbFinGenMap}}}, autos::Array{NfToNfMor, 1}, emb_sub::NfToNfMor)

  @vprint :MaxAbExt 3 "Starting checking abelian extension\n"
  K = base_field(class_fields[1][1])
  d = degree(K)
  G = domain(class_fields[1][2][1])
  expo = G.snf[end]
  com, uncom = ppio(Int(expo), d)
  if com == 1
    return Hecke.ClassField{Hecke.MapRayClassGrp,GrpAbFinGenMap}[x[1] for x in class_fields]
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
  R = GF(p, cached = false)
  Rx, x = PolynomialRing(R, "x", cached = false)
  fmod = Rx(K.pol)
  mp_pol = Rx(emb_sub.prim_img)
  for i = 1:length(autos)
    pol = Rx(autos[i].prim_img)
    if mp_pol ==  Hecke.compose_mod(mp_pol, pol, fmod)
      push!(act_indices, i)
      #I compute the order of the automorphisms. I need the exponent of the relative extension!
      j = 2
      att = Hecke.compose_mod(pol, pol, fmod)
      while att != x
        att = Hecke.compose_mod(pol, att, fmod)
        j += 1
      end
      push!(expG_arr, j)
    end
  end
  expG = lcm(expG_arr)
  expG1 = ppio(expG, com)[1]
  com1 = ppio(com, expG1)[1]
  @vprint :MaxAbExt 3 "Context for ray class groups\n"
  
  OK = maximal_order(K)
  rcg_ctx = Hecke.rayclassgrp_ctx(OK, com1*expG1)
  
  @vprint :MaxAbExt 3 "Ordering the class fields\n"
  
  mins = Vector{fmpz}(undef, length(class_fields))
  for i = 1:length(mins)
    mins[i] = minimum(defining_modulus(class_fields[i][1])[1])
  end
  ismax = trues(length(mins))
  for i = 1:length(ismax)
    for j = i+1:length(ismax)
      if ismax[j] 
        i2 = ppio(mins[i], mins[j])[2]
        if isone(i2)
          ismax[i] = false
          break
        end 
        i3 = ppio(mins[j], mins[i])[2]
        if isone(i3)
          ismax[j] = false
        end
      end
    end
  end
  ord_class_fields = Vector{Int}(undef, length(ismax))
  j1 = 1
  j2 = length(ismax)
  for i = 1:length(ismax)
    if ismax[i]
      ord_class_fields[j1] = i
      j1 += 1
    else
      ord_class_fields[j2] = i
      j2 -= 1
    end
  end
  
  cfields = Hecke.ClassField{Hecke.MapRayClassGrp, GrpAbFinGenMap}[]
  for i = 1:length(class_fields)
    @vprint :MaxAbExt 3 "Class Field $i\n"
    C, res_act = class_fields[ord_class_fields[i]]
    res_act_new = Vector{GrpAbFinGenMap}(undef, length(act_indices))
    for i = 1:length(act_indices)
      res_act_new[i] = res_act[act_indices[i]]
    end
    fl = check_abelian_extension(C, res_act_new, emb_sub, rcg_ctx)
    if fl
      push!(cfields, C)
    end
  end
  return cfields
  
end


function check_abelian_extension(C::Hecke.ClassField, res_act::Vector{GrpAbFinGenMap}, emb_sub::NfToNfMor, rcg_ctx::Hecke.ctx_rayclassgrp)

  #I consider the action on every P-sylow and see if it is trivial
  G = codomain(C.quotientmap)
  expG = Int(exponent(G))
  fac = factor(rcg_ctx.n)
  prime_to_test = Int[]
  new_prime = false
  for (P, v) in fac
    # I check that the action of the P-Sylow has no fixed points.
    PS, mPS = psylow_subgroup(G, P)
    s, ms = snf(PS)
    act_sub = induce_action_on_subgroup(ms*mPS, res_act)
    if !isfixed_point_free(act_sub)
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
    C1 = ray_class_field(C.rayclassgroupmap, Hecke.GrpAbFinGenMap(Hecke.compose(C.quotientmap, mQ)))
    #@vtime :MaxAbExt 1 
    fl = _maximal_abelian_subfield(C1, emb_sub, rcg_ctx, expG)
  else
    #@vtime :MaxAbExt 1 
    fl = _maximal_abelian_subfield(C, emb_sub, rcg_ctx, expG)
  end
  return fl

end

function _bound_exp_conductor_wild(O::NfOrd, n::Int, q::Int, bound::fmpz)
  d = degree(O)
  lp = prime_decomposition_type(O, q)
  f_times_r = divexact(d, lp[1][2]) 
  sq = fmpz(q)^f_times_r
  nbound = n+n*lp[1][2]*valuation(n,q)-div(fmpz(n), q^(valuation(n,q)))
  obound = flog(bound, sq)
  bound_max_ap = min(nbound, obound)  #bound on ap
  return div(q*bound_max_ap, n*(q-1)) #bound on the exponent in the conductor
end

function minimumd(D::Dict{NfOrdIdl, Int}, deg_ext::Int)
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


function _maximal_abelian_subfield(A::Hecke.ClassField, mp::Hecke.NfToNfMor, ctx::Hecke.ctx_rayclassgrp, expG::Int)
  K = base_field(A)
  k = domain(mp)
  ZK = maximal_order(K)
  zk = maximal_order(k)
  expected_order = div(degree(K), degree(k))
  if gcd(expected_order, degree(A)) == 1
    return false
  end
  # disc(ZK/Q) = N(disc(ZK/zk)) * disc(zk)^deg
  # we need the disc ZK/k, well a conductor.
  d = abs(div(discriminant(ZK), discriminant(zk)^expected_order))
  mR1 = A.rayclassgroupmap
  expo = Int(exponent(codomain(A.quotientmap)))
  deg = expected_order
  #First, a suitable modulus for A over k
  #I take the discriminant K/k times the norm of the conductor A/K
  fm0 = Dict{NfOrdIdl, Int}()
  for (P, e) in mR1.fact_mod
    p = intersect_prime(mp, P)
    if haskey(fm0, p)
      if !iscoprime(minimum(P, copy = false), deg*expo)
        fm0[p] += e
      end
    else
      if !iscoprime(minimum(P, copy = false), deg*expo)
        fm0[p] = e
      else
        fm0[p] = 1
      end
    end
  end
  lp = factor(ideal(zk, d))
  for (P, e) in lp
    if haskey(fm0, P)
      if !iscoprime(minimum(P, copy = false), deg*expo)
        fm0[P] += e
      end
    else
      if !iscoprime(minimum(P, copy = false), deg*expo)
        fm0[P] = e
      else
        fm0[P] = 1
      end
    end
  end
  
  #Now, I extend this modulus to K
  fM0 = Dict{NfOrdIdl, Int}()
  for (p, v) in fm0
    lp = prime_decomposition(mp, p)
    if iscoprime(minimum(p, copy = false), expo*deg)
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
    @vtime :MaxAbExt 3 R, mR = Hecke.ray_class_group_quo(ZK, fM0, defining_modulus(mR1)[2], ctx, check = false)
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
    if istotally_real(K) && isempty(defining_modulus(mR1)[2])
      inf_plc = InfPlc[]
    else
      inf_plc = real_places(k)
    end
    #@vtime :MaxAbExt 1 
    r, mr = Hecke.ray_class_group(zk, fm0, inf_plc, n_quo = ctx.n)
  else
    rel_plc = true
    if istotally_real(K) && isempty(defining_modulus(mR1)[2])
      rel_plc = false
    end
    modulo = minimumd(fm0, expo * expected_order)
    #@vtime :MaxAbExt 1 
    r, mr = Hecke.ray_class_groupQQ(zk, modulo, rel_plc, ctx.n)
  end
  #@vtime :MaxAbExt 1 
  lP, gS = Hecke.find_gens(mR, coprime_to = minimum(defining_modulus(mR1)[1]))
  listn = NfOrdIdl[norm(mp, x) for x in lP]
  # Create the map between R and r by taking norms
  preimgs = Vector{GrpAbFinGenElem}(undef, length(listn))
  for i = 1:length(preimgs)
    preimgs[i] = mr\listn[i]
  end
  proj = hom(gS, preimgs)
  #compute the norm group of A in R
  prms = Vector{GrpAbFinGenElem}(undef, length(lP))
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


