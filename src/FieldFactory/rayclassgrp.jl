###############################################################################
#
#  Ray Class Group: Ctx
#
###############################################################################

mutable struct ctx_rayclassgrp
  order::AbsSimpleNumFieldOrder
  class_group_map::MapClassGrp #The class group mod n map
  n::Int #the n for n_quo
  diffC::ZZRingElem #exponent of the full class group, divided by n
  units::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}
  princ_gens::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}

  computed::Vector{Tuple{Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}, Bool, MapRayClassGrp}}
  multiplicative_groups::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, GrpAbFinGenToAbsOrdQuoRingMultMap}

  function ctx_rayclassgrp()
    z = new()
    return z
  end
end

function rayclassgrp_ctx(O::AbsSimpleNumFieldOrder, expo::Int)

  C1, mC1 = class_group(O, use_aut = true)
  valclass = ppio(exponent(C1), ZZRingElem(expo))[1]
  C, mC = Hecke.n_part_class_group(mC1, expo)
  ctx = ctx_rayclassgrp()
  ctx.order = O
  ctx.class_group_map = mC
  ctx.n = expo
  ctx.diffC = Int(divexact(exponent(C1), exponent(C)))
  ctx.multiplicative_groups = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, GrpAbFinGenToAbsOrdQuoRingMultMap}()
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
  units = FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}[_preproc(mU(U[i]), ZZRingElem(n)) for i = 1:ngens(U)]
  princ_gens = FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}[_preproc(mC.princ_gens[i][2], ZZRingElem(n)) for i = 1:length(mC.princ_gens)]
  ctx.units = units
  ctx.princ_gens = princ_gens
  return nothing
end

###############################################################################
#
#  Ray Class Group: Fields function
#
###############################################################################

function ray_class_group_quo(m::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, y1::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},Int}, y2::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},Int}, inf_plc::Vector{<: InfPlc}, ctx::ctx_rayclassgrp; check::Bool = true, GRH::Bool = true)

  mC = ctx.class_group_map
  C = domain(mC)
  diffC = ctx.diffC

  if isempty(y1) && isempty(y2) && isempty(inf_plc)
    local exp_c
    let mC = mC
      function exp_c(a::FinGenAbGroupElem)
        return FacElem(Dict(mC(a) => 1))
      end
    end
    return class_as_ray_class(C, mC, exp_c, m, ctx.n)
  end

  O = ctx.order
  K = nf(O)
  n_quo = ctx.n

  lp = merge(max, y1, y2)

  powers = Vector{Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}}()
  quo_rings = Tuple{AbsSimpleNumFieldOrderQuoRing, Hecke.AbsOrdQuoMap{AbsNumFieldOrder{AbsSimpleNumField,AbsSimpleNumFieldElem},AbsNumFieldOrderIdeal{AbsSimpleNumField,AbsSimpleNumFieldElem},AbsSimpleNumFieldOrderElem}}[]
  groups_and_maps = Tuple{FinGenAbGroup, Hecke.GrpAbFinGenToAbsOrdQuoRingMultMap{AbsNumFieldOrder{AbsSimpleNumField,AbsSimpleNumFieldElem},AbsNumFieldOrderIdeal{AbsSimpleNumField,AbsSimpleNumFieldElem},AbsSimpleNumFieldOrderElem}}[]
  for (PP, ee) in lp
    if isone(ee)
      dtame = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}(PP => 1)
      dwild = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}()
    else
      dwild = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}(PP => ee)
      if haskey(y1, PP)
        dtame = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}(PP => 1)
      else
        dtame = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}()
      end
    end
    QQ = PP^ee

    push!(powers, (PP, QQ))
    if haskey(ctx.multiplicative_groups, QQ)
      cached_map = ctx.multiplicative_groups[QQ]
      QQQ = codomain(cached_map)
      mQQQ = AbsOrdQuoMap(O, QQQ)
      push!(quo_rings, (QQQ, mQQQ))
      new_map = GrpAbFinGenToAbsOrdQuoRingMultMap(domain(cached_map), QQQ, copy(cached_map.generators), cached_map.discrete_logarithm)
      # If we do new_map.tame = copy(cached_map.tame), this is only shallow copy
      # but the keys of this dictionary are maps, which have a .generators field.
      # These generators are changed to assert coprimeness, but if they are always
      # identical, we make them too large eventually
      new_map.tame = Dict(P => begin @assert !isdefined(y, :modulus); _n = GrpAbFinGenToAbsOrdMap(domain(y), codomain(y), copy(y.generators), y.discrete_logarithm); if isdefined(y, :disc_log) _n.disc_log = y.disc_log; end; _n; end for (P, y) in cached_map.tame)
      new_map.wild = Dict(P => begin @assert !isdefined(y, :modulus); _n = GrpAbFinGenToAbsOrdMap(domain(y), codomain(y), copy(y.generators), y.discrete_logarithm); if isdefined(y, :disc_log) _n.disc_log = y.disc_log; end; _n; end for (P, y) in cached_map.wild)
      push!(groups_and_maps, (domain(new_map), new_map))
    else
      QQQ, mQQQ = quo(O, QQ)
      if ee == 1
        QQQ.factor = dtame
      else
        QQQ.factor = dwild
      end
      push!(quo_rings, (QQQ, mQQQ))
      gandm = _mult_grp_mod_n(quo_rings[end][1], dtame, dwild, n_quo)
      map_to_cache = GrpAbFinGenToAbsOrdQuoRingMultMap(gandm[1], QQQ, copy(gandm[2].generators), gandm[2].discrete_logarithm)
      # See above why we cannot just copy
      map_to_cache.tame = Dict(P => begin @assert !isdefined(y, :modulus); _n = GrpAbFinGenToAbsOrdMap(domain(y), codomain(y), copy(y.generators), y.discrete_logarithm); if isdefined(y, :disc_log) _n.disc_log = y.disc_log; end; _n; end for (P, y) in gandm[2].tame)
      map_to_cache.wild = Dict(P => begin @assert !isdefined(y, :modulus); _n = GrpAbFinGenToAbsOrdMap(domain(y), codomain(y), copy(y.generators), y.discrete_logarithm); if isdefined(y, :disc_log) _n.disc_log = y.disc_log; end; _n; end for (P, y) in gandm[2].wild)
      ctx.multiplicative_groups[QQ] = map_to_cache
      push!(groups_and_maps, gandm)
    end
  end

  if isempty(groups_and_maps)
    nG = 0
    expon = ZZRingElem(1)
  else
    nG = sum(ngens(x[1]) for x in groups_and_maps)
    expon = lcm([exponent(x[1]) for x in groups_and_maps])
  end


  if iseven(n_quo)
    p = eltype(inf_plc)[ x for x in inf_plc if isreal(x) ]
  else
    p = eltype(inf_plc)[]
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
    @assert is_snf(G)
    for i = 1:ngens(G)
      R[i+ngens(C)+ind-1, i+ngens(C)+ind-1] = G.snf[i]
    end
    ind += ngens(G)
  end
  for i = 1:ngens(H)
    R[ngens(C)+nG+i, ngens(C)+nG+i] = 2
  end


  @vprintln :RayFacElem 1 "Collecting elements to be evaluated; first, units"
  tobeeval = Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}(undef, nU+ngens(C))
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
      aa = lH(tobeeval[j])::FinGenAbGroupElem
      for s = 1:ngens(H)
        R[j+nG+ngens(C)+ngens(H), ngens(C)+ind-1+s] = aa[s]
      end
    end
    for j = 1:ngens(C)
      aa = lH(tobeeval[j+nU])::FinGenAbGroupElem
      for s = 1:ngens(H)
        R[j, ngens(C)+ind-1+s] = -aa[s]
      end
    end
  end

  X = abelian_group(R)
  X.exponent = n_quo
  if isone(order(X))
    mp = MapRayClassGrp()
    mp.header = MapHeader(X, FacElemMon(parent(m)))
    return X, mp
  end

  invd = invmod(ZZRingElem(diffC), expon)
  local disclog
  let X = X, mC = mC, invd = invd, C = C, exp_class = exp_class, powers = powers, groups_and_maps = groups_and_maps, quo_rings = quo_rings, lH = lH, diffC = diffC, n_quo = n_quo, m = m, p = p, expon = expon

    # Discrete logarithm
    function disclog(J::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
      @vprintln :RayFacElem 1 "Disc log of element $J"
      a1 = id(X)
      for (f, k) in J
        a1 += k*disclog(f)
      end
      return a1
    end

    function disclog(J::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
      @hassert :RayFacElem 1 is_coprime(J, m)
      if isone(J)
        @vprintln :RayFacElem 1 "J is one"
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
        @vprintln :RayFacElem 1 "Disc log of element J in the Class Group: $(L.coeff)"
        eL = exp_class(L)
        inv!(eL)
        add_to_key!(eL.fac, J, 1)
        pow!(eL, diffC)
        @vprintln :RayFacElem 1 "This ideal is principal: $eL"
        z = principal_generator_fac_elem(eL)
      end
      ii = 1
      z1 = _preproc(z, expon)
      for i = 1:length(powers)
        P, Q = powers[i]
        exponq = gcd(expon, norm(Q)-divexact(norm(Q), norm(P)))
        el = fac_elems_eval(P, Q, FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}[z1], exponq)
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
      return FinGenAbGroupElem(X, coeffs)
    end
  end

  Dgens = Tuple{AbsSimpleNumFieldOrderElem, FinGenAbGroupElem}[]
  ind = 1
  #We need generators of the full multiplicative group
  #In particular, we need the idempotents...
  if !isone(length(powers))
    for i = 1:length(powers)
      P, QQ = powers[i]
      mG = groups_and_maps[i][2]
      J = ideal(O, 1)
      minJ = ZZRingElem(1)
      mins = ZZRingElem(1)
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
      new_mprim = GrpAbFinGenToAbsOrdMap(domain(mprim), codomain(mprim), copy(mprim.generators), mprim.discrete_logarithm)
      dis = zero_matrix(FlintZZ, 1, ngens(X))
      to_be_c = mprim.disc_log.coeff
      for i = 1:length(to_be_c)
        dis[1, ind-1+i+ngens(C)] = to_be_c[1, i]
      end
      new_mprim.disc_log = FinGenAbGroupElem(X, dis)
      mG.tame[prim] = new_mprim
    end
    ind += ngens(domain(mG))
  end

  disc_log_inf = Dict{eltype(p), FinGenAbGroupElem}()
  for i = 1:length(p)
    eldi = zero_matrix(FlintZZ, 1, ngens(X))
    eldi[1, ngens(X) - length(inf_plc) + i] = 1
    disc_log_inf[p[i]] = FinGenAbGroupElem(X, eldi)
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
  X.exponent = ZZRingElem(n_quo)
  return X, mp

end


function log_infinite_primes(O::AbsSimpleNumFieldOrder, p::Vector{<: InfPlc})
  if isempty(p)
    S = abelian_group(Int[])

    local log1
    let S = S
      function log1(B::T) where T <: Union{AbsSimpleNumFieldElem ,FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}
        return id(S)
      end
    end
    return S, log1
  end

  S = abelian_group(Int[2 for i=1:length(p)])
  local log
  let S = S, p = p
    function log(B::T) where T <: Union{AbsSimpleNumFieldElem ,FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}
      emb = signs(B, _embedding.(p))
      ar = zero_matrix(FlintZZ, 1, length(p))
      for i = 1:length(p)
        if emb[_embedding(p[i])] == -1
          ar[1, i] = 1
        end
      end
      return FinGenAbGroupElem(S, ar)
    end
  end
  return S, log
end


function ray_class_group_quo(O::AbsSimpleNumFieldOrder, m::Int, wprimes::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},Int}, inf_plc::Vector{<: InfPlc}, ctx::ctx_rayclassgrp; GRH::Bool = true)

  d1 = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}()
  lp = factor(m)
  I = ideal(O, 1)
  minI = ZZRingElem(1)
  for q in keys(lp.fac)
    lq = prime_decomposition(O, q)
    for (P, e) in lq
      if !haskey(wprimes, P)
        I *= P
        d1[P] = 1
      else
        d1[P] = 1
      end
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



function ray_class_group_quo(O::AbsSimpleNumFieldOrder, y::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}, inf_plc::Vector{<: InfPlc}, ctx::ctx_rayclassgrp; GRH::Bool = true, check::Bool = true)

  y1=Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},Int}()
  y2=Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},Int}()
  n = ctx.n
  for (q, e) in y
    if gcd(norm(q)-1, n) != 1
      y1[q] = 1
      if gcd(norm(q), n) != 1 && e >= 2
        y2[q] = e
      end
    elseif gcd(norm(q), n) != 1 && e >= 2
      y2[q] = e
    end
  end
  I = ideal(O,1)
  for (q, vq) in y1
    I *= q
  end
  for (q, vq) in y2
    I *= q^vq
  end
  return ray_class_group_quo(I, y1, y2, inf_plc, ctx, GRH = GRH, check = check)

end
