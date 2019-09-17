###############################################################################
#
#  Ray Class Group: Ctx
#
###############################################################################

mutable struct ctx_rayclassgrp
  mC::MapClassGrp
  n::Int
  vect::Vector{fmpz}
  units::Vector{Tuple{NfOrdElem, Dict{fmpz, Int}}}
  princ_gens::Vector{Tuple{NfOrdElem, Dict{fmpz, Int}}}
  
  computed::Vector{Tuple{Dict{NfOrdIdl, Int}, Bool, MapRayClassGrp}}
  
  function ctx_rayclassgrp()
    z = new()
    return z
  end
end

function elems_to_be_eval(ctx::ctx_rayclassgrp, Kel::Vector{nf_elem})
  units = ctx.units
  O = parent(units[1][1])
  princ_gens = ctx.princ_gens
  mC = ctx.mC
  C = domain(ctx.mC)
  vect = ctx.vect
  n = fmpz(ctx.n)
  @vprint :RayFacElem 1 "Collecting elements to be evaluated; first, units \n"
  to_be_eval = Vector{NfOrdElem}(undef, length(units) + length(princ_gens))
  to_be_eval_int = Vector{Dict{fmpz, Int}}(undef, length(units) + length(princ_gens))
  for i = 1:length(units)
    to_be_eval[i] = units[i][1]
    to_be_eval_int[i] = units[i][2]
  end
  C = domain(ctx.mC)
  vect = ctx.vect
  n = fmpz(ctx.n)
  for i = 1:length(princ_gens)
    expokel = mod(C.snf[i]*vect[i], n)
    if iszero(expokel) || isone(Kel[i])
      to_be_eval[i+length(units)] = princ_gens[i][1]
      to_be_eval_int[i+length(units)] = princ_gens[i][2]
      continue
    end
    numkel = numerator(Kel[i])
    denkel = denominator(Kel[i])
    mul!(numkel, princ_gens[i][1].elem_in_nf, numkel^expokel)
    to_be_eval[i+length(units)] = O(numkel, false)
    to_be_eval_int[i+length(units)] = copy(princ_gens[i][2])
    if !isone(denkel)
      if haskey(to_be_eval_int[i+length(units)], denkel)
        to_be_eval_int[i+length(units)][denkel] = Int(mod(to_be_eval_int[i+length(units)][denkel]-expokel, n))
      else
        to_be_eval_int[i+length(units)][denkel] = Int(mod(-expokel, n))
        to_be_eval_int[i+length(units)] = coprime_base(to_be_eval_int[i+length(units)], n)
      end
    end
  end
  return to_be_eval, to_be_eval_int

end

function rayclassgrp_ctx(O::NfOrd, expo::Int)

  C1, mC1 = class_group(O)
  valclass = ppio(exponent(C1), fmpz(expo))[1]
  C, mC, vect = Hecke._class_group_mod_n(C1, mC1, Int(valclass))
  U, mU = unit_group_fac_elem(O)
  units_to_be_eval = FacElem{nf_elem, AnticNumberField}[mU(U[i]) for i = 1:ngens(U)]
  Hecke._assure_princ_gen(mC)
  princgens_to_be_eval = FacElem{nf_elem, AnticNumberField}[mC.princ_gens[i][2] for i = 1:length(mC.princ_gens)]
  preproc, ints1 = Hecke._new_preproc(units_to_be_eval, fmpz(expo))
  units = Vector{Tuple{NfOrdElem, Dict{fmpz, Int}}}(undef, length(preproc))
  for i = 1:length(units)
    el = evaluate(preproc[i])
    Qx = parent(parent(el).pol)
    elpol = Qx(el)
    c = content(elpol)
    el1 = el//c
    if haskey(ints1[i], numerator(c))
      ints1[i][numerator(c)] += 1
    else
      ints1[i][numerator(c)] = 1
    end
    if haskey(ints1[i], denominator(c))
      ints1[i][denominator(c)] -= 1
    else
      ints1[i][denominator(c)] = 1
    end
    units[i] = (O(el1), coprime_base(ints1[i], fmpz(expo)))
  end
  princ_gens = Vector{Tuple{NfOrdElem, Dict{fmpz, Int}}}(undef, ngens(C))
  if !iszero(ngens(C))
    preproc1, ints2 = Hecke._new_preproc(princgens_to_be_eval, fmpz(expo))
    for i = 1:length(princ_gens)
      el = evaluate(preproc1[i])
      Qx = parent(parent(el).pol)
      elpol = Qx(el)
      c = content(elpol)
      el1 = el//c
      if haskey(ints2[i], numerator(c))
        ints2[i][numerator(c)] += 1
      else
        ints2[i][numerator(c)] = 1
      end
      if haskey(ints2[i], denominator(c))
        ints2[i][denominator(c)] -= 1
      else
        ints2[i][denominator(c)] = -1
      end
      princ_gens[i] = (O(el1), coprime_base(ints2[i], fmpz(expo)))
    end
  end
  ctx = ctx_rayclassgrp()
  ctx.mC = mC
  ctx.n = expo
  ctx.vect = vect
  ctx.units = units
  ctx.princ_gens = princ_gens
  return ctx

end

###############################################################################
#
#  Ray Class Group: Fields function
#
###############################################################################

function _minimum(wprimes::Dict{NfOrdIdl, Int})
  mins = Dict{fmpz, Int}()
  for (P, v) in wprimes
    e = P.splitting_type[1]
    p = minimum(P)
    k, r = divrem(v, e)
    if !iszero(r)
      k += 1
    end
    if haskey(mins, p)
      mins[p] = max(mins[p], k)
    else
      mins[p] = k
    end
  end
  return prod(x^v for (x, v) in mins)
end

function ray_class_group_quo(O::NfOrd, m::Int, wprimes::Dict{NfOrdIdl,Int}, inf_plc::Array{InfPlc,1}, ctx::ctx_rayclassgrp; GRH::Bool = true)
  
  d1 = Dict{NfOrdIdl, Int}()
  lp = factor(m)
  I = ideal(O, 1)
  for q in keys(lp.fac)
    lq = prime_decomposition(O, q) 
    for (P, e) in lq
      I *= P
      d1[P] = 1
    end   
  end
  I.minimum = m
  if !isempty(wprimes)
    for (p, v) in wprimes
      I *= p^v
    end
    I.minimum = m*_minimum(wprimes)
  end
  
  return ray_class_group_quo(I, d1, wprimes, inf_plc, ctx, GRH = GRH)
  
end

function log_infinite_primes(O::NfOrd, p::Array{InfPlc,1})
    
  S = DiagonalGroup(Int[2 for i=1:length(p)])
  local log
  let S = S, p = p
    function log(B::T) where T <: Union{nf_elem ,FacElem{nf_elem, AnticNumberField}}
      emb = Hecke.signs(B, p)
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



function ray_class_group_quo(I::NfOrdIdl, y1::Dict{NfOrdIdl,Int}, y2::Dict{NfOrdIdl,Int}, inf_plc::Vector{InfPlc}, ctx::ctx_rayclassgrp; check::Bool = true, GRH::Bool = true)

  O = order(I)
  K = nf(O)
  #@assert (!(isempty(y1) && isempty(y2))) || isone(I)
  vect = ctx.vect
  n = ctx.n
  mC = ctx.mC
  lp = Dict{NfOrdIdl, Int}()
  for (p, v) in y1
    lp[p] = 1
  end
  for (p, v) in y2
    lp[p] = v
  end
  
  Q, pi = quo(O, I)
  Q.factor = lp
  C = domain(mC)
  @vtime :RayFacElem 1 G, mG, tame, wild = _mult_grp_mod_n(Q, y1, y2, n)
  if iszero(mod(n,2)) && !isempty(inf_plc)
    H, lH = Hecke.log_infinite_primes(O, inf_plc)
    T = G
    G = Hecke.direct_product(G, H, task = :none)
  end
  expo = exponent(G)
  
  if exponent(C)*expo < n && check
    return empty_ray_class(I)::Tuple{GrpAbFinGen, MapRayClassGrp}
  end
  
  C1, mC1 = class_group(O, GRH = GRH)::Tuple{GrpAbFinGen, MapClassGrp}
  valclass, nonnclass = ppio(exponent(C1), fmpz(n))
  U, mU = unit_group_fac_elem(O, GRH = GRH)

  exp_class, Kel = find_coprime_representatives(mC, I, lp)
  
  if order(G) == 1
    RR, mRR = class_as_ray_class(C, mC, exp_class, I, n) 
    mRR.clgrpmap = mC
    return RR, mRR 
  end
  
#
# We start to construct the relation matrix
#

  
  R = zero_matrix(FlintZZ, 2*ngens(C)+ngens(U)+2*ngens(G), ngens(C)+ngens(G))
  for i=1:ncols(R)
    R[ngens(C)+ngens(U)+ngens(G)+i, i] = n
  end
  for i = 1:ngens(C)
    R[i, i] = C.snf[i]
  end
  if issnf(G)
    for i=1:ngens(G)
      R[i+ngens(C), i+ngens(C)] = G.snf[i]
    end
  else
    for i=1:ngens(G)
      R[i+ngens(C), i+ngens(C)] = G.rels[i,i]
    end
  end
  
  #
  # We compute the relation matrix given by the image of the map U -> (O/m)^*
  #

  @hassert :RayFacElem 1 issnf(U)
  to_be_eval, to_be_eval_int = elems_to_be_eval(ctx, Kel)
  @vprint :RayFacElem 1 "Time for elements evaluation: "
  @vtime :RayFacElem 1 evals, quots, idemps = _crt_normalization(O, Q, to_be_eval, to_be_eval_int, lp)
  @vprint :RayFacElem 1 "\n"
  
  for i = 1:ngens(U)
    @vprint :RayFacElem 1 "Disclog of unit $i \n"
    a = preimage(mG, evals[i])::GrpAbFinGenElem
    for j = 1:ncols(a.coeff)
      R[i+ngens(G)+ngens(C), ngens(C)+j] = a[j]
    end
    if iszero(mod(n, 2)) && !isempty(inf_plc)
      if i==1
        for j = 1:length(inf_plc)
          R[i+ngens(G)+ngens(C), ngens(C)+ncols(a.coeff)+j] = 1
        end
      else
        b = lH(mU(U[i]))
        for j = 1:length(inf_plc)
          R[i+ngens(G)+ngens(C), ngens(C)+ncols(a.coeff)+j] = b[j]
        end
      end
    end
  end 

  # 
  # We compute the relation between generators of Cl and (O/m)^* in Cl^m
  #
  

  for i=1:ngens(C)
    @vprint :RayFacElem 1 "Disclog of class group element $i \n"
    invn = invmod(vect[i], expo)
    a = preimage(mG, evals[i+ngens(U)])::GrpAbFinGenElem
    for j = 1:ncols(a.coeff)
      R[i,ngens(C)+j] = -a[j]*invn
    end
    if mod(n, 2)==0 && !isempty(inf_plc)
      b = lH(mC.princ_gens[i][2]*(Kel[i]^(C.snf[i]*vect[i])))::GrpAbFinGenElem
      for j = 1:ncols(b.coeff)
        R[i, ngens(C)+ncols(a.coeff)+j] = -b[j]
      end
    end
  end
  
  X = AbelianGroup(R)

  disc_log_inf = Dict{InfPlc, GrpAbFinGenElem}()
  for i = 1:length(inf_plc)
    eldi = zeros(FlintZZ, ngens(X))
    eldi[ngens(X) - length(inf_plc) + i] = 1
    disc_log_inf[inf_plc[i]] = X(eldi)
  end
   
  #
  # Discrete logarithm
  #
  inverse_d = invmod(nonnclass, expo)
  
  local disclog
  let X = X, I = I, mG = mG, O = O, pi = pi, exp_class = exp_class, mC = mC, Q = Q, nonnclass = nonnclass, inverse_d = inverse_d, n = n, quots = quots, idemps = idemps, C = C, expo = expo
  function disclog(J::NfOrdIdl)
    
    res = zero_matrix(FlintZZ, 1, ngens(X))
    @hassert :RayFacElem 1 iscoprime(J, I)
    if J.is_principal==1
      if isdefined(J,:princ_gen)
        el = J.princ_gen
        y = preimage(mG, pi(el)).coeff
        for i = 1:ncols(y)
          res[1, ngens(C) + i] = y[1, i]
        end
        if iszero(mod(n, 2)) && !isempty(inf_plc)
          b = lH(K(el))
          for i = 1:length(inf_plc)
            res[1, ngens(C)+ncols(y)+i] = b[i]
          end
        end
      elseif isdefined(J,:princ_gen_special)
        el1 = O(J.princ_gen_special[2])+O(J.princ_gen_special[3])
        YY = preimage(mG, pi(el1)).coeff
        for i = 1:ncols(YY)
          res[1, i+ngens(C)] = YY[1, i]
        end
        if iszero(mod(n,2)) && !isempty(pr)
          b = lH(K(el)).coeff
          for i = 1:ncols(b)
            res[1, i+ngens(C)+ncols(YY)] = b[1, i]
          end
        end
      else
        z = principal_gen_fac_elem(J)
        el = _fac_elem_evaluation(O, Q, quots, idemps, z, gcd(expo,n))
        y = (mG\(pi(el))).coeff
        for i = 1:ncols(y)
          res[1, i+ngens(C)] = y[1, i]
        end
        if mod(n,2)==0 && !isempty(inf_plc)
          b=lH(z).coeff
          for i = 1:ncols(b)
            res[1, i+ngens(C)+ncols(y)] = b[1, i]
          end
        end
      end 
    else      
      W = mC\J
      for i = 1:ngens(C)
        res[1, i] = W[i]
      end
      s = exp_class(W)
      pow!(s, -nonnclass)
      if haskey(s.fac, J)
        s.fac[J] += nonnclass
      else
        s.fac[J] = nonnclass
      end
      z = principal_gen_fac_elem(s)
      el = _fac_elem_evaluation(O, Q, quots, idemps, z, gcd(expo,n))
      y=(mG\(pi(el))).coeff
      for i = 1:ncols(y)
        res[1, i+ngens(C)] = y[1, i]*inverse_d
      end
      if mod(n,2)==0 && !isempty(inf_plc)
        b = lH(z).coeff
        for i = 1:ncols(b)
          res[1, i+ngens(C)+ncols(y)] = b[1, i]
        end
      end
    end    
    return GrpAbFinGenElem(X, res)
  end 
  end
  
  for (prim, mprim) in tame
    dis = zero_matrix(FlintZZ, 1, ngens(X))
    to_be_c = mprim.disc_log.coeff
    for i = 1:length(to_be_c)
      dis[1, i+ngens(C)] = to_be_c[1, i]
    end
    mprim.disc_log = X(dis)
  end

  mp = Hecke.MapRayClassGrp()
  mp.header = Hecke.MapHeader(X, FacElemMon(parent(I)))
  mp.header.preimage = disclog
  mp.modulus_fin = I
  mp.modulus_inf = inf_plc
  mp.quots_nquo = quots
  mp.idemps = idemps
  mp.coprime_elems = Kel
  mp.fact_mod = lp
  mp.tame_mult_grp = tame
  mp.wild_mult_grp = wild
  mp.defining_modulus = (I, inf_plc)
  mp.disc_log_inf_plc = disc_log_inf
  mp.clgrpmap = mC
  return X::GrpAbFinGen, mp
  
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
    # I check that the action on the P-sylow is the identity.
    for i = 1:ngens(G)
      if !divisible(G.snf[i], P)
        continue
      end
      pp, q = ppio(G.snf[i], P)
      new_prime = false
      for j = 1:length(res_act)
        if res_act[j](q*G[i]) != q*G[i]
          new_prime = true
          break
        end
      end
      if new_prime
        break
      end
    end
    if !new_prime
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

  #First, a suitable modulus for A over k
  #I take the discriminant K/k times the norm of the conductor A/K
  
  fac1 = factor(d)
  fm0 = Dict{NfOrdIdl, Int}()
  for (p, v) in fac1
    lPp = prime_decomposition(zk, p)
    if divisible(fmpz(expected_order), p)
      theoretical_bound = _bound_exp_conductor_wild(zk, expG, Int(p), d)
      for i = 1:length(lPp)
        fm0[lPp[i][1]] = min(theoretical_bound, Int(v))
      end
    else
      for i = 1:length(lPp)
        fm0[lPp[i][1]] = 1
      end
    end
  end
  #Now, I want to compute f_m0 = merge(max, norm(mR1.fact_mod), fac2)
  primes_done = fmpz[]
  for (P, e) in mR1.fact_mod
    p = minimum(P)
    if p in primes_done
      continue
    else
      push!(primes_done, p)
    end
    lp = prime_decomposition(zk, p)
    if !divisible(fmpz(expected_order * expo), p)
      for i = 1:length(lp)
        fm0[lp[i][1]] = 1
      end
    else
      #I need the relative norm of P expressed as a prime power.
      pm = Hecke.intersect_prime(mp, P)
      fpm = divexact(P.splitting_type[2], pm.splitting_type[2])
      theoretical_bound1 = _bound_exp_conductor_wild(zk, lcm(expo, expG), Int(p), d*norm(defining_modulus(A)[1]))
      for i = 1:length(lp)
        if haskey(fm0, lp[i][1])
          fm0[lp[i][1]] =  min(fm0[lp[i][1]] * fpm * e, theoretical_bound1)
        else
          fm0[lp[i][1]] = min(fpm * e, theoretical_bound1)
        end
      end
    end
  end
  # Now, I extend the modulus to K
  fM0 = Dict{NfOrdIdl, Int}()
  primes_done = fmpz[]
  for (P, e) in fm0
    p = Hecke.minimum(P)
    if p in primes_done
      continue
    else
      push!(primes_done, p)
    end
    
    lp = prime_decomposition(ZK, p)
    multip = divexact(lp[1][2], P.splitting_type[1])
    if !divisible(fmpz(expected_order * expo), p)
      for i = 1:length(lp)
        fM0[lp[i][1]] = 1
      end
    else
      if isdefined(A, :abs_disc) 
        d = A.abs_disc
        ev = prod(w^z for (w,z) in d)
        ev = divexact(ev, discriminant(ZK))
        theoretical_bound2 = _bound_exp_conductor_wild(ZK, expo, Int(p), ppio(ev, p)[1])
        for i = 1:length(lp)
          fM0[lp[i][1]] = min(multip * e, theoretical_bound2)
        end
      else
        for i = 1:length(lp)
          fM0[lp[i][1]] = multip * e
        end
      end
    end 
  end
  ind = 0
  #@vtime :MaxAbExt 1 
  if isdefined(ctx, :computed)
    flinf = isempty(mR1.modulus_inf)
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
    R, mR = Hecke.ray_class_group_quo(ZK, fM0, mR1.modulus_inf, ctx, check = false)
    if isdefined(ctx, :computed)
      push!(ctx.computed, (fM0, isempty(mR1.modulus_inf), mR))
    else
      ctx.computed = [(fM0, isempty(mR1.modulus_inf), mR)]
    end
  else
    mR = ctx.computed[ind][3]
    R = domain(mR)
  end
  if degree(zk) != 1
    if istotally_real(K) && isempty(mR1.modulus_inf)
      inf_plc = InfPlc[]
    else
      inf_plc = real_places(k)
    end
    #@vtime :MaxAbExt 1 
    r, mr = Hecke.ray_class_group_quo(zk, ctx.n, fm0, inf_plc)
  else
    rel_plc = true
    if istotally_real(K) && isempty(mR1.modulus_inf)
      rel_plc = false
    end
    modulo = minimumd(fm0, expo * expected_order)
    #@vtime :MaxAbExt 1 
    r, mr = Hecke.ray_class_groupQQ(zk, modulo, rel_plc, ctx.n)
  end
  #@vtime :MaxAbExt 1 
  lP, gS = Hecke.find_gens(mR, coprime_to = minimum(mR1.modulus_fin))
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


