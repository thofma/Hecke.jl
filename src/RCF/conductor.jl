export conductor, is_conductor, norm_group, maximal_abelian_subfield, genus_field, content_ideal, subfields, is_normal, is_central, normal_closure

########################################################################################
#
#  Tools for conductor
#
########################################################################################

function _norm_group_gens_small(C::ClassField)

  mp=C.mq

  mR = C.rayclassgroupmap
  mS = C.quotientmap

  R=domain(mR)
  cond, inf_plc1 = defining_modulus(mR)
  O = order(cond)
  E=order(domain(mp))
  expo=Int(exponent(domain(mp)))
  K=O.nf

  mS=pseudo_inv(mS)
  dom=domain(mS)
  M=zero_matrix(FlintZZ,ngens(dom), ngens(codomain(mS)))
  for i=1:ngens(dom)
    elem=mS(dom[i]).coeff
    for j=1:ngens(codomain(mS))
      M[i,j]=elem[1,j]
    end
  end
  S1=Hecke.GrpAbFinGenMap(domain(mS),codomain(mS),M)
  T,mT=Hecke.kernel(S1)

  Sgens=find_gens_sub(mR,mT)

  return Sgens

end

#
#  Find small primes generating a subgroup of the ray class group
#

function find_gens_sub(mR::MapRayClassGrp, mT::GrpAbFinGenMap)

  O = order(codomain(mR))
  R = domain(mR)
  T = domain(mT)
  m = Hecke._modulus(mR)
  l = minimum(m)
  lp = NfOrdIdl[]
  sR = GrpAbFinGenElem[]

  if isdefined(mR, :prime_ideal_cache)
    S = mR.prime_ideal_cache
  else
    S = prime_ideals_up_to(O, 1000)
    mR.prime_ideal_cache = S
  end
  q, mq = quo(T, sR, false)
  for (i,P) in enumerate(S)
    if divisible(l,P.minimum)
      continue
    end
    if haskey(mR.prime_ideal_preimage_cache, P)
      f = mR.prime_ideal_preimage_cache[P]
    else
      f = mR\P
      mR.prime_ideal_preimage_cache[P] = f
    end
    bool, pre = haspreimage(mT, f)
    if !bool
      continue
    end
    if iszero(mq(pre))
      continue
    end
    push!(sR, pre)
    push!(lp, P)
    q, mq = quo(T, sR, false)
    if order(q) == 1
      break
    end
  end
  if order(q) == 1
    return lp
  else
    error("Not enough primes")
  end
end

#
#  This functions constructs generators for 1+p^u/1+p^u+1
#

function _1pluspk_1pluspk1(K::AnticNumberField, p::NfOrdIdl, pk::NfOrdIdl, pv::NfOrdIdl, powers::Vector{Tuple{NfOrdIdl, NfOrdIdl}}, a::Union{Int, fmpz}, n::Int)

  O = maximal_order(K)
  b = basis(pk, copy = false)
  N = basis_matrix(pv, copy = false)*basis_mat_inv(pk, copy = false)
  G = abelian_group(N.num)
  S, mS = snf(G)
  #Generators
  gens = Vector{NfOrdElem}(undef, ngens(S))
  for i=1:ngens(S)
    gens[i] = one(O)
    for j = 1:ngens(G)
      mult = mod(mS.map[i,j], S.snf[end])
      if !iszero(mult)
        add!(gens[i], gens[i], mult*b[j])
      end
    end
  end
  if length(powers) > 1
    i = findfirst(x -> x[1] == p, powers)
    q = powers[i][2]
    i_without_p = prod([powers[j][2] for j = 1:length(powers) if j != i])
    alpha, beta = idempotents(q, i_without_p)
    for i in 1:length(gens)
      mul!(gens[i], gens[i], beta)
      add!(gens[i], gens[i], alpha)
    end
  end
  if mod(n,2)==0
    for i=1:length(gens)
      gens[i] = make_positive(gens[i], fmpz(a))
    end
  end
  return gens
end


#######################################################################################
#
#  Signature
#
#######################################################################################

@doc Markdown.doc"""
    signature(C::ClassField) -> Int, Int

Return the signature of the number field defined by $C$.
"""
function signature(C::ClassField)
  mR = C.rayclassgroupmap
  mS = C.quotientmap
  inf_plc = defining_modulus(mR)[2]
  K = base_field(C)
  rK, sK = signature(K)
  if isempty(inf_plc)
    r = degree(C)*rK
    s = div(degree(K)*degree(C) - r, 2)
    return r, s
  end
  if degree(K) == 1
    OK = base_ring(C)
    el = mR\(ideal(OK, 1-minimum(defining_modulus(mR)[1])))
    if iszero(mS(el))
      return degree(C), 0
    else
      return 0, div(degree(C), 2)
    end
  end
  D = mR.disc_log_inf_plc
  r = rK - length(D)
  for (P, el) in D
    if iszero(mS(el))
      r += 1
    end
  end
  r *= degree(C)
  s = div(degree(K)*degree(C) - r, 2)
  return r, s
end

function signature(C::ClassField{MapClassGrp, GrpAbFinGenMap})
  K = base_field(C)
  rK, sK = signature(K)
  r = degree(C)*rK
  s = div(degree(K)*degree(C) - r, 2)
  return r, s
end



#######################################################################################
#
#  Conductor functions
#
#######################################################################################

@doc Markdown.doc"""
    conductor(C::ClassField) -> NfOrdIdl, Vector{InfPlc}

Return the conductor of the abelian extension corresponding to $C$.
"""
function conductor(C::T) where T <:Union{ClassField, ClassField_pp}

  if isdefined(C,:conductor)
    return C.conductor
  end
  mR = C.rayclassgroupmap
  mS = C.quotientmap
  mp = pseudo_inv(mS)* mR
  G = domain(mp)
  #
  #  First, we need to find the subgroup
  #

  cond, inf_plc = defining_modulus(C)
  O = order(cond)
  if isone(cond) && isempty(inf_plc)
    return ideal(O,1), InfPlc[]
  end
  E = order(G)
  expo = Int(exponent(G))
  K = O.nf

  #
  #  Some of the factors of the modulus are unnecessary for order reasons:
  #
  L = Dict{NfOrdIdl, Int}()
  for (p, vp) in mR.fact_mod
    if !divisible(E, minimum(p, copy = false))
      if !is_coprime(E, norm(p)-1)
        L[p] = 1
      end
    else
      if !isone(vp)
        L[p] = vp
      end
    end
  end

  #Finite part of the modulus
  mult_grps = mR.groups_and_maps
  powers = mR.powers
  for i = 1:length(mult_grps)
    mG = mult_grps[i][2]
    p = powers[i][1]
    if !haskey(L, p)
      continue
    end
    v = L[p]
    if isone(v)
      tmg = mG.tame[p]
      if iszero(mS(tmg.disc_log))
        Base.delete!(L, p)
      end
    else
      k1 = v-1
      k2 = v
      gens = GrpAbFinGenElem[]
      Q = abelian_group(Int[])
      while k1 >= 1
        multg = _1pluspk_1pluspk1(K, p, p^k1, p^k2, powers, minimum(cond), expo)
        for i = 1:length(multg)
          push!(gens, preimage(mp, ideal(O, multg[i])))
        end
        Q, mQ = quo(G,gens,false)
        if order(Q) != E
          L[p] = k2
          break
        end
        k1 -= 1
        k2 -= 1
      end
      if k2 == 1 && order(Q) == E
        tmgD = mG.tame
        if haskey(tmgD, p)
          push!(gens, mS(tmgD[p].disc_log))
          Q,mQ = quo(G, gens, false)
          if order(Q) == E
            delete!(L, p)
          else
            L[p] = 1
          end
        else
          delete!(L,p)
        end
      end
    end
  end
  cond = ideal(O,1)
  C.factored_conductor = L
  for (p,vp) in L
    cond *= p^vp
  end

  #Infinite part of the modulus
  cond_inf = InfPlc[]
  if !isempty(inf_plc)
    D = mR.disc_log_inf_plc
    for (Pl, el) in D
      if !iszero(mS(el))
        push!(cond_inf, Pl)
      end
    end
  end

  return cond, cond_inf

end

###############################################################################
#
#  is_conductor function
#
###############################################################################

@doc Markdown.doc"""
    is_conductor(C::Hecke.ClassField, m::NfOrdIdl, inf_plc::Vector{InfPlc}=InfPlc[]; check) -> NfOrdIdl, Vector{InfPlc}

Checks if (m, inf_plc) is the conductor of the abelian extension corresponding to $C$. If `check` is `false`, it assumes that the
given modulus is a multiple of the conductor.
This is usually faster than computing the conductor.
"""
function is_conductor(C::Hecke.ClassField, m::NfOrdIdl, inf_plc::Vector{InfPlc} = InfPlc[]; check::Bool=true)
  if isdefined(C, :conductor)
    real_cond = C.conductor
    return real_cond[1] == m && Set(real_cond[2]) == Set(inf_plc)
  end
  mR = C.rayclassgroupmap
  mS = C.quotientmap
  G = codomain(mS)
  mp = pseudo_inv(mS) * mR

  R = domain(mR)
  cond, inf_plc2 = defining_modulus(mR)
  O = order(cond)
  E = order(G)
  expo = Int(exponent(G))
  K = O.nf

  if check
    mS1 = pseudo_inv(mS)
    dom = domain(mS1)
    M = zero_matrix(FlintZZ,ngens(dom), ngens(codomain(mS1)))
    for i = 1:ngens(dom)
      elem = mS1(dom[i]).coeff
      for j = 1:ngens(codomain(mS1))
        M[i, j] = elem[1,j]
      end
    end
    S1=Hecke.GrpAbFinGenMap(domain(mS1), codomain(mS1), M)
    T,mT = Hecke.kernel(S1)

    Sgens = find_gens_sub(mR, mT)

    r,mr = ray_class_group(m, inf_plc, n_quo = expo)
    quot = GrpAbFinGenElem[mr\s for s in Sgens]
    s,ms = quo(r, quot, false)
    if order(s) != E
      return false
    end
  end

  #  Some of the factors of the modulus are unnecessary for order reasons:
  L = factor(m)
  for (p,vp) in L
    if !haskey(mR.fact_mod, p) || vp>mR.fact_mod[p]
      return false
    end
    if !divisible(E,minimum(p))
      if gcd(E, norm(p)-1)==1
        return false
      elseif vp>1
        return false
      end
    elseif vp==1
      return false
    end
  end

  #Infinite part of the modulus
  if isodd(E) && !isempty(inf_plc)
    return false
  end
  for pl in inf_plc
    if !(pl in inf_plc2)
      return false
    end
  end

  if !isempty(inf_plc2)
    D = mR.disc_log_inf_plc
    for (Pl, el) in D
      Q, mQ = quo(G, mS(el), false)
      if order(Q) == E
        return false
      end
    end
  end

  #Finite part of the modulus
  powers = mR.powers
  g_and_maps = mR.groups_and_maps
  fact_def_mod = mR.fact_mod
  for i = 1:length(powers)
    P = powers[i][1]
    if !haskey(L, P) || fact_def_mod[P] < L[P]
      return false
    end
    v = L[P]
    if v == 1
      mG = g_and_maps[i][2]
      tmg = mG.tame[P]
      Q, mQ = quo(G, [mS(tmg.disc_log)], false)
      if order(Q) == E
        return false
      end
    else
      multg = _1pluspk_1pluspk1(K, P, P^(v-1), P^v, powers, cond.gen_one, expo)
      gens = Vector{GrpAbFinGenElem}(undef, length(multg))
      for i = 1:length(multg)
        gens[i] = preimage(mp, ideal(O, multg[i]))
      end
      Q,mQ = quo(G, gens, false)
      if order(Q) == E
        return false
      end
    end
  end
  C.conductor = (m, inf_plc)
  return true
end

####################################################################################
#
#  Discriminant function
#
####################################################################################

function discriminant_sign(C::ClassField)
# Compute the sign using Brill's theorem
  _, s = signature(C)
  if mod(s, 2) == 0
    return 1
  else
    return -1
  end
end

function absolute_discriminant(C::ClassField)
  OK = base_ring(C)
  return discriminant_sign(C) * norm(discriminant(C))*discriminant(OK)^degree(C)
end

function discriminant(C::ClassField, ::FlintRationalField)
  return absolute_discriminant(C)
end

@doc Markdown.doc"""
    discriminant(C::ClassField) -> NfOrdIdl

Using the conductor-discriminant formula, compute the (relative) discriminant of $C$.
This does not use the defining equations.
"""
function discriminant(C::ClassField)
  if isdefined(C,:conductor)
    m = C.conductor[1]
    inf_plc = C.conductor[2]
  else
    C.conductor = conductor(C)
    m = C.conductor[1]
    inf_plc = C.conductor[2]
  end
  O = order(m)
  if isdefined(C, :relative_discriminant)
    if isempty(C.relative_discriminant)
      return ideal(O, 1)
    else
      return prod([P^v for (P, v) in C.relative_discriminant])
    end
  end


  @assert typeof(m) == NfOrdIdl

  mR = C.rayclassgroupmap
  mS = C.quotientmap
  mp = pseudo_inv(mS) * mR
  R = domain(mp)
  n = order(R)
  relative_disc = Dict{NfOrdIdl,Int}()
  lp = factor(m)

  if is_prime(n)
    for (p, v) in lp
      ap = n*v - v
      relative_disc[p] = ap
      continue
    end
    C.relative_discriminant = relative_disc
    if isempty(C.relative_discriminant)
      return ideal(O, 1)
    else
      return prod([P^v for (P, v) in C.relative_discriminant])
    end
  end



  expo = Int(exponent(R))
  K = O.nf
  a = minimum(m)
  g_and_maps = mR.groups_and_maps
  powers = mR.powers
  for i = 1:length(powers)
    p = powers[i][1]
    if !haskey(lp, p)
      continue
    end
    v = lp[p]
    mG = g_and_maps[i][2]
    if isone(v)
      tmg = mG.tame[p]
      el = mS(tmg.disc_log)
      Q, mQ = quo(R, GrpAbFinGenElem[el], false)
      relative_disc[p] = n - order(Q)
      continue
    end
    s = v
    ap = v*degree(C)
    @hassert :AbExt 1 s>=2
    els = GrpAbFinGenElem[]
    for k = 2:v
      s = s-1
      pk = p^s
      pv = pk*p
      gens = _1pluspk_1pluspk1(K, p, pk, pv, powers, a, expo)
      for i=1:length(gens)
        push!(els, mp\ideal(O, gens[i]))
      end
      ap -= Int(order(quo(R, els, false)[1]))
      @hassert :AbExt 1 ap>0
    end
    if haskey(mG.tame, p)
      push!(els, mS(mG.tame[p].disc_log[1]))
    end
    ap -= Int(order(quo(R, els, false)[1]))
    @hassert :AbExt 1 ap>0
    relative_disc[p] = ap
  end
  C.relative_discriminant = relative_disc
  if isempty(relative_disc)
    return ideal(O, 1)
  else
    return prod([P^v for (P, v) in relative_disc])
  end
end

##############################################################################
#
#  Is Abelian function
#
##############################################################################

function is_abelian(K::NfRel)
  k = base_field(K)
  Ok = maximal_order(k)
  d = ideal(Ok, Ok(discriminant(K.pol)))
  r, mr = ray_class_group(d, real_places(k), n_quo = degree(K))
  s, ms = norm_group(K.pol, mr, false)
  deg = divexact(order(r), order(s))
  return deg == degree(K)
end

function is_abelian(K::NfRelNS)
  k = base_field(K)
  kx, _ = PolynomialRing(k, "x", cached = false)
  Ok = maximal_order(k)
  pols = [to_univariate(kx, x) for x in K.pol]
  d = ideal(Ok, Ok(discriminant(pols[1])))
  for i = 2:length(pols)
    d = lcm(d, ideal(Ok, Ok(discriminant(pols[i]))))
  end
  r, mr = ray_class_group(d, real_places(k), n_quo = degree(K))
  s, ms = norm_group(pols, mr, false, cached = false)
  deg = divexact(order(r), order(s))
  return deg == degree(K)
end

function is_abelian(K::AnticNumberField)
  c = get_attribute(K, :is_abelian)
  if c !== nothing
    return c
  end
  if !is_normal_easy(K)
    return false
  end
  if is_maximal_order_known(K)
    d1 = discriminant(maximal_order(K))
  else
    d = discriminant(K)
    den = denominator(d)
    if !isone(den)
      d *= den^degree(K)
    end
    d1 = numerator(d)
  end
  KQ = rationals_as_number_field()[1]
  ZKQ = maximal_order(KQ)
  r, mr = ray_class_group(ideal(ZKQ, d1), real_places(KQ), n_quo = degree(K))
  s, ms = norm_group(map_coefficients(KQ, K.pol), mr, false, cached = false)
  deg = divexact(order(r), order(s))
  if deg == degree(K)
    set_attribute!(K, :is_abelian => true)
    return true
  else
    set_attribute!(K, :is_abelian => false)
    return false
  end
end

################################################################################
#
#  Norm group function
#
################################################################################

@doc Markdown.doc"""
    norm_group(K::NfRel{nf_elem}, mR::Hecke.MapRayClassGrp) -> Hecke.FinGenGrpAb, Hecke.FinGenGrpAbMap

    norm_group(K::NfRelNS{nf_elem}, mR::Hecke.MapRayClassGrp) -> Hecke.FinGenGrpAb, Hecke.FinGenGrpAbMap

Computes the subgroup of the Ray Class Group $R$ given by the norm of the extension.
"""
function norm_group(K::NfRel{nf_elem}, mR::T, is_abelian::Bool = true; of_closure::Bool = false) where T <: Union{MapClassGrp, MapRayClassGrp}
  base_field(K) == nf(order(codomain(mR))) || error("field has to be over the same field as the ray class group")
  return norm_group(K.pol, mR, is_abelian, of_closure = of_closure)
end
function norm_group(K::NfRelNS{nf_elem}, mR::T, is_abelian::Bool = true; of_closure::Bool = false) where T <: Union{MapClassGrp, MapRayClassGrp}
  base_field(K) == nf(order(codomain(mR))) || error("field has to be over the same field as the ray class group")
  kx, = PolynomialRing(base_field(K), "x", cached = false)
  return norm_group([to_univariate(kx, x) for x = K.pol], mR, is_abelian, of_closure = of_closure)
end

@doc Markdown.doc"""
    norm_group(f::Nemo.PolyElem, mR::Hecke.MapRayClassGrp, is_abelian::Bool = true; of_closure::Bool = false) -> Hecke.FinGenGrpAb, Hecke.FinGenGrpAbMap

    norm_group(f::Array{PolyElem{nf_elem}}, mR::Hecke.MapRayClassGrp, is_abelian::Bool = true; of_closure::Bool = false) -> Hecke.FinGenGrpAb, Hecke.FinGenGrpAbMap

Computes the subgroup of the Ray Class Group $R$ given by the norm of the extension generated by a/the roots of $f$. If `is_abelian` is set to true, then the code assumes the field to be
abelian, hence the algorithm stops when the quotient by the norm group has the correct order.
Even though the algorithm is probabilistic by nature, in this case the result is guaranteed.
If `of_closure` is given, then the norm group of the splitting field of the polynomial(s)
is computed.
It is the callers responsibility to ensure that the ray class group passed in is large enough.
"""
function norm_group(f::Nemo.PolyElem, mR::T, is_abelian::Bool = true; of_closure::Bool = false, cached::Bool = true, check::Bool = false)  where T <: Union{MapClassGrp, MapRayClassGrp}
  return norm_group(typeof(f)[f], mR, is_abelian, of_closure = of_closure, cached = cached, check = check)
end

function norm_group(l_pols::Vector{T}, mR::U, is_abelian::Bool = true; of_closure::Bool = false, cached::Bool = true, check::Bool = false) where {T <: PolyElem{nf_elem}, U <: Union{MapClassGrp, MapRayClassGrp}}

  R = domain(mR)
  O = order(codomain(mR))
  K = nf(O)
  @assert all(x->base_ring(x) == K, l_pols) "Polynomials must be over the same field"
  if check
    @assert all(x -> is_irreducible(x), l_pols) "Input polynomials must be irreducible"
  end
  N1 = minimum(defining_modulus(mR)[1])
  #I don't want to compute the discriminant of the polynomials.
  #The degree might be large and so difficult to compute.
  #Thus I will check for every prime if the projection has discriminant 0

  n = lcm(Int[degree(x) for x = l_pols])
  if of_closure
    #we cannot work in the quotient, it "could" be lcm(factorial(degree(x)) for x = f)
    Q, mQ = quo(R, GrpAbFinGenElem[])
  else
    Q, mQ = quo(R, n, false)
  end

  p = maximum(degree(x)+1 for x = l_pols)

  listprimes = GrpAbFinGenElem[]

  # Adding small primes until it stabilizes
  B = prod(Int[degree(x) for x in l_pols])
  max_stable = 50*n
  stable = max_stable
  denom = lcm([denominator(coeff(x, i)) for x in l_pols for i = 0:degree(x)])
  indexO = index(O)
  while true
    @vprint :ClassField 3 "Order of Q: $(order(Q))\n"
    if is_abelian && order(Q) == B
      break
    end
    if !is_abelian && order(Q) <= B && stable <= 0
      break
    end
    p = next_prime(p)
    @vprint :ClassField 3 "Using prime $(p)\n"
    if divisible(N1, p) || divisible(denom, p)
      continue
    end
    if divides(indexO, fmpz(p))[1]
      continue
    end
    found = false
    L = prime_decomposition(O, p, 1)
    for i = 1:length(L)
      candidate = mR\L[i][1]
      if iszero(mQ(candidate))
        continue
      end
      F, mF = ResidueFieldSmallDegree1(O, L[i][1])
      mFp = extend_easy(mF, K)
      all_deg = Vector{Int}[]
      #=
        the idea, taking 2 polys:
          f splits in d_i
          g splits in e_i
        Then, over an extensions of degree d_i an irreducible of degree e_i
        splits into factors of degree e_i/gcd(d_i, e_i) so there are gcd() many
        (but this is not used). The total degree over base field is then
        d_i * e_i/gcd() = lcm(d_i, e_i)
        This can be iterated...
              =#
      fl = true
      for x = l_pols
        g = map_coefficients(mFp, x)
        if degree(g) != degree(x) || iszero(discriminant(g))
          fl = false
          break
        end
        D = factor_distinct_deg(g)
        push!(all_deg, Int[x[1] for x in D])
      end
      if !fl
        continue
      end
      if !of_closure
        all_f = Set{Int}()
        for d = Iterators.product(all_deg...)
          push!(all_f, lcm(collect(d)))
        end
        else
        all_f = Set(lcm([x for x = all_f]))
      end
      E = gcd(collect(all_f))
      candidate = E*candidate
      if !iszero(mQ(candidate))
        push!(listprimes, candidate)
        Q, mQ = quo(R, listprimes, false)
        found = true
        stable = max_stable
      end
    end
    if !found
      stable -= 1
    end
  end

  if !of_closure
    for i=1:ngens(R)
       push!(listprimes, n*R[i])
    end
  end
  return sub(R, listprimes, cached)
end


function defining_modulus(mC::MapClassGrp)
  OK = order(codomain(mC))
  I = ideal(OK, 1)
  lp = Vector{InfPlc}()
  return I, lp
end

function norm_group(mL::NfToNfMor, mR::Union{MapRayClassGrp, MapClassGrp}, expected_index::Int = 1)

  K = domain(mL)
  L = codomain(mL)
  R = domain(mR)
  O = order(codomain(mR))
  @assert nf(O) == K
  if is_coprime(exponent(R), divexact(degree(L), degree(K)))
    return sub(R, gens(R), true)
  end

  N = minimum(defining_modulus(mR)[1])

  els = GrpAbFinGenElem[]

  #  Adding small primes until it stabilizes
  n = divexact(degree(L), degree(K))
  max_stable = 20*n
  GRH_bound = (4*log(abs(discriminant(maximal_order(L)))) + 2.5*expected_index + 5)^2
  stable = max_stable
  p = 0
  Q, mQ = quo(R, els, false)
  while true
    if order(Q) == expected_index || (order(Q) <= n && stable <= 0)
      break
    end
    p = next_prime(p)
    if p > GRH_bound
      break
    end
    if !is_coprime(N, p)
      continue
    end
    found = false
    lP = prime_decomposition(O, p)
    for (P, e) in lP
      lQ = prime_decomposition_type(mL, P)
      s = gcd(Int[x[1] for x in lQ])
      candidate = s*(mR\P)
      if !iszero(mQ(candidate))
        push!(els, candidate)
        Q, mQ = quo(R, els, false)
        stable = max_stable
        found = true
      end
    end
    if !found
      stable -= 1
    end
  end
  return sub(R, els, !false)
end

function norm_group(KK::KummerExt, mp::NfToNfMor, mR::Union{MapRayClassGrp, MapClassGrp})
  k = domain(mp)
  K = codomain(mp)
  ZK = maximal_order(K)
  zk = order(codomain(mR))
  # disc(ZK/Q) = N(disc(ZK/zk)) * disc(zk)^deg
  # we need the disc ZK/k, well a conductor.


  n = degree(KK)
  els = GrpAbFinGenElem[]
  stable = 0
  max_stable = 15*n*degree(k)
  R = domain(mR)
  expo = exponent(R)
  Q, mQ = quo(R, els, false)
  modu = lcm(minimum(defining_modulus(mR)[1]), index(ZK))
  prev = length(els)
  #S = PrimesSet(minimum(defining_modulus(mR)[1]), fmpz(-1), minimum(defining_modulus(mR)[1]), fmpz(1))
  S = PrimesSet(200, -1, exponent(KK), 1)
  for p in S
    if !is_coprime(p, modu)
      continue
    end
    lp = prime_decomposition(zk, p, 1)
    if isempty(lp)
      continue
    end
    D = Vector{Vector{gfp_poly}}(undef, length(KK.gen))
    for i = 1:length(D)
      D[i] = Vector{gfp_poly}(undef, length(KK.gen[i].fac))
    end
    first = false
    for i = 1:length(lp)
      P = lp[i][1]
      if iszero(mR\P)
        continue
      end
      lP = prime_decomposition(mp, P)
      local z::GrpAbFinGenElem
      try
        z = _canonical_frobenius_with_cache(lP[1][1], KK, first, D)
        @hassert :ClassField 1 z == canonical_frobenius(lP[1][1], KK)
        first = true
      catch e
        if !isa(e, BadPrime)
          rethrow(e)
        end
        continue
      end
      f = order(z)*divexact(degree(lP[1][1]), degree(P))
      if divisible(f, expo)
        stable += 1
        continue
      end
      el = f*(mR\P)
      if !iszero(mQ(el))
        push!(els, el)
        Q, mQ = quo(R, els, false)
      else
        stable += 1
      end
    end
    if stable >= max_stable
      break
    end
  end
  return sub(R, els, false)
end


@doc Markdown.doc"""
    maximal_abelian_subfield(::Type{ClassField}, K::AnticNumberField) -> ClassField

The maximal abelian subfield of $K$ as a class field, i.e. the norm group
is computed and the corresponding `ray_class_field` created.
"""
function maximal_abelian_subfield(::Type{ClassField}, K::AnticNumberField)
  Zx, x = PolynomialRing(FlintZZ, cached = false)
  QQ = rationals_as_number_field()[1]
  R, mR = ray_class_group(discriminant(maximal_order(K))*maximal_order(QQ), infinite_places(QQ), n_quo = degree(K))
  f = hom(QQ, K, K(1), check = false)
  N, mN = norm_group(f, mR)
  return ray_class_field(mR, quo(R, N)[2])
end


function norm_group_map(R::ClassField{S, T}, r::Vector{<:ClassField}, map = false) where {S, T}
  @assert map != false || all(x -> base_ring(R) == base_ring(x), r)
#  @assert map == false && all(x -> base_ring(R) == base_ring(x), r)

  mR = defining_modulus(R)[1]
  @assert map != false || all(x->mR+defining_modulus(x)[1] == defining_modulus(x)[1], r)

  fR = compose(pseudo_inv(R.quotientmap), R.rayclassgroupmap)
 
  if degree(R) == 1
    @assert all(x->degree(x) == 1, r)
    return [hom(domain(fR), domain(x.quotientmap), GrpAbFinGenElem[]) for x = r]
  end

  lp, sR = find_gens(MapFromFunc(x->preimage(fR, x), IdealSet(base_ring(R)), domain(fR)),
                             PrimesSet(100, -1), minimum(mR))
  if map == false
    h = [hom(sR, GrpAbFinGenElem[preimage(compose(pseudo_inv(x.quotientmap), x.rayclassgroupmap), p) for p = lp]) for x = r]
  else
    h = [hom(sR, GrpAbFinGenElem[preimage(compose(pseudo_inv(x.quotientmap), x.rayclassgroupmap), map(p)) for p = lp]) for x = r]
  end
  return h
end

function norm_group_map(R::ClassField, r::ClassField, map = false)
  return norm_group_map(R, [r], map)[1]
end

@doc Markdown.doc"""
    maximal_abelian_subfield(K::NfRel{nf_elem}; of_closure::Bool = false) -> ClassField

Using a probabilistic algorithm for the norm group computation, determine the maximal
abelian subfield in $K$ over its base field. If `of_closure` is set to true, then
the algorithm is applied to the normal closure of $K$ (without computing it).
"""
function maximal_abelian_subfield(K::NfRel{nf_elem}; of_closure::Bool = false)
  zk = maximal_order(base_field(K))
  if has_attribute(K, :maximal_order)
    ZK = get_attribute(K, :maximal_order)
    d = discriminant(ZK)
    @assert order(d) == zk
    dd = d
  else
    d = ideal(zk, discriminant(K))
    dd = d.num
  end

  r1, r2 = signature(base_field(K))
  C, mC = ray_class_group(dd, infinite_places(base_field(K))[1:r1], n_quo = degree(K))
  N, iN = norm_group(K, mC, of_closure = of_closure)
  return ray_class_field(mC, quo(C, N)[2])
end

@doc Markdown.doc"""
    maximal_abelian_subfield(A::ClassField, k::AnticNumberField) -> ClassField

The maximal abelian extension of $k$ contained in $A$. $k$ must be a subfield of
the base field of $A$.
"""
function maximal_abelian_subfield(A::ClassField, k::AnticNumberField)
  K = base_field(A)
  fl, mp = is_subfield(k, K)
  @assert fl
  return maximal_abelian_subfield(A, mp)
end

function maximal_abelian_subfield(A::ClassField, ::FlintRationalField)
  return maximal_abelian_subfield(A, Hecke.rationals_as_number_field()[1])
end

function factored_modulus(A::ClassField{MapRayClassGrp, T}) where T
  return A.rayclassgroupmap.fact_mod
end

function factored_modulus(A::ClassField{MapClassGrp, T}) where T
  return Dict{NfOrdIdl, Int}()
end

function factored_modulus(A::ClassField_pp{MapRayClassGrp, T}) where T
  return A.rayclassgroupmap.fact_mod
end

function factored_modulus(A::ClassField_pp{MapClassGrp, T}) where T
  return Dict{NfOrdIdl, Int}()
end

function maximal_abelian_subfield(A::ClassField, mp::NfToNfMor)
  k = domain(mp)
  K = codomain(mp)
  ZK = maximal_order(K)
  zk = maximal_order(k)
  # disc(ZK/Q) = N(disc(ZK/zk)) * disc(zk)^deg
  # we need the disc ZK/k, well a conductor.
  d = div(discriminant(ZK), discriminant(zk)^div(degree(K), degree(k)))
  deg = divexact(degree(K), degree(k))
  if is_automorphisms_known(K) && is_normal(K)
    G, mG = automorphism_group(K)
    deg = min(lcm([order(x) for x in G]), deg)
  end
  expo = Int(exponent(codomain(A.quotientmap)))
  mR1 = A.rayclassgroupmap
  mC = pseudo_inv(A.quotientmap)*mR1
  #First, I construct a suitable modulus for A/k
  f_m0 = Dict{NfOrdIdl, Int}()
  fact_mod = factored_modulus(A)
  for (P, e) in fact_mod
    p = intersect_prime(mp, P)
    if haskey(f_m0, p)
      if !is_coprime(minimum(P, copy = false), deg*expo)
        f_m0[p] += e
      end
    else
      if !is_coprime(minimum(P, copy = false), deg*expo)
        f_m0[p] = e
      else
        f_m0[p] = 1
      end
    end
  end
  lp = factor(ideal(zk, d))
  for (P, e) in lp
    if haskey(f_m0, P)
      if !is_coprime(minimum(P, copy = false), deg*expo)
        f_m0[P] += e
      end
    else
      if !is_coprime(minimum(P, copy = false), deg*expo)
        f_m0[P] = e
      else
        f_m0[P] = 1
      end
    end
  end

  #Now, I extend this modulus to K
  f_M0 = Dict{NfOrdIdl, Int}()
  for (p, v) in f_m0
    lp = prime_decomposition(mp, p)
    if is_coprime(minimum(p, copy = false), expo*deg)
      for (P, e) in lp
        f_M0[P] = 1
      end
    else
      for (P, e) in lp
        f_M0[P] = e*v
      end
    end
  end

  R, mR = Hecke.ray_class_group(ZK, f_M0, real_places(K), n_quo = expo * deg)
  r, mr = Hecke.ray_class_group(zk, f_m0, real_places(k), n_quo = expo * deg)
  lP, gS = Hecke.find_gens(mR, coprime_to = minimum(defining_modulus(mR1)[1]))
  listn = NfOrdIdl[norm(mp, x) for x in lP]
  # Create the map between R and r by taking norms
  proj = hom(gS, GrpAbFinGenElem[mr\x for x in listn])
  #compute the norm group of A in R
  proj1 = hom(gS, GrpAbFinGenElem[mC\x for x in lP])
  S, mS = kernel(proj1)
  mS1 = compose(mS, proj)
  G, mG = Hecke.cokernel(mS1)
  return ray_class_field(mr, mG)
end


@doc Markdown.doc"""
    ray_class_field(K::NfRel{nf_elem}) -> ClassField

For a (relative) abelian extension, compute an abstract representation
as a class field.
"""
function ray_class_field(K::NfRel{nf_elem})
  C = maximal_abelian_subfield(K)
  @assert degree(C) <= degree(K)
  if degree(C) != degree(K)
    error("field is not abelian")
  end
  return C
end

@doc Markdown.doc"""
    genus_field(A::ClassField, k::AnticNumberField) -> ClassField

The maximal extension contained in $A$ that is the compositum of $K$
with an abelian extension of $k$.
"""
function genus_field(A::ClassField, k::AnticNumberField)
  B = maximal_abelian_subfield(A, k)
  K = base_field(A)
  fl, mp = is_subfield(k, K)
  @assert fl
  h = norm_group_map(A, B, x -> norm(mp, x))
  return ray_class_field(A.rayclassgroupmap, GrpAbFinGenMap(A.quotientmap * quo(domain(h), kernel(h)[1])[2]))
end

@doc Markdown.doc"""
    subfields(C::ClassField, d::Int) -> Vector{ClassField}

Find all subfields of $C$ of degree $d$ as class fields.
Note: this will not find all subfields over $Q$, but only the ones
sharing the same base field.
"""
function subfields(C::ClassField, d::Int)
  mR = C.rayclassgroupmap
  mQ = C.quotientmap

  return ClassField[ray_class_field(mR, GrpAbFinGenMap(mQ*x)) for x = subgroups(codomain(mQ), index = d, fun = (x,y) -> quo(x, y, false)[2])]
end

@doc Markdown.doc"""
    subfields(C::ClassField) -> Vector{ClassField}

Find all subfields of $C$ as class fields.
Note: this will not find all subfields over $Q$, but only the ones
sharing the same base field.
"""
function subfields(C::ClassField)
  mR = C.rayclassgroupmap
  mQ = C.quotientmap

  return ClassField[ray_class_field(mR, GrpAbFinGenMap(mQ*x)) for x = subgroups(codomain(mQ), fun = (x,y) -> quo(x, y, false)[2])]
end

@doc Markdown.doc"""
    normal_closure(C::ClassField) -> ClassField

For a ray class field $C$ extending a normal base field $k$, compute the
normal closure over $Q$.
"""
function normal_closure(C::ClassField)
  c = defining_modulus(C)
  k = base_field(C)
  if length(c[2]) > 0
    inf = real_places(k)
  else
    inf = InfPlc[]
  end
  aut = automorphisms(k)
  @assert length(aut) == degree(k)
  fin = lcm([induce_image(x, c[1]) for x = aut])

  D = ray_class_field(fin, inf, n_quo = Int(exponent(codomain(C.quotientmap))))
  h = norm_group_map(D, C)
  aut1 = small_generating_set(aut)
  act = Hecke.induce_action(D, aut1)
  k = kernel(h, true)[1]

  k = intersect([x(k)[1] for x = act])

  q, mq = quo(domain(h), k)
  return ray_class_field(D.rayclassgroupmap, GrpAbFinGenMap(D.quotientmap * mq))
end

function rewrite_with_conductor(C::ClassField)
  c, inf = conductor(C)
  if defining_modulus(C) == (c, inf)
    return C
  end
  E = ray_class_field(C.rayclassgroupmap)
  D = ray_class_field(c, inf, n_quo = Int(exponent(codomain(C.quotientmap))))
  h = norm_group_map(E, D)
  q, mq = quo(codomain(h), h(GrpAbFinGenMap(E.quotientmap)(kernel(GrpAbFinGenMap(C.quotientmap), true)[1])[1])[1])
  C = ray_class_field(D.rayclassgroupmap, GrpAbFinGenMap(D.quotientmap*mq))
  return C
end

function induce_action(C::ClassField, Aut::Vector{Hecke.NfToNfMor} = Hecke.NfToNfMor[])
  return induce_action(C.rayclassgroupmap, Aut, C.quotientmap)
end

@doc Markdown.doc"""
    is_normal(C::ClassField) -> Bool

For a class field $C$ defined over a normal base field $k$, decide
if $C$ is normal over $Q$.
"""
function is_normal(C::ClassField)

  K = base_field(C)
  aut = automorphisms(K)
  if length(aut) == degree(K)
    return is_normal_easy(C)
  else
    return is_normal_difficult(C)
  end

end

function is_normal_easy(C::ClassField)
  aut = automorphisms(base_field(C))
  c, inf = conductor(C)
  if any(x-> c != induce_image(x, c), aut)
    return false
  end
  s1 = Set(inf)
  if any(x -> s1 != Set(induce_image(x, y) for y = s1), aut)
    return false
  end
  C = rewrite_with_conductor(C)
  mR = C.rayclassgroupmap
  new_aut = small_generating_set(aut)
  act = induce_action(mR, new_aut)
  mk = kernel(GrpAbFinGenMap(C.quotientmap), true)[2]
  #normal iff kernel is invariant
  return is_stable(act, mk)
end

function is_normal_difficult(C::ClassField)

  #First, I check that the norm group of the splitting field
  #of the base field contains C

  K = base_field(C)
  nK = degree(K)
  O = maximal_order(K)
  f = K.pol
  I = ideal(O, discriminant(O))
  r, mr = ray_class_group(I, real_places(K))
  Kt, t = PolynomialRing(K, "t", cached = false)
  g = divexact(evaluate(f, t), t - gen(K))
  G, mG = norm_group(g, mr, of_closure = true)
  k, mk = cokernel(mG)
  C1 = ray_class_field(mr, mk)
  if rem(degree(C), degree(C1))!= 0 || !is_subfield(C1, C)
    return false
  end
  if degree(C1) == degree(C)
    return true
  end

  # Claus's Idea: I don't want to compute the extension, I want to test the stability of the modulus under the action of the
  # automorphisms, so only the totally split primes!
  # In other words, I need to check that given a totally split prime p, all the primes lying
  # over p are either all zero or all non-zero in the ray class field

  p = 1
  d = (discriminant(O)^degree(C1))*numerator(norm(evaluate(FacElem(discriminant(C1)))))
  ld = (ceil(fmpz, log(d)))
  n = degree(C1)*nK
  bound = (4*ld + 2*n +5)^2
  mp = pseudo_inv(C.quotientmap) * C.rayclassgroupmap
  while p < bound
    p = next_prime(p)
    if divisible(discriminant(O), p)
      continue
    end
    lp = prime_decomposition(O, p)
    if !all([q[1].splitting_type[2] == 1 for q in lp])
      continue
    end
    q = lp[1][1]
    fl = iszero(mp\q)
    for i = 2:nK
      if fl != iszero(mp\lp[i][1])
        return false
      end
    end
  end
  return true
end


@doc Markdown.doc"""
    is_central(C::ClassField) -> Bool

For a class field $C$ defined over a normal base field $k$, decide
if $C$ is central over $Q$.
"""
function is_central(C::ClassField)
  aut = automorphisms(base_field(C))
  c, inf = conductor(C)

  if any(x-> c != induce_image(x, c), aut)
    return false
  end
  s1 = Set(inf)
  if any(x -> s1 != Set(induce_image(x, y) for y = s1), aut)
    return false
  end
  C = rewrite_with_conductor(C)
  mR = C.rayclassgroupmap
  act = induce_action(mR, aut)
  k = kernel(GrpAbFinGenMap(C.quotientmap), true)
  #central iff action is trivial on the kernel
  g = [k[2](k[1][i]) for i = 1:ngens(k[1])]

  return all(x -> all(y -> x(y) == y, g), act)
end

function lcm(A::AbstractArray{<:NfAbsOrdIdl})
  a = first(A)
  a = ideal(order(a), 1)
  for b = A
    a = lcm(a, b)
  end
  return a
end

#TODO: should be done in Nemo/AbstractAlgebra s.w.
#      needed by ^ (the generic power in Base using square and multiply)
Base.copy(f::Generic.MPoly) = deepcopy(f)
Base.copy(f::Generic.Poly) = deepcopy(f)


@doc Markdown.doc"""
    lorenz_module(k::AnticNumberField, n::Int) -> NfOrdIdl

Finds an ideal $A$ s.th. for all positive units $e = 1 \bmod A$ we have that
$e$ is an $n$-th power. Uses Lorenz, number theory, 9.3.1.
If `containing` is set, it has to be an integral ideal. The resulting ideal will be
a multiple of this.
"""
function lorenz_module(k::AnticNumberField, n::Int; containing=false)
  lf = factor(n)
  return Base.reduce(lcm, [lorenz_module_pp(k, Int(p), l, containing = containing) for (p,l) = lf.fac])
end

#TODO: is this the right interface???
@doc Markdown.doc"""
    (::NfAbsOrdIdlSet)(m::Map, I::NfOrdIdl) -> NfOrdIdl

Given an embedding $m:k\to K$ of number fields and an ideal $I$ in $k$,
find the ideal above $I$ in $K$.
"""
function (I::NfAbsOrdIdlSet{Nemo.AnticNumberField,Nemo.nf_elem})(mp::Map, i::NfOrdIdl)
  assure_2_normal(i)
  return ideal(order(I), i.gen_one, order(I)(mp(i.gen_two.elem_in_nf)))
end

#TODO: write code (map?) to change polynomial rings other than evaluate

@doc Markdown.doc"""
    norm(m::T, a::nf_elem) where T <: Map{AnticNumberField, AnticNumberField} -> nf_elem

Given an embedding $m:k\to K$ of number fields and an element in $K$, find the norm
$N_{K/k}(a)$.
"""
function norm(m::T, a::nf_elem) where T <: Map{AnticNumberField, AnticNumberField}
  K = codomain(m)
  #= shamelessly from Trager:
           K  Then: K = Q(c) = k(c) = Q(b)(c)
           |        f(c) = 0 in Q[t]
      k    |        h(c) = 0 in k[t]. Trager: N(h) = f. eta in Q[t] s.th. m(b) = eta(c)
      |    |        h = gcd(b - eta, f)
      Q    Q  so N_K/k(a) = res(h, a)
  =#
  @assert K == parent(a)
  k = domain(m)
  kt, t = PolynomialRing(k, cached = false)
  Qt = parent(K.pol)
  h = gcd(gen(k) - evaluate(Qt(m(gen(k))), t), evaluate(K.pol, t))
  return resultant(h, mod(evaluate(Qt(a), t), h))
end

function norm(m::T, a::FacElem{nf_elem, AnticNumberField}) where T <: Map{AnticNumberField, AnticNumberField}
  K = codomain(m)
  @assert K == base_ring(a)
  k = domain(m)
  kt, t = PolynomialRing(k, cached = false)
  Qt = parent(K.pol)
  h = gcd(gen(k) - evaluate(Qt(m(gen(k))), t), evaluate(K.pol, t))
  d = Dict{nf_elem, fmpz}()
  for (e,v) = a.fac
    n = resultant(h, mod(change_base_ring(k, Qt(e), parent = kt), h))
    if haskey(d, n)
      d[n] += v
    else
      d[n] = v
    end
  end
  return FacElem(k, d)
end

#TODO: change order!!! this only works for maximal orders
function Base.intersect(I::NfAbsOrdIdl, R::NfAbsOrd)
  @assert is_maximal(R)
  if number_field(R) == number_field(order(I))
    return I
  end
  fl, m = is_subfield(number_field(R), number_field(order(I)))
  @assert fl
  return minimum(m, I)
end

Base.intersect(R::NfAbsOrd, I::NfAbsOrdIdl) = intersect(I, R)

function Base.intersect(I::NfOrdFracIdl, R::NfAbsOrd)
  @assert is_maximal(R)
  n, d = integral_split(I)
  return intersect(n, R)
end

Base.intersect(R::NfAbsOrd, I::NfOrdFracIdl) = intersect(I, R)

@doc Markdown.doc"""
    content_ideal(f::PolyElem{nf_elem}, R::NfAbsOrd) -> NfAbsOrdIdl

The fractional $R$-ideal generated by the coefficients of $f$.
"""
function content_ideal(f::PolyElem{nf_elem}, R::NfAbsOrd)
  @assert number_field(R) == base_ring(f)
  i = sum(coeff(f, i)*R for i=0:degree(f) if !iszero(coeff(f, i)))
  return i
end

@doc Markdown.doc"""
    content_ideal(f::PolyElem{NfAbsOrdElem}) -> NfAbsOrdIdl

The ideal generated by the coefficients of $f$.
"""
function content_ideal(f::PolyElem{NfAbsOrdElem})
  R = base_ring(f)
  return sum(coeff(f, i)*R for i=0:degree(f) if !iszero(coeff(f, i)))
end

#TODO: check the math
# - I think in the p==2 l is too large in general
# - I probably only the p-part of c is needed
# - possibly even only the p-th cyclo field, although I really don't know
function lorenz_module_pp(k::AnticNumberField, p::Int, l::Int; containing=false)
  if p == 2
    l = max(l, lorenz_eta_level(k))
    l += 1
  end
  n = p^l
  C = cyclotomic_extension(k, n)
  Ka = C.Ka
  ZK = maximal_order(Ka)
  c, mc = class_group(Ka)
  lp = prime_decomposition(ZK, p)
  S = [P[1] for P = lp]
  s = [P[1] for P = prime_decomposition(maximal_order(k), p)]

  fc = false
  if containing != false
    @assert typeof(containing) == NfOrdIdl
    fc = factor(containing)
    s = union(s, collect(keys(fc)))
    fc = factor(parent(S[1])(C.mp[2], containing))
    S = union(S, collect(keys(fc)))
  end
  Q, mQ = quo(c, [mc\P for P = S])

  a, _ = find_gens(pseudo_inv(mc)*mQ, PrimesSet(degree(k), -1), p*numerator(discriminant(Ka)))
  S = Set(intersect_nonindex(C.mp[2], P) for P = a)
  union!(S, s)

  d = Dict{typeof(first(S)), Int}()
  for P = S
    # need x = 1 mod P^l -> x = y^n in k_P
    # Newton: x^n-1 has derivative nx^(n-1) and need l > 2*val(n, P)
    v = 2*valuation(p, P) + 1
    if containing != false
      v = max(v, valuation(containing, P))
    end
    d[P] = v
  end
  return numerator(evaluate(FacElem(d), coprime = true))
end

function lorenz_eta_level(k::AnticNumberField)
  # find max r s.th. eta_r in k, eta_(r+1) not in k
  # where eta_r = (zeta_(2^r) + 1/zeta_(2^r))
  r = 2
  x = PolynomialRing(FlintZZ, cached = false)[2]
  f = cos_minpoly(2^r, x)
  while has_root(f, k)[1]
    r += 1
    f = cos_minpoly(2^r, x)
  end
  return r - 1
end
