###############################################################################
#
#  Number_field with Brauer
#
###############################################################################
@doc Markdown.doc"""
    NumberField_using_Brauer(CF::ClassField) -> NfRelNS{Nemo.nf_elem}
Given a (formal) abelian extension, compute the class field by
finding defining polynomials
for all prime power cyclic subfields using Brauer relations.
Note, by type this is always a non-simple extension.
"""
function NumberField_using_Brauer(CF::ClassField{S, T}; redo::Bool = false) where {S, T}
  if isdefined(CF, :A) && !redo
    return CF.A
  end
  
  res = ClassField_pp{S, T}[]
  G = codomain(CF.quotientmap)
  @assert issnf(G)
  q = GrpAbFinGenElem[G[i] for i=1:ngens(G)]
  for i=1:ngens(G)
    o = G.snf[i]
    lo = factor(o)
    for (p, e) = lo.fac
      q[i] = p^e*G[i]
      S1, mQ = quo(G, q, false)
      push!(res, ray_class_field_cyclic_pp_Brauer(CF, mQ))
    end
    q[i] = G[i]
  end
  CF.cyc = res
  CF.A = number_field(Generic.Poly{nf_elem}[x.A.pol for x = CF.cyc], check = false, cached = false)[1]
  @vprint :ClassField 1 "NumberField_using_Brauer finished\n"
  return CF.A
end


function ray_class_field_cyclic_pp_Brauer(CF::ClassField{S, T}, mQ::GrpAbFinGenMap) where {S, T}
  @vprint :ClassField 1 "cyclic prime power class field of degree $(degree(CF))\n"
  CFpp = ClassField_pp{S, T}()
  CFpp.quotientmap = compose(CF.quotientmap, mQ)
  CFpp.rayclassgroupmap = CF.rayclassgroupmap
  @assert domain(CFpp.rayclassgroupmap) == domain(CFpp.quotientmap)
  
  e = degree(CFpp)
  v, q = ispower(e)
  k = base_field(CFpp)
  CE = cyclotomic_extension(k, e)
  
  @vprint :ClassField 1 "computing the S-units...\n"
  @vtime :ClassField 1 _rcf_S_units_using_Brauer(CFpp)
  mr = CF.rayclassgroupmap
  mq = CFpp.quotientmap
  KK = kummer_extension(e, FacElem{nf_elem, AnticNumberField}[CFpp.a])
  ng, mng = norm_group(KK, CE.mp[2], mr)
  attempt = 1
  while !iszero(mng*mq)
    attempt += 1
    @show "attempt number $(attempt)"
    _rcf_S_units_enlarge(CE, CFpp)
    KK = kummer_extension(e, FacElem{nf_elem, AnticNumberField}[CFpp.a])
    ng, mng = norm_group(KK, CE.mp[2], mr)
  end
  
  @vprint :ClassField 1 "reducing the generator...\n"
  @vtime :ClassField 1 _rcf_reduce(CFpp)
  @vprint :ClassField 1 "descending ...\n"
  @vtime :ClassField 1 _rcf_descent(CFpp)
  return CFpp
end

################################################################################
#
#  S-units computation
#
################################################################################

function _rcf_S_units_enlarge(CE, CF::ClassField_pp)
  lP = CF.sup
  OK = order(lP[1])
  f = maximum(minimum(p) for p in lP)
  for i = 1:5
    f = next_prime(f)
    push!(lP, prime_decomposition(OK, f)[1][1])
  end
  e = degree(CF)
  @vtime :Fields 3 S, mS = NormRel.sunit_group_fac_elem_quo_via_brauer(nf(OK), lP, e)
  KK = kummer_extension(e, FacElem{nf_elem, AnticNumberField}[mS(S[i]) for i=1:ngens(S)])

  #gens mod n-th power - to speed up the frobenius computation
  gens = KK.gen
  gens_mod_nth = Vector{FacElem{nf_elem, AnticNumberField}}(undef, length(gens))
  for i = 1:length(gens)
    el = Dict{nf_elem, fmpz}()
    for (s, v) in gens[i].fac
      ex = mod(v, e)
      if ex != 0 
        el[s] = ex
      end
    end
    gens_mod_nth[i] = FacElem(el)
  end
  KK.gen_mod_nth_power = gens_mod_nth
  CF.bigK = KK
  lf = factor(minimum(defining_modulus(CF)[1]))
  lfs = Set(collect(keys(lf.fac)))
  CE.kummer_exts[lfs] = (lP, KK)
  _rcf_find_kummer(CF)
  return nothing
end


function _rcf_S_units_using_Brauer(CF::ClassField_pp)

  f = defining_modulus(CF)[1]
  @vprint :ClassField 2 "Kummer extension with modulus $f\n"
  k1 = base_field(CF)
  
  #@assert Hecke.isprime_power(e)
  @vprint :ClassField 2 "Adjoining the root of unity\n"
  C = cyclotomic_extension(k1, degree(CF))
  automorphisms(C, copy = false)
  G, mG = automorphism_group(C.Ka)
  @vtime :ClassField 3 fl = NormRel.has_useful_brauer_relation(G)
  if fl
    @vtime :ClassField 3 lP, KK = _s_unit_for_kummer_using_Brauer(C, minimum(f))
  else
    lP, KK = _s_unit_for_kummer(C, minimum(f))
  end
  
  CF.bigK = KK
  CF.sup = lP
  _rcf_find_kummer(CF)
  return nothing
end


#This function finds a set S of primes such that we can find a Kummer generator in it.
function _s_unit_for_kummer_using_Brauer(C::CyclotomicExt, f::fmpz)
  
  e = C.n
  lf = factor(f)
  lfs = Set(collect(keys(lf.fac)))
  for (k, v) in C.kummer_exts
    if issubset(lfs, k)
      return v
    end
  end  
  K = absolute_field(C)
  @vprint :ClassField 2 "Maximal order of cyclotomic extension\n"
  ZK = maximal_order(K)
  
  lP = Hecke.NfOrdIdl[]

  for p = keys(lf.fac)
    #I remove the primes that can't be in the conductor
    lp = prime_decomposition(ZK, p)
    for (P, s) in lp
      if gcd(norm(P), e) != 1 || gcd(norm(P)-1, e) != 1
        push!(lP, P)
      end 
    end
  end
  
  if length(lP) < 10
    #add some primes
    pp = f+1
    while length(lP) < 10
      pp = next_prime(pp)
      lpp = prime_decomposition(ZK, pp)
      if length(lpp) == degree(K)
        push!(lP, lpp[1][1])
      end
    end
  end

  
  @vprint :Fields 3 "Computing S-units with $(length(lP)) primes\n"
  @vtime :Fields 3 S, mS = NormRel.sunit_group_fac_elem_quo_via_brauer(C.Ka, lP, e)
  KK = kummer_extension(e, FacElem{nf_elem, AnticNumberField}[mS(S[i]) for i=1:ngens(S)])
  
  #gens mod n-th power - to speed up the frobenius computation
  gens = KK.gen
  gens_mod_nth = Vector{FacElem{nf_elem, AnticNumberField}}(undef, length(gens))
  for i = 1:length(gens)
    el = Dict{nf_elem, fmpz}()
    for (s, v) in gens[i].fac
      ex = mod(v, e)
      if ex != 0 
        el[s] = ex
      end
    end
    gens_mod_nth[i] = FacElem(el)
  end
  KK.gen_mod_nth_power = gens_mod_nth
  C.kummer_exts[lfs] = (lP, KK)
  return lP, KK
end
