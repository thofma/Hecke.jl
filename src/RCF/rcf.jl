export kummer_extension, ray_class_field

add_verbose_scope(:ClassField)
add_assert_scope(:ClassField)
set_assert_level(:ClassField, 1)


function kummer_extension(n::Int, gen::Array{nf_elem, 1})
  g = [FacElem(x) for x=gen]
  return kummer_extension(n, g)
end

function _extend_auto(K::Hecke.NfRel{nf_elem}, h::Hecke.NfToNfMor)
  @assert iskummer_extension(K)
  k = base_ring(K)
  Zk = maximal_order(k)
  zeta, ord = Hecke.torsion_units_gen_order(Zk)
  @assert ord % degree(K) == 0
  zeta = k(zeta)^div(ord, degree(K))

  im_zeta = h(zeta)
  r = 1
  z = zeta
  while im_zeta != z
    r += 1
    z *= zeta
  end

  a = -coeff(K.pol, 0)
  a = a^r//h(a) # this assumes K/k to be abelian
#  global last_rt = (a, degree(K))
  fl, b = hasroot(a, degree(K))
  @assert fl

  return NfRelToNfRelMor(K, K, h, 1//b*gen(K)^r)
end

doc"""
  number_field(I::NfOrd)
> Return the number fields containing $I$.
"""
@inline function number_field(O::NfOrd)
  return O.nf
end

# the Frobenius at p in K:
#K is an extension of k, p a prime in k,
#returns a vector in (Z/nZ)^r representing the Frob
function can_frobenius(p::NfOrdIdl, K::KummerExt)
  if haskey(K.frob_cache, p)
    return K.frob_cache[p]
  end
  Zk = order(p)
  if index(Zk) % minimum(p) == 0 
    #index divisors and residue class fields don't agree
    # ex: x^2-10, rcf of 29*Zk, 7. 239 is tricky...
    throw(BadPrime(p))
  end

  F, mF = ResidueField(Zk, p)
  mF = extend_easy(mF, number_field(Zk))

  #K = sqrt[n](gen), an automorphism will be
  # K[i] -> zeta^? K[i]
  # Frob(sqrt[n](a), p) = sqrt[n](a)^N(p) (mod p) = zeta^r sqrt[n](a)
  # sqrt[n](a)^N(p) = a^(N(p)-1 / n) = zeta^r mod p

  z_p = inv(mF(Zk(K.zeta)))
  @assert norm(p) % K.n == 1
  ex = div(norm(p)-1, K.n)
  aut = fmpz[]
  for g in K.gen
    mu = mF(g)^ex  # can throw bad prime!
    i = 0
    while !isone(mu)
      i += 1
      if i > K.n
      end
      @assert i <= K.n
      mu *= z_p
    end
    push!(aut, fmpz(i))
  end
  z = K.AutG(aut)
  K.frob_cache[p] = z
  return z
end

function can_frobenius(p::NfOrdIdl, K::KummerExt, g::FacElem{nf_elem})
  Zk = order(p)
  if index(Zk) % minimum(p) == 0 
    #index divisors and residue class fields don't agree
    # ex: x^2-10, rcf of 29*Zk, 7. 239 is tricky...
    throw(BadPrime(p))
  end

  F, mF = ResidueField(Zk, p)
  mF = extend_easy(mF, number_field(Zk))

  #K = sqrt[n](gen), an automorphism will be
  # K[i] -> zeta^? K[i]
  # Frob(sqrt[n](a), p) = sqrt[n](a)^N(p) (mod p) = zeta^r sqrt[n](a)
  # sqrt[n](a)^N(p) = a^(N(p)-1 / n) = zeta^r mod p

  z_p = inv(mF(Zk(K.zeta)))
  @assert norm(p) % K.n == 1
  ex = div(norm(p)-1, K.n)
  aut = fmpz[]

  mu = mF(g)^ex  # can throw bad prime!
  i = 0
  while !isone(mu)
    i += 1
    if i > K.n
    end
    @assert i <= K.n
    mu *= z_p
  end
  return i
end


#=
  next, to piece things together:
    have a quo of some ray class group in k,
    taking primes in k over primes in Z that are 1 mod n
    then the prime is totally split in Kr, hence I do not need to
      do relative splitting and relative ideal norms. I am lazy
        darn: I still need to match the ideals
    find enough such primes to generate the rcg quotient (via norm)
                       and the full automorphism group of the big Kummer

          Kr(U^(1/n))  the "big" Kummer ext
         /
        X(z) = Kr(x^(1/n)) the "target"
      / /
    X  Kr = k(z)  = Ka
    | /             |
    k               |
    |               |
    Q               Q

    this way we have the map (projection) from "big Kummer" to 
    Aut(X/k) = quo(rcg)
    The generator "x" is fixed by the kernel of this map

    Alternatively, "x" could be obtained via Hecke's theorem, ala Cohen

    Finally, X is derived via descent
=#

# for a supported ideal map, the modulus that was used to define it.
function _modulus(mR::Map)
  while issubtype(typeof(mR), Hecke.CompositeMap)
    mR = mR.f
  end
  if issubtype(typeof(mR), Hecke.MapClassGrp)
    return ideal(order(codomain(mR)), 1)
  end
  @assert issubtype(typeof(mR), Hecke.MapRayClassGrp)
  return mR.modulus_fin
end

######################################################################
#mR: SetIdl -> GrpAb (inv of ray_class_group or Frobenius or so)
#
function find_gens(mR::Map, S::PrimesSet, cp::fmpz=fmpz(1))
  ZK = order(domain(mR))

  R = codomain(mR) 

  sR = elem_type(R)[]
  lp = elem_type(domain(mR))[]

  st = start(S)
  np = 0
  extra = 1

  q, mq = quo(R, sR, false)
  while true
    p, st = next(S, st)
    if cp % p == 0
      continue
    end
    @vprint :ClassField 2 "doin` $p\n"
    np += 1

    if np % ngens(R) == 0
      @vprint :ClassField 3 "need many generators... $np for group with $(ngens(R))"
    end
    lP = prime_decomposition(ZK, p)

    f=R[1]
    for (P, e) = lP
      try
        f = mR(P)
      catch e
        if !isa(e, BadPrime)
          rethrow(e)
        end
        continue
      end
      if iszero(mq(f))
        continue
      end
      push!(sR, f)
      push!(lp, P)
      q, mq = quo(R, sR, false)
    end
    if order(q) == 1   
      break
    end
  end

  return lp, sR
end


# mR: GrpAb A -> Ideal in k, only preimage used
# cf: Ideal in K -> GrpAb B, only image
# mp:: k -> K inclusion
# builds a (projection) from B -> A identifying (pre)images of
# prime ideals, the ideals are coprime to cp and ==1 mod n

function order(A::FacElemMon{IdealSet})
  return order(A.base_ring)
end

function order(A::FacElemMon{NfOrdIdlSet})
  return order(A.base_ring)
end

function build_map(mR::Map, K::KummerExt, c::CyclotomicExt)
  #mR should be GrpAbFinGen -> IdlSet
  #          probably be either "the rcg"
  #          or a compositum, where the last component is "the rcg"
  # we need this to get the defining modulus - for coprime testing

  ZK = maximal_order(base_ring(K.gen[1]))
  cp = lcm(minimum(_modulus(mR)), discriminant(ZK))
  cf = Hecke.MapFromFunc(x->can_frobenius(x, K), IdealSet(ZK), K.AutG)

  mp = c.mp[2]
  ZK = maximal_order(c.Ka)
  @assert order(domain(cf)) == ZK
  Zk = order(codomain(mR))
  Id_Zk = Hecke.NfOrdIdlSet(Zk)
  k = nf(Zk)
  @assert k == domain(mp)
  Qx = parent(k.pol)

  Sp = Hecke.PrimesSet(200, -1, c.n, 1) #primes = 1 mod n, so totally split in cyclo

  lp, sG = find_gens(cf, Sp, cp)

  R = domain(mR) 
  G = codomain(cf)
  sR = elem_type(R)[]

  for P = lp
    p = Id_Zk(intersect_nonindex(mp, P))
    push!(sR, valuation(norm(P), norm(p))*preimage(mR, p))
  end
  @assert order(quo(G, sG, false)[1]) == 1
       # if think if the quo(G, ..) == 1, then the other is automatic
       # it is not, in general it will never be.
       #example: Q[sqrt(10)], rcf of 16*Zk
  # now the map G -> R sG[i] -> sR[i] 
  h = hom(sG, sR)
  return h
end

function (I_Zk::NfOrdIdlSet)(a::NfOrdIdl)
  if parent(a) == I_Zk
    return a
  end
  Zk = order(I_Zk)
  Zl = order(a)
  @assert has_2_elem(a)
  b = ideal(Zk, a.gen_one, Zk(Zk.nf(Zl.nf(a.gen_two))))
  for i in [:gens_normal, :gens_weakly_normal, :iszero, :minimum]
    if isdefined(a, i)
      setfield!(b, i, getfield(a, i))
    end
  end
  n = divexact(degree(Zk.nf), degree(Zl.nf))
  if isdefined(a, :norm)
    b.norm = a.norm^n
  end
  if isdefined(a, :princ_gen)
    b.princ_gen = Zk(Zk.nf(Zl.nf(a.princ_gen)))
  end
  if isdefined(a, :isprime) && Zk.nf == Zl.nf && Zk.ismaximal == 1 &&
    Zl.ismaximal == 1
    b.isprime = a.isprime
    if isdefined(a, :splitting_type)
      b.splitting_type = a.splitting_type
    end
  end
  return b
end

doc"""
    ray_class_field(m::Map, p::Int=0) -> ClassField
> Creates the (formal) abelian extension defined by the map $m: A \to I$
> where $I$ is the set of ideals coprime to the modulus defining $m$ and $A$ 
> is a quotient of the ray class group (or class group).
> If $p$ is given and non-zero, only the quotient modulo $p$-th powers is
> created.
"""
function ray_class_field(m::Map, p::Int=0)
  CF = ClassField()
  if p != 0
    q, mq = quo(domain(m), p, false)
    m = m*inv(mq)
  end
  m = Hecke.make_snf(m)

  CF.mq = m
  return CF
end

doc"""
    number_field(CF::ClassField) -> Array{GenPol{nf_elem}, 1}
> Given a (formal) abelian extension, compute defining polynomials
> for all prime power cyclic subfields.
"""
function number_field(CF::ClassField)
  if isdefined(CF, :A)
    return CF.A
  end
  m = CF.mq
  
  res = []
  G = domain(m)
  q = [G[i] for i=1:ngens(G)]
  for i=1:ngens(G)
    o = order(G[i])
    lo = factor(o)
    for (p, e) = lo.fac
      q[i] = p^e*G[i]
      S, mQ = quo(G, q, false)
      push!(res, ray_class_field_cyclic_pp(m*inv(mQ)))
    end
    q[i] = G[i]
  end
  CF.cyc = res
  CF.A = number_field([x.A.pol for x = CF.cyc])[1]
  return CF.A
end

function ray_class_field_cyclic_pp(mq::Map)
  @assert iscyclic(domain(mq))
  @vprint :ClassField 1 "cyclic prime power class field of degree $(order(domain(mq)))\n"
  CF = ClassField_pp()
  CF.mq = mq
  @vprint :ClassField 1 "finding the Kummer extension...\n"
  _rcf_find_kummer(CF)
  @vprint :ClassField 1 "reducing the generator...\n"
  _rcf_reduce(CF)
  @vprint :ClassField 1 "descending ...\n"
  _rcf_descent(CF)
  return CF
end

function _rcf_find_kummer(CF::ClassField_pp)
  mq = CF.mq
  if isdefined(CF, :K)
    return CF.K
  end
  f = _modulus(mq)
  @vprint :ClassField 2 "Kummer extension ... with conductor(?) $f\n"
  k = nf(order(f))
  e = order(domain(mq))  
  @assert Hecke.isprime_power(e)

  @vprint :ClassField 2 "Adjoining the root of unity\n"
  C = cyclotomic_extension(k, Int(e))
  K = C.Ka

  @vprint :ClassField 2 "Maximal order of cyclotomic extension\n"
  ZK = maximal_order(K)
  
  @vprint :ClassField 2 "Class group of cyclotomic extension\n"
  c, mc = class_group(ZK)
  allow_cache!(mc)
  @vprint :ClassField 2 "... $c\n"

  q, mq = quo(c, e, false)
  mc = mc*inv(mq)
  c = q

  lf = factor(minimum(f)*e)
  lP = Hecke.NfOrdIdl[]
  for p = keys(lf.fac)
    lp = prime_decomposition(ZK, p)  #TODO: make it work for fmpz
    lP = vcat(lP, [x[1] for x = lp])
  end
  g = elem_type(c)[preimage(mc, x) for x = lP]

  q, mq = quo(c, g, false)
  mc = mc * inv(mq)
  c = q

  lP = vcat(lP, Hecke.find_gens(inv(mc), PrimesSet(100, -1))[1])
  @vprint :ClassField 2 "using $lP of length $(length(lP)) for s-units\n"
if false
  println("enlarging to be Galois closed - just in case...", length(lP))
  lP = Set(lP)
  _lp = Set(minimum(x) for x = lP)
  for p = _lp
    fp = prime_decomposition(ZK, Int(p))
    for I = fp
      push!(lP, I[1])
    end
  end
  lP = collect(lP)
  println("finally:", length(lP))
end
  @vprint :ClassField 2 "using $lP of length $(length(lP)) for s-units\n"

  @vtime :ClassField 2 S, mS = Hecke.sunit_group_fac_elem(lP)
  @vprint :ClassField 2 "... done\n"
  @vtime :ClassField 2 KK = kummer_extension(Int(e), [mS(S[i]) for i=1:ngens(S)])
  CF.bigK = KK

  @vprint :ClassField 2 "building Artin map for the large Kummer extension\n"
  @vtime :ClassField 2 h = build_map(CF.mq, KK, C)
  @vprint :ClassField 2 "... done\n"

  k, mk = kernel(h) 
  G = domain(h)
  
  # x needs to be fixed by k
  # that means x needs to be in the kernel:
  # x = prod gen[1]^n[i] -> prod (z^a[i] gen[i])^n[i]
  #                            = z^(sum a[i] n[i]) x
  # thus it works iff sum a[i] n[i] = 0
  # for all a in the kernel
  R = ResidueRing(FlintZZ, C.n)
  M = zero_matrix(R, ngens(k), ngens(G))
  for i=1:ngens(k)
    ki = mk(k[i])
    for j=1:ngens(G)
      M[i, j] = ki[j]
    end
  end

  n, i = nullspace(M)
  @assert i>0
  n = lift(n)
  N = GrpAbFinGen([e for j=1:rows(n)])
  s, ms = sub(N, GrpAbFinGenElem[sum([n[j, k]*N[j] for j=1:rows(n)]) for k=1:i], false)
  ms = Hecke.make_snf(ms)
  @assert iscyclic(domain(ms))
  o = order(domain(ms)[1])
  c = fmpz(1)
  if o < e
    c = div(e, o)
  end
  n = ms(domain(ms)[1])
  @vprint :ClassField 2 "final $n of order $o and e=$e\n"
  a = prod([KK.gen[i]^div(mod(n[i], e), c) for i=1:ngens(parent(n))])
  @vprint :ClassField 2 "generator $a\n"
  CF.a = a
  CF.bigK = KK
  CF.K = pure_extension(Int(o), a)[1]
end

function _rcf_reduce(CF::ClassField_pp)
  e = order(domain(CF.mq))
  CF.a = FacElem(reduce_mod_powers(CF.a, degree(CF.K)))
  CF.K = pure_extension(degree(CF.K), CF.a)[1]
end

function _rcf_descent(CF::ClassField_pp)
  if isdefined(CF, :A)
    return CF.A
  end

  @vprint :ClassField 2 "Descending ...\n"
               
  const mq = CF.mq
  const e = Int(order(domain(mq)))
  const k = nf(order(codomain(mq)))
  const C = cyclotomic_extension(k, e)
  const A = CF.K
#= 
    now the automorphism group of A OVER k
    A = k(zeta, a^(1/n))
    we have
     tau: A-> A : zeta -> zeta   and a^(1/n) -> zeta a^(1/n)
   sigma: A-> A : zeta -> zeta^l and a^(1/n) -> (sigma(a))^(1/n)
                                                = c a^(s/n)
     for some c in k(zeta) and gcd(s, n) == 1
    Since A is compositum of the class field and k(zeta), A is abelian over
    k, thus sigma * tau = tau * sigma

    sigma * tau : zeta    -> zeta         -> zeta^l
                  a^(1/n) -> zeta a^(1/n) -> zeta^l c a^(s/n)
    tau * sigma : zeta    -> zeta^l       -> zeta^l
                  a^(1/n) -> c a^(s/n)    -> c zeta^s a^(s/n)
   
    Since A is abelian, the two need to agree, hence l==s and
    c can be computed as root(sigma(a)*a^-s, n)

    This has to be done for enough autpmorphisms of k(zeta)/k to generate
    the full group. If n=p^k then this is one (for p>2) and n=2, 4 and
    2 for n=2^k, k>2
=#

  g, mg = unit_group(ResidueRing(FlintZZ, e))
  mg = Hecke.make_snf(mg)
  @assert (e%8 == 0 && ngens(domain(mg))==2) ||
           ngens(domain(mg)) <= 1

  if degree(C.Kr) < order(g)  # there was a common subfield, we
                              # have to pass to a subgroup
    @assert order(g) % degree(C.Kr) == 0
    f = C.Kr.pol
    s, ms = sub(g, [x for x = g if iszero(f(gen(C.Kr)^Int(lift(mg(x)))))], false)
    ss, mss = snf(s)
    g = ss
    mg = mg*ms*mss
  end

  @vprint :ClassField 2 "building automorphism group over ground field...\n"

  AutA_gen = []
  AutA_rel = zero_matrix(FlintZZ, ngens(g)+1, ngens(g)+1)
  const zeta = C.mp[1](gen(C.Kr))
  const n = degree(A)
  @assert e % n == 0

  @vprint :ClassField 2 "... the trivial one (Kummer)\n"
  tau = Hecke.NfRelToNfRelMor{nf_elem,  nf_elem}(A, A, zeta^div(e, n)*gen(A))
  push!(AutA_gen, tau)

  AutA_rel[1,1] = n  # the order of tau

  K = C.Ka
  @vprint :ClassField 2 "... need to extend $(ngens(g)) from the cyclo ext\n"
  for i=1:ngens(g)
    si = Hecke.NfRelToNfRelMor{nf_elem, nf_elem}(C.Kr, C.Kr, gen(C.Kr)^Int(lift(mg(g[i]))))
    @vprint :ClassField 2 "... extending zeta -> zeta^$(mg(g[i]))\n"
    sigma = _extend_auto(A, Hecke.NfToNfMor(K, K, 
                                      C.mp[1](si(preimage(C.mp[1], gen(K))))))
    push!(AutA_gen, sigma)

#    pe = 17*gen(K) + gen(A)
#    @assert sigma(tau(pe)) - tau(sigma(pe)) == 0
#    @assert sigma(tau(pe)) == tau(sigma(pe))
 
    @vprint :ClassField 2 "... finding relation ...\n"
    m = gen(A)
    for j=1:Int(order(g[i]))
      m = sigma(m)
    end
    # now m SHOULD be tau^?(gen(A)), so sigma^order(g[i]) = tau^?
    # the ? is what I want...
    j = 0
    local zeta_i::nf_elem = (inv(zeta)^div(e, n))::nf_elem
    local mi::nf_elem = coeff(m, 1)
    @hassert :ClassField 1 m == mi*gen(A) 

    while mi != 1
      mi *= zeta_i
      j += 1
      @assert j <= e
    end
    @vprint :ClassField 2 "... as tau^$(j) == sigma_$i^$(order(g[i]))\n"
    AutA_rel[i+1, 1] = -j
    AutA_rel[i+1, i+1] = order(g[i])
  end
  CF.AutG = AutA_gen
  CF.AutR = AutA_rel
  
  AutA = GrpAbFinGen(AutA_rel)
  AutA_snf, mp = snf(AutA)
  @vprint :ClassField 2 "Automorphism group (over ground field) $AutA\n"

 
  # now we need a primitive element for A/k
  # mostly, gen(A) will do
  @vprint :ClassField 2 "Searching for primitive element...\n"
  pe = gen(A) + 0*gen(C.Ka)
  Auto=Dict{Hecke.GrpAbFinGenElem, Any}()
  cnt = 0
  while true
    @vprint :ClassField 3 "candidate: $pe\n"
    Im = Set{Hecke.NfRelElem{nf_elem}}()
    for j = AutA
      im = grp_elem_to_map(AutA_gen, j, pe)
      if im in Im
        pe += gen(C.Ka)
        cnt += 1
        if cnt > 100
          error("", Im, CF)
        end
        break
      else
        push!(Im, im)
      end
      Auto[j]=im
    end
    if length(Im) == order(AutA)
      break
    end
  end
  @vprint :ClassField 2 "have primitive element!!!  "
  @vprint :ClassField 3 " $pe"
  @vprint :ClassField 2 "\nnow the fix group...\n"

  if iscyclic(AutA_snf)  # the subgroup is trivial to find!
    @vprint :ClassField 2 ".. trivial as automorphism group is cyclic\n"
    s, ms = sub(AutA_snf, [e*AutA_snf[1]], false)
  else
    @vprint :ClassField 2 ".. interesting...\n"
    #want: hom: AutA = Gal(A/k) -> Gal(K/k) = domain(mq)
    # idea: take primes p in k and compare
    #  Frob(p, A/k) and preimage(mq, p)
    @assert n == degree(CF.K)
    Zk = order(_modulus(CF.mq))
    function canFrob(p)
      lP = Hecke.prime_decomposition_nonindex(C.mp[2], p)
      P = lP[1][1]
      Q = lP[end][1]
      F,  mF = ResidueField(order(P), P)
      Ft, t = PolynomialRing(F)
      mFp = extend_easy(mF, C.Ka)
      ap = mFp(CF.a)
      Ap = ResidueRing(Ft, t^n-ap)
      
      function toAp(x) # x in CF.K
        xp = zero(Ft)
        @assert coeff(x, n) == 0
        for i=0:n-1
          setcoeff!(xp, i, mFp(coeff(x, i)))
        end
        return Ap(xp)
      end

#      @assert length(Set([toAp(v) for (k,v) = Auto])) == length(Auto)
#TODO: bad prime possible if set is too small (pe might interfere with p)
      imF = toAp(pe)^norm(p)
      for (ky,v) = Auto
        kp = toAp(v)
        if kp == imF
          return ky
        end
      end
      error("Frob not found")
    end
    @vprint :ClassField 2 "finding Artin map...\n"
#TODO can only use non-indx primes, easy primes...
    @vtime :ClassField 2 lp, f = find_gens(MapFromFunc(canFrob, IdealSet(Zk), AutA),
                      PrimesSet(200, -1), minimum(_modulus(CF.mq)))
    h = hom(f, [preimage(CF.mq, p) for p = lp])
    @hassert :ClassField 1 issurjective(h)
    h = h*mp
    h = hom(AutA_snf, [h(AutA_snf[i]) for i=1:ngens(AutA_snf)])
    s, ms = kernel(h)
    @vprint :ClassField 2 "... done, have subgroup!\n"
  end
 
  #now, hopefully either norm or trace will be primitive for the target
  #norm, trace relative to s, the subgroup

  @vprint :ClassField 2 "computing orbit of primitive element\n"
  os = [Auto[mp(ms(j))] for j=s]

  function coerce_down(a)
    @assert a.data.length <= 1
    b = coeff(a, 0)
    c = preimage(C.mp[1], b)
    @assert c.data.length <= 1
    return coeff(c, 0)
  end

  function minpoly(a)
    @vtime :ClassField 2 o = [grp_elem_to_map(AutA_gen, mp(mq(j)), t) for j = q]
    @vtime :ClassField 2 f = prod(T-x for x=o)
    @assert degree(f) == length(o)
    @assert length(o) == e
    @vtime :ClassField 2 g = [coerce_down(coeff(f, i)) for i=0:Int(e)]
    return PolynomialRing(parent(g[1]))[1](g)
  end

#  n = prod(os) # maybe primitive??  
  @vprint :ClassField 2 "trying relative trace\n"
  t = sum(os)
  CF.pe = t
  #now the minpoly of t - via Galois as this is easiest to implement...
  q, mq = quo(AutA_snf, [ms(s[i]) for i=1:ngens(s)], false)
  @assert order(q) == order(domain(CF.mq))
  AT, T = PolynomialRing(A, "T")
  @vprint :ClassField 2 "char poly...\n"
  f = minpoly(t)
  @vprint :ClassField 2 "... done\n"
  if !issquarefree(f)
    @vprint :ClassField 2 "trying relative trace of squares\n"
    for i=1:length(os)
      os[i] *= os[i]
    end
    t = sum(os)
    CF.pe = t
    #now the minpoly of t - via Galois as this is easiest to implement...
    q, mq = quo(AutA_snf, [ms(s[i]) for i=1:ngens(s)], false)
    @assert order(q) == order(domain(CF.mq))
    AT, T = PolynomialRing(A, "T")
    @vprint :ClassField 2 "char poly...\n"
    f = minpoly(t)
    @vprint :ClassField 2 "... done\n"
    @assert issquarefree(f)
  end  

  CF.A = number_field(f)[1]
  nothing
end

function grp_elem_to_map(A::Array, b::Hecke.GrpAbFinGenElem, pe)
  res = pe
  for i=1:length(A)
    if b[i] == 0
      continue
    end
    for j=1:b[i]
      res = A[i](res)
    end
  end
  return res
end

function _reduce(a::fq_nmod)
  A = parent(a)
  if a.length < 2*degree(A)
    ccall((:fq_nmod_reduce, :libflint), Void, (Ptr{fq_nmod}, Ptr{FqNmodFiniteField}), &a, &A)
  else
    ccall((:nmod_poly_rem, :libflint), Void, (Ptr{fq_nmod}, Ptr{fq_nmod}, Ptr{Void}, Ptr{Void}), &a, &a, pointer_from_objref(A)+6*sizeof(Int) + 2*sizeof(Ptr{Void}), pointer_from_objref(A)+sizeof(fmpz))
  end
end

#TODO: move elsewhere - and use. There are more calls to nmod_set/reduce
function (A::FqNmodFiniteField)(x::nmod_poly)
  u = A()
  ccall((:fq_nmod_set, :libflint), Void,
                     (Ptr{fq_nmod}, Ptr{nmod_poly}, Ptr{FqNmodFiniteField}),
                                     &u, &x, &A)
  _reduce(u)
#  ccall((:fq_nmod_reduce, :libflint), Void, (Ptr{fq_nmod}, Ptr{FqNmodFiniteField}), &u, &A)                                   
  return u
end

function _nf_to_fq!(a::fq_nmod, b::nf_elem, K::FqNmodFiniteField, a_tmp::nmod_poly)
  nf_elem_to_nmod_poly_den!(a_tmp, b)
  ccall((:fq_nmod_set, :libflint), Void,
                     (Ptr{fq_nmod}, Ptr{nmod_poly}, Ptr{FqNmodFiniteField}),
                                     &a, &a_tmp, &K)
  _reduce(a)
#  ccall((:fq_nmod_reduce, :libflint), Void, (Ptr{fq_nmod}, Ptr{FqNmodFiniteField}), &a, &K)                                   
end
  

doc"""
   extend_easy(f::Hecke.NfOrdToFqNmodMor, K::AnticNumberField) -> NfToFqNmodMor
> For a residue field map from a prime ideal, extend the domain of the map
> to the entire field.
> Requires the prime ideal to be coprime to the index, unramified and
> over a small integer.
> Will throw a {{{BadPrime}}} exception if applied to an element in the 
> field with a $p$ in the denominator or with valuation $>0$.
> Also applies to {{{FacElem{nf_elem}}}}.
"""
function extend_easy(f::Hecke.NfOrdToFqNmodMor, K::AnticNumberField)
  nf(domain(f)) != K && error("Number field is not the number field of the order")

  O = domain(f) #used for the hassert and thus the testing
  z = Hecke.NfToFqNmodMor()
  z.header.domain = K
  z.header.codomain = f.header.codomain

  p = characteristic(z.header.codomain)
  y = f(NfOrdElem(domain(f), gen(K)))
  Ft, t = PolynomialRing(ResidueRing(FlintZZ, UInt(p)))
  K = number_field(domain(f))
#  g = gcd(Ft(K.pol), Ft(K(f.P.gen_two)))
#it would be cool to assert that g is the poly defining the codomain
  qm1 = size(codomain(f))-1

  function _image(x::NfOrdElem)
    return f(x)
  end

  Fq = codomain(f)
  s = Fq()
  t = Ft()

  function _image(x::nf_elem)
    m = den(x)
    if m %p == 0
      throw(BadPrime(p))
    end
    return Fq(Ft(x)) 
  end


  function _image(x::FacElem{nf_elem, AnticNumberField})
    r = one(Fq)
    for (k, v) = x.fac
      if v == 0 || v%qm1 == 0
        continue
      end
      if den(k) % p == 0
        throw(BadPrime(p))
      end
      _nf_to_fq!(s, k, Fq, t)
      if iszero(s)
        throw(BadPrime(p))
      end
      vr = v % qm1
      if vr < 0
        vr = (-vr) %qm1
        ccall((:fq_nmod_inv, :libflint), Void, (Ptr{fq_nmod}, Ptr{fq_nmod}, Ptr{FqNmodFiniteField}), &s, &s, &Fq)
      end
      ccall((:fq_nmod_pow, :libflint), Void, (Ptr{fq_nmod}, Ptr{fq_nmod}, Ptr{fmpz}, Ptr{FqNmodFiniteField}), &s, &s, &vr, &Fq)
      mul!(r, r, s)
    end
    @hassert :ClassField 3 r == f(O(evaluate(x)))
    return r
  end

  function _preimage(x::fq_nmod)
    return elem_in_nf(preimage(f, x))
  end

  z.header.image = _image
  z.header.preimage = _preimage

  return z
end

doc"""
    reduce_mod_powers(a::nf_elem, n::Int) -> nf_elem
    reduce_mod_powers(a::nf_elem, n::Int, primes::Array{NfOrdIdl, 1}) -> nf_elem
> Given some non-zero algebraic integeri $\alpha$, try to find  $\beta$ s.th.
> $\beta$ is "small" and $\alpha/\beta$ is an $n$-th power.
> If the factorisation of $a$ into prime ideals is known, the ideals
> should be passed in.
"""
function reduce_mod_powers(a::nf_elem, n::Int)
  M = maximal_order(parent(a))
  p = factor(M(a)*M)
  return reduce_mod_powers(a, n, collect(keys(p)))
end

function reduce_mod_powers(a::nf_elem, n::Int, primes::Array{NfOrdIdl, 1})
  # works quite well if a is not too large. There has to be an error
  # somewhere in the precision stuff...
  @vprint :ClassField 2 "reducing modulo $(n)-th powers\n"
  @vprint :ClassField 3 "starting with $a\n"
  Zk = maximal_order(parent(a))
  val = [ div(valuation(a, x), n) for x = primes if !isone(x)]
  if all(x->x==0, val)
    I = ideal(maximal_order(parent(a)), 1)
  else
    I = prod([primes[x]^val[x] for x=1:length(primes)])
  end
  Iinv = inv(I)

  p = 100
  old = precision(BigFloat)
  r1, r2 = signature(parent(a))
  no = abs(norm(a))
  l = Int[]
  while true
   if p > 40000
      error("Something wrong in reduce_mod_powers")
    end
    setprecision(BigFloat, p)
    l = Int[]
    try
      fn = log2(BigFloat(no))/n/degree(parent(a))
      m = Hecke.minkowski(a, p)
      for i=1:r1
        push!(l, Int(BigInt(round(fn - 1/n*log2(abs(m[i]))))))
      end
      for i=1:r2
        v = Int(BigFloat(round(fn - 1/2*1/n*log2((m[r1+2*i-1]^2 + m[r1+2*i]^2)))))
        push!(l, v)
        push!(l, v)
      end
    catch e
      p *= 2
      continue
    end
    if abs(sum(l)) <= length(l) 
      try
        b = Hecke.short_elem(Iinv, -matrix(FlintZZ, 1, length(l), l), prec=p)
      catch e
        if e != Hecke.LowPrecisionLLL() 
          rethrow(e)
        end
        p *= 2
        if p> 40000
          println("\n\nELT\n\n", a, "\n\nn: $n $primes\n\n")
          error("too much prec")
        end
        continue
      end
#=
  N(x) = prox x_i 
  N(x)^(2/n) <= 1/n sum x_i^2 <= 1/n 2^((n-1)/2) disc^(1/n) (LLL)
 so
  N(x) <= (2^((n-1)/4)/n)^(n/2) disc^(1/2)
=#
      if abs(norm(b)//norm(Iinv)) <= abs(discriminant(Zk)) 
        c = a*b^n
        @vprint :ClassField 3 "leaving with $c\n"
        return c
      end
      println("bad norm")
      println(abs(norm(b)//norm(Iinv)))
      println("should be")
      println(abs(discriminant(Zk)))
    end
    p *= 2
    if p> 40000
      println("abs sum ", l)
      error("too much prec")
    end
  end
  b = Hecke.short_elem(Iinv, -matrix(FlintZZ, 1, length(l), l), prec=p)
  c = a*b^n
  @vprint :ClassField 3 "leaving with $c\n"
  return c
end

function reduce_mod_powers(a::FacElem{nf_elem, AnticNumberField}, n::Int, primes::Array{NfOrdIdl, 1})
  lp = Dict((p, valuation(a, p)) for p = primes)
  b = compact_presentation(a, n, decom = lp)
  b = prod([k for (k,v) = b.fac if v == 1])
  return b  
end

function reduce_mod_powers(a::FacElem{nf_elem, AnticNumberField}, n::Int)
  global last_data = a
  Zk = maximal_order(base_ring(a))
  lp = factor_coprime(a, IdealSet(Zk))
  return reduce_mod_powers(a, n, collect(keys(lp)))
end

doc"""
   factor_coprime(a::FacElem{nf_elem, AnticNumberField}, I::NfOrdIdlSet) -> Dict{NfOrdIdl, fmpz}
> Factors the rincipal ideal generated by $a$ into coprimes by computing a coprime
> basis from the principal ideals in the factorisation of $a$.
"""
function factor_coprime(a::FacElem{nf_elem, AnticNumberField}, I::NfOrdIdlSet)
  Zk = order(I)
  A = Dict{NfOrdIdl, fmpz}()
  for (e,v) = a.fac
    N, D = integral_split(ideal(Zk, e))
    if !isone(N)
      if haskey(A, N)
        A[N] += v
      else
        A[N] = v
      end
    end
    if !isone(D)
      if haskey(A, D)
        A[D] -= v
      else
        A[D] = -v
      end
    end
  end
  if length(A) == 0
    A[ideal(Zk, 1)] = 1
  end
  return factor_coprime(FacElem(A))
end

doc"""
  factor(a::nf_elem, I::NfOrdIdlSet) -> Dict{NfOrdIdl, fmpz}
> Factors the principal ideal generated by $a$.
"""
function factor(a::nf_elem, I::NfOrdIdlSet)
  return factor(ideal(order(I),  a))
end

doc"""
  factor(a::FacElem{nf_elem, AnticNumberField}, I::NfOrdIdlSet) -> Dict{NfOrdIdl, fmpz}
> Factors the principal ideal generated by $a$ by refinind a coprime factorisation.
"""
function factor(a::FacElem{nf_elem, AnticNumberField}, I::NfOrdIdlSet)
  cp = factor_coprime(a, I)
  f = Dict{NfOrdIdl, fmpz}()
  for (I, v) = cp
    lp = factor(I)
    for (p, e) = lp
      f[p] = e*f
    end
  end
  return f
end

doc"""
   factor(a::fmpq, ::FlintIntegerRing) -> Fac{fmpz}
> Factor the rational number $a$ into prime numbers
"""
function factor(a::fmpq, ::FlintIntegerRing)
  fn = factor(num(a))
  fd = factor(den(a))
  for (p,e) = fd.fac
    fn.fac[p] = -e
  end
  return fn
end

function rel_auto(A::ClassField_pp)
  # sqrt[n](a) -> zeta sqrt[n](a) on A.A
  @assert isdefined(A, :A)
  #on A.K, the Kummer: sqrt[n](a) = gen(A.K) -> zeta gen(A.K)
  #we have the embedding A.A -> A.K : gen(A.A) -> A.pe
  M = SMat(base_ring(A.K))
  b = A.K(1)
  push!(M, SRow(b))
  for i=2:degree(A)
    b *= A.pe
    push!(M, SRow(b))
  end
  tau = NfRelToNfRelMor(A.K, A.K, A.bigK.zeta*gen(A.K))
  N = SRow(tau(A.pe))
  C = cyclotomic_extension(base_field(A), degree(A))
  Mk = _expand(M, C.mp[1])
  Nk = _expand(N, C.mp[1])
  s = solve(Mk, Nk) # will not work, matrix non-square...
  im = A.A()
  r = degree(C.Kr)
  for (i, c) = s
    @assert i % r == 0
    setcoeff!(im, div(i, r)-1, c)
  end

  return NfRelToNfRelMor(A.A, A.A, im)
end

function rel_auto(A::ClassField)
  aut = [rel_auto(x) for x = A.cyc]
  K = number_field(A)
  g = gens(K)
  Aut = []
  for i=1:length(aut)
    push!(Aut, NfRel_nsToNfRel_nsMor(K, K, [j==i ? aut[i].prim_img.data(g[j]) : g[j] for j=1:length(aut)]))
  end
  return Aut
end

function extend_aut(A::ClassField, tau::T) where T <: Map
  # tau: k       -> k
  k = domain(tau)
  @assert k == codomain(tau)
  @assert k == base_field(A)
  lp = factor(fmpz(degree(A)))
  all_h = [A.A() for x=A.cyc]
  for (p, v) = lp.fac
#    println("doin' $p^$v")
    Cp = [Ap for Ap = A.cyc if degree(Ap) % Int(p) == 0]
    i = 1
    om = 0
    im = 0
    while i <= length(Cp)
      if degree(Cp[i]) > om
        om = degree(Cp[i])
        im = i
      end
      i += 1
    end
    #now Cp[im] is of maximal exponent - hence, it should have the maximal
    # big Kummer extension. By construction (above), the set of s-units
    # SHOULD guarantee this....
    # Now I want all generators in terms of this large Kummer field.
    #
    # Idea: similar to pSelmer in Magma:
    #  look at frob(p, k(zeta_n)(sqrt[n](a)))(sqrt[n](a)):
    #  sqrt[n](a) -> zeta_n^i sqrt[n](a) = sqrt[n](a)^N(p) mod p
    # so N(p) = en+f => f = 1 (otherwise the congruence cannot work)
    # zeta_n^i = a^e mod p for any prime p in k(zeta_n)
    # since a = S-Unit (mod n-th powers) I can compare frob(p, a) to
    # the frob(sqrt[n](U_S)) and find the presentation:
    # next, we want the "same" for sqrt[n](tau(a)).
    # Given, that can_frob is kind of non-cheap, we want to be clever
    # zeta_n^i = tau(a)^e mod p =>
    # tau^-1(zeta_n)^i = a^e mod tau^-1(p) or
    # zeta_n^(ij) = a^e mod tau^-1(p)
    # So: need j = j(tau) and the permutation on lp...
    # in particular, tau need to be extened to k(zeta_n)
    # Cheat: g = Kr.pol => g(zeta) = 0
    #  tau(g)(zeta^r) = 0 for some suitable r
    # then zeta -> zeta^r should be a valid extension....
    #
    # TODO: Don't use the bigK.gen (the full s-units), just use the 
    # group generated by the .a, the various Kummer generators, lifted
    # to the large cyclotomic extension.
    C = cyclotomic_extension(k, Int(om))
    g = C.Kr.pol
    tau_g = parent(g)([tau(coeff(g, i)) for i=0:degree(g)])
#    println("g: $g")
#    println("tau(g): $tau_g")
    i = 1
    z = gen(C.Kr)
    while gcd(i, om) != 1 || !iszero(tau_g(z))
      i *= 1
      z *= gen(C.Kr) 
    end
    z_i = i

    z_i_inv = invmod(z_i, om)
#println("z_i: $z_i")
    Tau = NfRelToNfRelMor(C.Kr, C.Kr, tau, z)
    tau_Ka = NfToNfMor(C.Ka, C.Ka, C.mp[1](Tau(C.mp[1]\gen(C.Ka))))
    #TODO: need the inverse of this or similar...
    # currently, this is not used as it did not work.

    lp = collect(keys(Cp[im].bigK.frob_cache))
    use_p = []
    z = matrix(FlintZZ, 0, length(Cp[im].bigK.gen), fmpz[])
    tau_z = matrix(FlintZZ, 0, length(Cp[im].bigK.gen), fmpz[])
    for p = lp
      local f
      local tau_f
      try
        f = can_frobenius(p, Cp[im].bigK).coeff
        tau_f = can_frobenius(induce_image(p, tau_Ka), Cp[im].bigK).coeff
      catch e
        if typeof(e) != BadPrime
          rethrow(e)
        end
      end
      z = vcat(z, f)
      tau_z = vcat(tau_z, tau_f)
      push!(use_p, p)
    end
#    println("z: $z")
#    println("tau(z): $tau_z")
    z = hcat(z, om*identity_matrix(FlintZZ, rows(z)))
    tau_z = hcat(tau_z, om*identity_matrix(FlintZZ, rows(z)))
    @assert C.Ka == base_ring(Cp[im].K)

    all_s = []
    all_tau_s = []
    all_emb = []
    for c in Cp
#      println("om: $om -> ", degree(c))
      Cs = cyclotomic_extension(k, Int(degree(c)))
      Emb = NfRelToNfRelMor(Cs.Kr, C.Kr, gen(C.Kr)^div(om, degree(c)))
      emb = C.mp[1] * Emb * inv(Cs.mp[1])
      a = FacElem(Dict(emb(k) => v for (k,v) = c.a.fac))
      tau_a = FacElem(Dict(tau_Ka(k) => v for (k,v) = a.fac))
      push!(all_emb, (a, tau_a, emb))
      y = matrix(FlintZZ, length(use_p), 1, [div(om, degree(c))*can_frobenius(p, Cp[im].bigK, a) for p = use_p])
      y = matrix(FlintZZ, length(use_p), 1, [can_frobenius(p, Cp[im].bigK, a) for p = use_p])
#      println("raw y: ", y')
      fl, s = cansolve(z, y)
      @assert fl
      s = [mod(s[x, 1], om) for x=1:length(Cp[im].bigK.gen)]
      #println("s: $s")

      y = matrix(FlintZZ, length(use_p), 1, [can_frobenius(p, Cp[im].bigK, tau_a) for p = use_p])
#      println("raw y: ", y')
      fl, tau_s = cansolve(z, y)
#      println((tau_z*tau_s)')
      @assert fl
      tau_s = [(z_i_inv*tau_s[x, 1]) % om for x=1:length(Cp[im].bigK.gen)]
#      println("tau(s): $tau_s")
      y = matrix(FlintZZ, length(use_p), 1, [can_frobenius(p, Cp[im].bigK, tau_a) for p = use_p])

      # so a = s -> z_i^-1 * tau_s = tau(a) (mod n) :
      push!(all_s, s)
      push!(all_tau_s, tau_s)
    end
    sG, msG = sub(Cp[im].bigK.AutG, [Cp[im].bigK.AutG(x) for x=all_s], false)
    all_b = []
    # if the above is correct, then tau_s in <s>
    for j = 1:length(Cp)
      sG, msG = sub(Cp[im].bigK.AutG, [Cp[im].bigK.AutG(all_s[x]) for x=1:length(all_s)], false)
      sG, msG = sub(Cp[im].bigK.AutG, vcat([(degree(Cp[j]) > om ? div(om, degree(Cp[i])):1)*Cp[im].bigK.AutG(all_s[x]) for x=1:length(all_s)], [degree(Cp[j])*Cp[im].bigK.AutG[x] for x=1:ngens(Cp[im].bigK.AutG)]), false)
      ts = all_tau_s[j]
      x = Cp[im].bigK.AutG(ts)
      fl, y = haspreimage(msG, x)
#      println(fl, " -> $(x.coeff) -> $(y.coeff)")
      @assert fl
      #need to establish the embeddings (which are also needed below)
#      println([Int(y[i]) for i=1:length(Cp)])
#      println(div(om, degree(Cp[j])))
      mu = prod(all_emb[i][1]^Int(y[i]) for i=1:length(Cp)) * inv(all_emb[j][2])
      mmu = evaluate(mu)
#      global last_rt = (mmu, degree(Cp[j]))
      rt = root(mmu, degree(Cp[j]))
      push!(all_b, (rt, y))
    end
    Ka = C.Ka
    KaT, X = Ka["T"]
    KK, gKK = number_field([X^degree(Cp[j]) - evaluate(all_emb[j][1]) for j=1:length(Cp)])
    h = NfRel_nsToNfRel_nsMor(KK, KK, tau_Ka, [inv(all_b[i][1])*prod(gKK[j]^Int(divexact(all_b[i][2][j], div(om, degree(Cp[j])))) for j=1:length(Cp)) for i=1:length(Cp)])

    # now "all" that remains is to restrict h to the subfield, using lin. alg..
    # .. and of course move away form the Cp stuff.

    #TODO: better (more efficient) maps from NfRel -> NfRel_ns in case
    # we're using only one generator
    #Similar: NfRel_ns -> NfRel_ns small gens set -> large gens set
    all_pe =[]
    for j=1:length(Cp)
      emb = NfRelToNfRel_nsMor(Cp[j].K, KK, all_emb[j][3], gens(KK)[j])
#      println("start:")
#      println(gen(Cp[j].K), " -> ", emb(gen(Cp[j].K)))
#      println(Cp[j].K.pol, " -> ", minpoly(emb(gen(Cp[j].K))))
      pe = emb(Cp[j].pe)
      tau_pe = h(pe)
#      println("$(Cp[j].pe) pe: $pe -> $tau_pe")
#      println(norm(minpoly(Cp[j].pe)))
#      println(norm(minpoly(pe)))
#      println(norm(minpoly(tau_pe)))
#      println("=======")
      push!(all_pe, (pe, tau_pe))
    end


    B = [KK(1), all_pe[1][1]]
    d = degree(Cp[1])
    while length(B) < degree(Cp[1])
      push!(B, B[end]*all_pe[1][1])
    end
  

    for j=2:length(Cp)
      d *= degree(Cp[j])
      D = copy(B)
      while length(B) < d
        D = [x*all_pe[j][1] for x = D]
        append!(B, D)
      end
    end
    M = SMat(Ka)
    for i=1:d
      push!(M, SRow(B[i]))
    end
    AA, gAA = number_field([c.A.pol for c = Cp])
    @assert d == degree(AA)
    @assert d == length(B)
    b_AA = basis(AA)
    Mk = _expand(M, C.mp[1])
    @hassert :ClassField 2 nullspace(Mk')[1] == 0
    all_im = NfRel_nsElem{nf_elem}[]
    for j=1:length(Cp)
      N = SRow(all_pe[j][2])
      Nk = _expand(N, C.mp[1])
       n = solve(Mk, Nk)
      im = sum(v*b_AA[i] for (i, v) = n)
      push!(all_im, im)
    end
    im = NfRel_nsElem{nf_elem}[]
    i = 1
    j = 1
    while j<=length(A.cyc)
      if i<= length(Cp) && degree(A.cyc[j]) == degree(Cp[i])
        push!(im, gens(A.A)[j])
        i += 1
        j += 1
      else
        j += 1
      end
    end
    emb = NfRel_nsToNfRel_nsMor(KK, A.A, im)
    i = 1
    j = 1
    while j<=length(A.cyc)
      if i<= length(Cp) && degree(A.cyc[j]) == degree(Cp[i])
        all_h[j] = emb(all_im[i])
        i += 1
        j += 1
      else
        j += 1
      end
    end
  end
  return NfRel_nsToNfRel_nsMor(A.A, A.A, tau, all_h)
end

#M is over K, mp: K -> K/k, expand M into a matrix over k
function _expand(M::Generic.Mat{nf_elem}, mp::Map)
  Kr = domain(mp)
  Ka = codomain(mp)
  k = base_ring(Kr)
  d = degree(Kr)
  N = zero_matrix(k, rows(M), cols(M) * d)
  for i=1:rows(M)
    for j = 1:cols(M)
      a = mp\M[i,j]
      for k=0:d-1
        N[i, (j-1)*d+k+1] = coeff(a, k)
      end
    end
  end
  return N
end

function _expand(M::SRow{nf_elem}, mp::Map)
  Kr = domain(mp)
  k = base_ring(Kr)
  d = degree(Kr)
  sr = SRow(k)
  for (j, v) = M
    a = mp\v
    for l=0:d-1
      c = coeff(a, l)
      if !iszero(c)
        push!(sr.pos, (j-1)*d+1+l+1)
        push!(sr.values, c)
      end
    end
  end
  return sr
end

function _expand(M::SMat{nf_elem}, mp::Map)
  Kr = domain(mp)
  k = base_ring(Kr)
  N = SMat(k)
  for i=1:rows(M)
    sr = _expand(M[i], mp)
    push!(N, sr)
  end
  return N
end

doc"""
  base_ring(A::ClassField)
> The maximal order of the field that $A$ is defined over.
"""
function base_ring(A::ClassField)
  return order(_modulus(A.mq))
end

doc"""
  base_field(A::ClassField)
> The number field that $A$ is defined over.
"""
function base_field(A::ClassField)
  return number_field(base_ring(A))
end

function base_ring(A::ClassField_pp)
  return order(_modulus(A.mq))
end

function base_field(A::ClassField_pp)
  return number_field(base_ring(A))
end

doc"""
  degree(A::ClassField)
> The degree of $A$ over its base field, ie. the size of the defining ideal group.
"""
function degree(A::ClassField)
  return Int(order(domain(A.mq)))
end

function degree(A::ClassField_pp)
  return Int(order(domain(A.mq)))
end

