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
  fl, b = hasroot(a, degree(K))
  @assert fl

  return NfRelToNfRelMor{nf_elem, nf_elem}(K, K, h, 1//b*gen(K)^r)
end


@inline function number_field(O::NfOrd)
  return O.nf
end

#TODO: extend mF to FacElem - hopefully it applies to nf_elem at all
#TODO: allow mF to fail grateously
#TODO: extend mF to nf_elem where this makes sense

function can_frobenius(p::NfOrdIdl, K::KummerExt)
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
  return K.AutG(aut)
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

function _modulus(mR::Map)
  while issubtype(typeof(mR), Hecke.CompositeMap)
    mR = mR.f
  end
  if issubtype(typeof(mR), Hecke.MapClassGrp)
    return ideal(order(codomain(mR)), 1)
  elseif issubtype(typeof(mR), Hecke.MapRayClassGrpFacElem)
    return mR.modulus_fin
  end
  @assert issubtype(typeof(mR), Hecke.MapRayClassGrp)
  return mR.modulus_fin
end

######################################################################
#mR: SetIdl -> GrpAb (inv of ray_class_group or Frobenius or so)
#TODO: remove gens that are redundant.
function find_gens(mR::Map, S::PrimesSet, cp::fmpz=fmpz(1))
  ZK = order(domain(mR))

  R = codomain(mR) 

  sR = elem_type(R)[]
  lp = elem_type(domain(mR))[]

  st = start(S)
  np = 0
  extra = 0

  q, mq = quo(R, sR)
  while true
    p, st = next(S, st)
    if cp % p == 0
      continue
    end
    @vprint :ClassField 2 "doin` $p\n"
    np += 1

    if false && np > 5*ngens(R)
      error("cannot stop")
    end
    if np % ngens(R) == 0
      println("cannot stop")
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
      #TODO check if already contained...
      if iszero(mq(f))
        continue
      end
      push!(sR, f)
      push!(lp, P)
      q, mq = quo(R, sR)
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
  k = nf(Zk)
  @assert k == domain(mp)
  Qx = parent(k.pol)

  Sp = Hecke.PrimesSet(200, -1, c.n, 1) #primes = 1 mod n, so totally split in cyclo

  lp, sG = find_gens(cf, Sp, cp)

  R = domain(mR) 
  G = codomain(cf)
  sR = elem_type(R)[]

  for P = lp
    p = intersect_nonindex(mp, P)
    push!(sR, valuation(norm(P), norm(p))*preimage(mR, p))
  end
  @assert order(quo(G, sG)[1]) == 1
       # if think if the quo(G, ..) == 1, then the other is automatic
       # it is not, in general it will never be.
       #example: Q[sqrt(10)], rcf of 16*Zk
  # now the map G -> R sG[i] -> sR[i] 
  h = hom(sG, sR)
  return h
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
    q, mq = quo(domain(m), p)
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
  if isdefined(CF, :cyc)
    return [x.A.pol for x = CF.cyc]
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
      S, mQ = quo(G, q)
      push!(res, ray_class_field_cyclic_pp(m*inv(mQ)))
    end
    q[i] = G[i]
  end
  CF.cyc = res
  return [x.A.pol for x = CF.cyc]
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

  q, mq = quo(c, e)
  mc = mc*inv(mq)
  c = q

  lf = factor(minimum(f)*e)
  lP = Hecke.NfOrdIdl[]
  for p = keys(lf.fac)
    lp = prime_decomposition(ZK, Int(p))  #TODO: make it work for fmpz
    lP = vcat(lP, [x[1] for x = lp])
  end
  g = elem_type(c)[preimage(mc, x) for x = lP]

  q, mq = quo(c, g)
  mc = mc * inv(mq)
  c = q

  lP = vcat(lP, Hecke.find_gens(inv(mc), PrimesSet(100, -1))[1])

  @vprint :ClassField 2 "using $lP of length $(length(lP)) for s-units\n"

  @vtime :ClassField 2 S, mS = Hecke.sunit_group_fac_elem(lP)
  @vprint :ClassField 2 "... done\n"
  @vtime :ClassField 2 KK = kummer_extension(Int(e), [mS(S[i]) for i=1:ngens(S)])

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
  M = MatrixSpace(R, ngens(k), ngens(G))()
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
  s, ms = sub(N, GrpAbFinGenElem[sum([n[j, k]*N[j] for j=1:rows(n)]) for k=1:i])
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
               
  mq = CF.mq
  e = Int(order(domain(mq)))
  k = nf(order(codomain(mq)))
  C = cyclotomic_extension(k, e)
  A = CF.K
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
    s, ms = sub(g, [x for x = g if iszero(f(gen(C.Kr)^Int(mg(x))))])
    g = s
    mg = mg*ms
  end

  @vprint :ClassField 2 "building automorphism group over ground field...\n"

  AutA_gen = []
  AutA_rel = MatrixSpace(FlintZZ, ngens(g)+1, ngens(g)+1)()
  zeta = C.mp[1](gen(C.Kr))
  n = degree(A)
  @assert e % n == 0

  @vprint :ClassField 2 "... the trivial one (Kummer)\n"
  tau = Hecke.NfRelToNfRelMor{nf_elem,  nf_elem}(A, A, zeta^div(e, n)*gen(A))
  push!(AutA_gen, tau)

  AutA_rel[1,1] = n  # the order of tau
  zeta  = C.mp[1](gen(C.Kr))
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
    for j=1:order(g[i])
      m = sigma(m)
    end
    # now m SHOULD be tau^?(gen(A)), so sigma^order(g[i]) = tau^?
    # the ? is what I want...
    j = 0
    zeta_i = inv(zeta)^div(e, n)
    mi = coeff(m, 1) 
    @hassert :ClassField 1 iszero(m-mi*gen(A))
    @hassert :ClassField 2 m == mi*gen(A)  # there is a bug in RelNf
                            # or the underlying ResidueRing
                            # I've got a non-simplified coeff
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
    @vprint :ClassField 2 "candidate: $pe\n"
    Im = Set{Hecke.NfRelElem{nf_elem}}()
    for j = AutA
      im = grp_elem_to_map(AutA_gen, j, pe)
      if im in Im
        pe += gen(C.Ka)
        cnt += 1
        if cnt > 100
          error("")
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
  @vprint :ClassField 2 "have primitive element!!! $pe\n"
  @vprint :ClassField 2 "now the fix group...\n"

  if iscyclic(AutA_snf)  # the subgroup is trivial to find!
    @vprint :ClassField 2 ".. trivial as automorphism group is cyclic\n"
    s, ms = sub(AutA_snf, [e*AutA_snf[1]])
  else
    @vprint :ClassField 2 ".. interesting...\n"
    #want: hom: AutA = Gal(A/k) -> Gal(K/k) = domain(mq)
    # idea: take primes p in k and compare
    #  Frob(p, A/k) and preimage(mq, p)
    @assert n == degree(CF.K)
    Zk = maximal_order(k)
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
    @vtime :ClassField 2 lp, f = find_gens(MapFromFunc(canFrob, IdealSet(maximal_order(k)), AutA),
                      PrimesSet(200, -1), minimum(_modulus(CF.mq)))
    h = hom(f, [preimage(CF.mq, p) for p = lp])
    @hassert :ClassField 1 issurjective(h)
    h = h*inv(mp)
    h = hom(AutA_snf, [h(AutA_snf[i]) for i=1:ngens(AutA_snf)])
    s, ms = kernel(h)
    @vprint :ClassField 2 "... done, have subgroup!\n"
  end
 
  #now, hopefully either norm or trace will be primitive for the target
  #norm, trace relative to s, the subgroup

  @vprint :ClassField 2 "computing orbit of primitive element\n"
  os = [Auto[preimage(mp, ms(j))] for j=s]

  function coerce_down(a)
    @assert a.data.length <= 1
    b = coeff(a, 0)
    c = preimage(C.mp[1], b)
    @assert c.data.length <= 1
    return coeff(c, 0)
  end

  function minpoly(a)
    @vtime :ClassField 2 o = [grp_elem_to_map(AutA_gen, preimage(mp, mq(j)), t) for j = q]
    @vtime :ClassField 2 f = prod(T-x for x=o)
    @assert degree(f) == length(o)
    @assert length(o) == e
    @vtime :ClassField 2 g = [coerce_down(coeff(f, i)) for i=0:Int(e)]
    return PolynomialRing(parent(g[1]))[1](g)
  end

#  n = prod(os) # maybe primitive??  
  @vprint :ClassField 2 "trying relative trace\n"
  t = sum(os)
  #now the minpoly of t - via Galois as this is easiest to implement...
  q, mq = quo(AutA_snf, [ms(s[i]) for i=1:ngens(s)])
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
    #now the minpoly of t - via Galois as this is easiest to implement...
    q, mq = quo(AutA_snf, [ms(s[i]) for i=1:ngens(s)])
    @assert order(q) == order(domain(CF.mq))
    AT, T = PolynomialRing(A, "T")
    @vprint :ClassField 2 "char poly...\n"
    f = minpoly(t)
    @vprint :ClassField 2 "... done\n"
    @assert issquarefree(f)
  end  

  CF.A = number_field(minpoly(t))[1]
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

#TODO: move elsewhere - and use. There are more calls to nmod_set/reduce
function (A::FqNmodFiniteField)(x::nmod_poly)
  u = A()
  ccall((:fq_nmod_set, :libflint), Void,
                     (Ptr{fq_nmod}, Ptr{nmod_poly}, Ptr{FqNmodFiniteField}),
                                     &u, &x, &A)
  ccall((:fq_nmod_reduce, :libflint), Void, (Ptr{fq_nmod}, Ptr{FqNmodFiniteField}), &u, &A)                                   
  return u
end

function _nf_to_fq!(a::fq_nmod, b::nf_elem, K::FqNmodFiniteField, a_tmp::nmod_poly)
  nf_elem_to_nmod_poly_den!(a_tmp, b)
  ccall((:fq_nmod_set, :libflint), Void,
                     (Ptr{fq_nmod}, Ptr{nmod_poly}, Ptr{FqNmodFiniteField}),
                                     &a, &a_tmp, &K)
  ccall((:fq_nmod_reduce, :libflint), Void, (Ptr{fq_nmod}, Ptr{FqNmodFiniteField}), &a, &K)                                   
end
  

function extend_easy(f::Hecke.NfOrdToFqNmodMor, K::AnticNumberField)
  nf(domain(f)) != K && error("Number field is not the number field of the order")

  z = Hecke.NfToFqNmodMor()
  z.header.domain = K
  z.header.codomain = f.header.codomain

  p = characteristic(z.header.codomain)
  y = f(NfOrdElem(domain(f), gen(K)))
  Ft, t = PolynomialRing(ResidueRing(FlintZZ, p))
  K = number_field(domain(f))
#  g = gcd(Ft(K.pol), Ft(K(f.P.gen_two)))
#it would be cool to assert that g is the poly defining the codomain
  qm1 = size(codomain(f))-1

  function _image(x::NfOrdElem)
    return f(x)
  end

  Fq = codomain(f)

  function _image(x::nf_elem)
    m = den(x)
    if m %p == 0
      throw(BadPrime(p))
    end
    return Fq(Ft(x)) 
  end


  function _image(x::FacElem{nf_elem, AnticNumberField})
    r = one(Fq)
    s = Fq()
    t = Ft()
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
  val = [ div(valuation(a, x), n) for x = primes]
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
        b = Hecke.short_elem(Iinv, -Matrix(FlintZZ, 1, length(l), l), prec=p)
      catch e
        if e != Hecke.LowPrecisionLLL() 
          rethrow(e)
        end
        p *= 2
        if p> 40000
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
      if abs(norm(b)//norm(Iinv)) < abs(discriminant(Zk)) 
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
  b = Hecke.short_elem(Iinv, -Matrix(FlintZZ, 1, length(l), l), prec=p)
  c = a*b^n
  @vprint :ClassField 3 "leaving with $c\n"
  return c
end

function reduce_mod_powers(a::FacElem{nf_elem, AnticNumberField}, n::Int, primes::Array{NfOrdIdl, 1})
  b = evaluate(a)
  return reduce_mod_powers(b, n, primes)
end

function reduce_mod_powers(a::FacElem{nf_elem, AnticNumberField}, n::Int)
  b = evaluate(a)
  return reduce_mod_powers(b, n)
end

