export kummer_extension, ray_class_field, hilbert_class_field, prime_decomposition_type, defining_modulus

add_verbose_scope(:ClassField)
add_assert_scope(:ClassField)
#set_assert_level(:ClassField, 1)


function kummer_extension(n::Int, gen::Array{nf_elem, 1})
  g = [FacElem(x) for x=gen]
  return kummer_extension(n, g)
end

###############################################################################
#
#  Ray Class Field, number_field interface and reduction to prime power case
#
###############################################################################

@doc Markdown.doc"""
    ray_class_field(m::MapClassGrp) -> ClassField
    ray_class_field(m::MapRayClassGrp) -> ClassField
> Creates the (formal) abelian extension defined by the map $m: A \to I$
> where $I$ is the set of ideals coprime to the modulus defining $m$ and $A$ 
> is a quotient of the ray class group (or class group). The map $m$
> must be the map returned from a call to {class_group} or {ray_class_group}.
"""
function ray_class_field(m::Union{MapClassGrp, MapRayClassGrp})
  return ray_class_field(m, GrpAbFinGenMap(domain(m)))
end

@doc Markdown.doc"""
    ray_class_field(m::Union{MapClassGrp, MapRayClassGrp}, quomap::GrpAbFinGenMap) -> ClassField
> For $m$ a map computed by either {ray_class_group} or {class_group} and
> $q$ a canonical projection (quotient map) as returned by {quo} for q 
> quotient of the domain of $m$ and a subgroup of $m$, create the
> (formal) abelian extension where the (relative) automorphism group
> is canonically isomorphic to the codomain of $q$.
"""
function ray_class_field(m::Union{MapClassGrp, MapRayClassGrp}, quomap::GrpAbFinGenMap)
  CF = ClassField()
  CF.rayclassgroupmap = m
  S, mS = snf(codomain(quomap))
  CF.quotientmap = Hecke._compose(inv(mS), quomap)
  #CF.mq = Hecke.make_snf(Hecke._compose(m, inv(quomap)))
  return CF
end

@doc Markdown.doc"""
    NumberField(CF::ClassField) -> Hecke.NfRel_ns{Nemo.nf_elem}
> Given a (formal) abelian extension, compute the class field by
> finding defining polynomials
> for all prime power cyclic subfields.
> Note, by type this is always a non-simple extension.
"""
function NumberField(CF::ClassField)
  if isdefined(CF, :A)
    return CF.A
  end
  
  res = ClassField_pp[]
  G = codomain(CF.quotientmap)
  @assert issnf(G)
  q = [G[i] for i=1:ngens(G)]
  for i=1:ngens(G)
    o = order(G[i])
    lo = factor(o)
    for (p, e) = lo.fac
      q[i] = p^e*G[i]
      S, mQ = quo(G, q, false)
      push!(res, ray_class_field_cyclic_pp(CF, mQ))
    end
    q[i] = G[i]
  end
  CF.cyc = res
  CF.A = number_field([x.A.pol for x = CF.cyc])[1]
  return CF.A
end

function ray_class_field_cyclic_pp(CF::ClassField, mQ::GrpAbFinGenMap)
  @vprint :ClassField 1 "cyclic prime power class field of degree $(degree(CF))\n"
  CFpp = ClassField_pp()
  #CFpp.mq = _compose(CF.mq, inv(mQ))
  CFpp.quotientmap = _compose(mQ, CF.quotientmap)
  CFpp.rayclassgroupmap = CF.rayclassgroupmap
  @assert domain(CFpp.rayclassgroupmap) == domain(CFpp.quotientmap)
  @vprint :ClassField 1 "finding the Kummer extension...\n"
  @vtime :ClassField 1 _rcf_find_kummer(CFpp)
  @vprint :ClassField 1 "reducing the generator...\n"
  @vtime :ClassField 1 _rcf_reduce(CFpp)
  @vprint :ClassField 1 "descending ...\n"
  @vtime :ClassField 1 _rcf_descent(CFpp)
  return CFpp
end

###############################################################################
#
#  Computation of Frobenius automorphisms
#
###############################################################################

# the Frobenius at p in K:
#K is an extension of k, p a prime in k,
#returns a vector in (Z/nZ)^r representing the Frob
function can_frobenius(p::NfOrdIdl, K::KummerExt)
  @assert norm(p) % K.n == 1
  if haskey(K.frob_cache, p)
    return K.frob_cache[p]
  end
  Zk = order(p)
  if index(Zk) % minimum(p) == 0 
    #index divisors and residue class fields don't agree
    # ex: x^2-10, rcf of 29*Zk, 7. 239 is tricky...
    throw(BadPrime(p))
  end

  if nbits(minimum(p)) > 64
    error("Oops")
  end

  F, mF = ResidueFieldSmall(Zk, p)
  mF = extend_easy(mF, number_field(Zk))

  # K = sqrt[n](gen), an automorphism will be
  # K[i] -> zeta^? K[i]
  # Frob(sqrt[n](a), p) = sqrt[n](a)^N(p) (mod p) = zeta^r sqrt[n](a)
  # sqrt[n](a)^N(p) = a^(N(p)-1 / n) = zeta^r mod p

  z_p = inv(mF(Zk(K.zeta)))

  ex = div(norm(p)-1, K.n)
  aut = Array{fmpz,1}(undef, length(K.gen))
  for j=1:length(K.gen)
    mu = mF(K.gen[j])^ex  # can throw bad prime!
    i = 0
    while !isone(mu)
      i += 1
      @assert i <= K.n
      mul!(mu, mu, z_p)
    end
    aut[j]= fmpz(i)
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

  if nbits(minimum(p)) > 64
    error("Oops")
  end

  F, mF = ResidueFieldSmall(Zk, p)
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
    @assert i <= K.n
    mul!(mu, mu, z_p)
  end
  return i
end


###############################################################################
#
#  Find small generator of class group
#
###############################################################################

function find_gens(mR::Map, S::PrimesSet, cp::fmpz=fmpz(1))
# mR: SetIdl -> GrpAb (inv of ray_class_group or Frobenius or so)
  ZK = order(domain(mR))
  R = codomain(mR) 
  sR = GrpAbFinGenElem[]
  lp = elem_type(domain(mR))[]

  #st = start(S)
  local q, mq, np, extra
  np = 0
  extra = 1

  #q, mq = quo(R, sR, false)
  for p in S
    q, mq = quo(R, sR, false)
  #while true
    #p, st = next(S, st)
    if cp % p == 0 || index(ZK) % p ==0
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



###############################################################################
#
#  First step: Find the Kummer extension over the cyclotomic field
#
###############################################################################
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



# mR: GrpAb A -> Ideal in k, only preimage used
# cf: Ideal in K -> GrpAb B, only image
# mp:: k -> K inclusion
# builds a (projection) from B -> A identifying (pre)images of
# prime ideals, the ideals are coprime to cp and ==1 mod n

#function build_map(mR::Map, K::KummerExt, c::CyclotomicExt)
function build_map(CF::ClassField_pp, K::KummerExt, c::CyclotomicExt)
  #mR should be GrpAbFinGen -> IdlSet
  #          probably be either "the rcg"
  #          or a compositum, where the last component is "the rcg"
  # we need this to get the defining modulus - for coprime testing
  m = defining_modulus(CF)[1]
  ZK = maximal_order(base_ring(K.gen[1]))
  cp = lcm(minimum(m), discriminant(ZK))
  
  cf = Hecke.MapFromFunc(x->can_frobenius(x, K), IdealSet(ZK), K.AutG)

  mp = c.mp[2]
  cp = lcm(cp, index(maximal_order(domain(mp))))
  ZK = maximal_order(c.Ka)
  @hassert :ClassField 1 order(domain(cf)) == ZK
  Zk = order(m)
  Id_Zk = Hecke.NfOrdIdlSet(Zk)
  k = nf(Zk)
  @hassert :ClassField 1 k == domain(mp)

  Sp = Hecke.PrimesSet(200, -1, c.n, 1) #primes = 1 mod n, so totally split in cyclo

  lp, sG = find_gens(cf, Sp, cp)
  G = codomain(cf)
  sR = Array{GrpAbFinGenElem, 1}(undef, length(lp))

  for i=1:length(lp)
    p = Id_Zk(intersect_nonindex(mp, lp[i]))
    sR[i]= valuation(norm(lp[i]), norm(p))*CF.quotientmap(preimage(CF.rayclassgroupmap, p))
  end
  @hassert :ClassField 1 order(quo(G, sG, false)[1]) == 1
       # if think if the quo(G, ..) == 1, then the other is automatic
       # it is not, in general it will never be.
       #example: Q[sqrt(10)], rcf of 16*Zk
  # now the map G -> R sG[i] -> sR[i] 
  h = hom(sG, sR)
  return h
end

function _s_unit_for_kummer(mc::Map, ZK::NfOrd, e::Int, f::fmpz)
  #This function finds a set S of primes such that we can find a Kummer generator in it.
  lP = Hecke.NfOrdIdl[]
  if f != 1
    lf = factor(f)  
    for p = keys(lf.fac)
       #I have to remove the primes that can't be in the conductor
       lp = prime_decomposition(ZK, p)  #TODO: make it work for fmpz
       for (P, s) in lp
         if gcd(norm(P), e) != 1 || gcd(norm(P)-1, e) != 1
           push!(lP, P)
         end 
       end
    end
  end
  g = GrpAbFinGenElem[preimage(mc, x) for x = lP]

  q, mq = quo(domain(mc), g, false)
  mc = compose(inv(mq), mc)
  
  lP = vcat(lP, find_gens(inv(mc), PrimesSet(100, -1))[1])
  @vprint :ClassField 2 "using $lP of length $(length(lP)) for S-units\n"
#if false
#  println("enlarging to be Galois closed - just in case...", length(lP))
#  lP = Set(lP)
#  _lp = Set(minimum(x) for x = lP)
#  for p = _lp
#    fp = prime_decomposition(ZK, Int(p))
#    for I = fp
#      push!(lP, I[1])
#    end
#  end
#  lP = collect(lP)
#  println("finally:", length(lP))
#end
  if isempty(lP)
    U, mU = unit_group_fac_elem(ZK)
    @vtime :ClassField 2 KK = kummer_extension(e, [mU(U[i]) for i=1:ngens(U)])
  else
    @vtime :ClassField 2 S, mS = Hecke.sunit_group_fac_elem(lP)
    @vtime :ClassField 2 KK = kummer_extension(e, [mS(S[i]) for i=1:ngens(S)])
  end
  
  return lP::Array{NfOrdIdl, 1}, KK
end

function _rcf_find_kummer(CF::ClassField_pp)

  if isdefined(CF, :K)
    return CF.K
  end
  f = defining_modulus(CF)[1]::NfOrdIdl
  @vprint :ClassField 2 "Kummer extension ... with conductor(?) $f\n"
  k1 = nf(order(f))
  e = degree(CF)::Int 
  @assert Hecke.isprime_power(e)

  @vprint :ClassField 2 "Adjoining the root of unity\n"
  C = cyclotomic_extension(k1, e)
  K = C.Ka

  @vprint :ClassField 2 "Maximal order of cyclotomic extension\n"
  ZK = maximal_order(K)
  
  @vprint :ClassField 2 "Class group of cyclotomic extension\n"
  @vtime :ClassField 2 c, mc = class_group(ZK)
  allow_cache!(mc)
  @vprint :ClassField 2 "... $c\n"
  c, mq = quo(c, e, false)
  mc = _compose(mc, inv(mq))
  
  lP, KK = _s_unit_for_kummer(mc, ZK, e, minimum(f))
  CF.bigK = KK
  CF.sup = lP
  @vprint :ClassField 2 "building Artin map for the large Kummer extension\n"
  @vtime :ClassField 2 h = build_map(CF, KK, C)
  @vprint :ClassField 2 "... done\n"

  k, mk = kernel(h) 
  G = domain(h)
  
  # Now, we find the kummer generator by considering the action 
  # of the automorphisms on the s-units
  # x needs to be fixed by k
  # that means x needs to be in the kernel:
  # x = prod gen[1]^n[i] -> prod (z^a[i] gen[i])^n[i]
  #                            = z^(sum a[i] n[i]) x
  # thus it works iff sum a[i] n[i] = 0
  # for all a in the kernel
  R = ResidueRing(FlintZZ, C.n, cached=false)
  M = MatrixSpace(R, ngens(k), ngens(G), false)(mk.map)
  i, l = nullspace(M)
  @assert i > 0
  n = lift(l)::fmpz_mat
  N = GrpAbFinGen([e for j=1:rows(n)])
  s, ms = sub(N, GrpAbFinGenElem[sum([n[j, k]*N[j] for j=1:rows(n)]) for k=1:i], false)
  ms = Hecke.make_snf(ms)
  H = domain(ms)
  @hassert :ClassField 1 iscyclic(H)
  o = Int(order(H))
  c = 1
  if o < e
    c = div(e, o)
  end
  g = ms(H[1])
  @vprint :ClassField 2 "final $n of order $o and e=$e\n"
  a = prod([KK.gen[i]^div(mod(g[i], e), c) for i=1:ngens(N)])
  @vprint :ClassField 2 "generator $a\n"
  CF.a = a
  
  CF.sup_known = true
  CF.o = o
  CF.defect = c
#  CF.K = pure_extension(Int(o), a)[1] #needs to evaluate a - too expensive!
  return nothing
end



###############################################################################
#
#  Descent to K
#
###############################################################################


function _find_prim_elem(A::NfRel, AutA_gen::Array{NfRelToNfRelMor{nf_elem,  nf_elem},1}, AutA::GrpAbFinGen, oA::fmpz, C::CyclotomicExt)
  pe = gen(A)# + 0*gen(C.Ka)
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
          error("Too many attempts to find primitive elements")
        end
        break
      else
        push!(Im, im)
      end
      Auto[j]=im
    end
    if length(Im) == oA
      break
    end
  end
  @vprint :ClassField 2 "have primitive element!!!  "
  @vprint :ClassField 3 " $pe"
  
  return pe, Auto
end

function _aut_A_over_k(C::CyclotomicExt, CF::ClassField_pp)
  
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
  e = degree(CF)
  g, mg = unit_group(ResidueRing(FlintZZ, e, cached=false))
  @assert issnf(g)
  #mg = Hecke.make_snf(mg)
  @assert (e%8 == 0 && ngens(domain(mg))==2) ||
           ngens(domain(mg)) <= 1

  if degree(C.Kr) < order(g)  # there was a common subfield, we
                              # have to pass to a subgroup
    @assert order(g) % degree(C.Kr) == 0
    f = C.Kr.pol
    # Can do better. If the group is cyclic (e.g. if p!=2), we already know the subgroup!
    s, ms = sub(g, [x for x in g if iszero(f(gen(C.Kr)^Int(lift(mg(x)))))], false)
    ss, mss = snf(s)
    g = ss
    #mg = mg*ms*mss
    mg = mss * ms * mg
  end

  @vprint :ClassField 2 "building automorphism group over ground field...\n"

  AutA_gen = Hecke.NfRelToNfRelMor{nf_elem,  nf_elem}[]
  AutA_rel = zero_matrix(FlintZZ, ngens(g)+1, ngens(g)+1)
  zeta = C.mp[1](gen(C.Kr))
  n = degree(A)
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
    sigma = _extend_auto(A, Hecke.NfToNfMor(K, K, C.mp[1](si(preimage(C.mp[1], gen(K))))))
    push!(AutA_gen, sigma)

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
  return nothing
  
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

  return NfRelToNfRelMor(K, K, h, 1//b*gen(K)^r)
end

function _rcf_descent(CF::ClassField_pp)
  if isdefined(CF, :A)
    return CF.A
  end

  @vprint :ClassField 2 "Descending ...\n"
               
  e = degree(CF)
  k = nf(order(codomain(CF.rayclassgroupmap)))
  C = cyclotomic_extension(k, e)
  A = CF.K
  n = degree(A)
  #@vprint :ClassField 2 "Automorphism group (over ground field) $AutA\n"
  _aut_A_over_k(C, CF)
  
  AutA_gen = CF.AutG
  AutA = GrpAbFinGen(CF.AutR)
  AutA_snf, mp = snf(AutA)
  # now we need a primitive element for A/k
  # mostly, gen(A) will do
  @vprint :ClassField 2 "Searching for primitive element...\n"
  pe, Auto = _find_prim_elem(A::NfRel, AutA_gen, AutA, order(AutA_snf), C)
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
    Zk = order(defining_modulus(CF)[1])
    function canFrob(p::NfOrdIdl)
      lP = Hecke.prime_decomposition_nonindex(C.mp[2], p)
      P = lP[1][1]
      Q = lP[end][1]
      F, mF = ResidueFieldSmall(order(P), P)
      Ft, t = PolynomialRing(F, cached=false)
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
                      PrimesSet(200, -1), lcm(minimum(defining_modulus(CF)[1]), index(maximal_order(codomain(C.mp[2])))))
    h = hom(f, [image(CF.quotientmap, preimage(CF.rayclassgroupmap, p)) for p = lp])
    @hassert :ClassField 1 issurjective(h)
    h = _compose(mp, h)
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
    return PolynomialRing(parent(g[1]), cached = false)[1](g)
  end

#  n = prod(os) # maybe primitive??  
  @vprint :ClassField 2 "trying relative trace\n"
  @assert length(os) > 0
  t = zero(parent(os[1]))
  for o in os
    t = t + o
  end

  #t = sum(os)
  CF.pe = t
  #now the minpoly of t - via Galois as this is easiest to implement...
  q, mq = quo(AutA_snf, [ms(s[i]) for i=1:ngens(s)], false)
  @assert order(q) == degree(CF)
  AT, T = PolynomialRing(A, "T", cached = false)
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
    @assert order(q) == degree(CF)
    AT, T = PolynomialRing(A, "T", cached = false)
    @vprint :ClassField 2 "char poly...\n"
    f = minpoly(t)
    @vprint :ClassField 2 "... done\n"
    @assert issquarefree(f)
  end  

  CF.A = number_field(f)[1]
  return nothing
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

@doc Markdown.doc"""
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
  Ft, t = PolynomialRing(ResidueRing(FlintZZ, UInt(p), cached=false), cached=false)
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
    m = denominator(x)
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
      if denominator(k) % p == 0
        throw(BadPrime(p))
      end
      _nf_to_fq!(s, k, Fq, t)
      if iszero(s)
        throw(BadPrime(p))
      end
      vr = v % qm1
      if vr < 0
        vr = (-vr) %qm1
        ccall((:fq_nmod_inv, :libflint), Nothing, (Ref{fq_nmod}, Ref{fq_nmod}, Ref{FqNmodFiniteField}), s, s, Fq)
      end
      ccall((:fq_nmod_pow, :libflint), Nothing, (Ref{fq_nmod}, Ref{fq_nmod}, Ref{fmpz}, Ref{FqNmodFiniteField}), s, s, vr, Fq)
      mul!(r, r, s)
    end
#too expensive - and automatically used in test
#    @hassert :ClassField 3 r == f(O(evaluate(x)))
    return r
  end

  function _preimage(x::fq_nmod)
    return elem_in_nf(preimage(f, x))
  end

  z.header.image = _image
  z.header.preimage = _preimage

  return z
end

###############################################################################
#
#  Reduction of generators
#
###############################################################################

function _rcf_reduce(CF::ClassField_pp)
  #e = order(codomain(CF.quotientmap))
  e = degree(CF)
  e = CF.o
  if CF.sup_known
    CF.a = reduce_mod_powers(CF.a, e, CF.sup)
    CF.sup_known = false
  else
    CF.a = reduce_mod_powers(CF.a, e)
  end
  CF.K = pure_extension(CF.o, CF.a)[1]
  return nothing
end

@doc Markdown.doc"""
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
  N(x) = prod x_i 
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

function reduce_mod_powers(a::FacElem{nf_elem, AnticNumberField}, n::Int, decom::Dict{NfOrdIdl, Int})
  b = compact_presentation(a, n, decom = decom)
  b = prod([k^(v % n) for (k,v) = b.fac if !iszero(v % n)])
  b *= denominator(b, maximal_order(parent(b)))^n  #non-optimal, but integral...
  return FacElem(b)  
end

function reduce_mod_powers(a::FacElem{nf_elem, AnticNumberField}, n::Int, primes::Array{NfOrdIdl, 1})
  lp = Dict((p, Int(valuation(a, p))) for p = primes)
  return reduce_mod_powers(a, n, lp)
  return b  
end

function reduce_mod_powers(a::FacElem{nf_elem, AnticNumberField}, n::Int)
  Zk = maximal_order(base_ring(a))
  lp = factor_coprime(a, IdealSet(Zk))
  return reduce_mod_powers(a, n, Dict((p, Int(v)) for (p, v) = lp))
end

###############################################################################
#
#  Automorphisms of abelian extension
#
###############################################################################

function rel_auto_easy(A::ClassField_pp)
  
  # sqrt[n](a) -> zeta sqrt[n](a) on A.A
  #on A.K, the Kummer: sqrt[n](a) = gen(A.K) -> zeta gen(A.K)
  #we have the embedding A.A -> A.K : gen(A.A) -> A.pe
  M = sparse_matrix(base_ring(A.K))
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
    setcoeff!(im, i-1, c)
  end
  return NfRelToNfRelMor(A.A, A.A, im)
  
end

function rel_auto_intersection(A::ClassField_pp)
  
  # In the computation of the class field, I saved the 
  # automorphisms of A.K over k.
  # Now, I have to search for the one that generates the Galois
  # group of the target field over k
  C = cyclotomic_extension(base_field(A), degree(A))
  a = ispower(degree(A))[2]
  @assert isprime(a)
  exp_to_test = divexact(degree(A), a)
  r = degree(C.Kr)
  if !isdefined(A, :AutG)
    _aut_A_over_k(C, A)
  end
  #Now, I restrict them to A.A
  M = sparse_matrix(base_ring(A.K))
  b = A.K(1)
  push!(M, SRow(b))
  for i=2:degree(A)
    b *= A.pe
    push!(M, SRow(b))
  end
  Mk = _expand(M, C.mp[1])
  i = 0
  # One of the automorphisms must generate the group, so I check the order.
  for j=1:length(A.AutG)
    tau = A.AutG[j]
    N = SRow(tau(A.pe))
    Nk = _expand(N, C.mp[1])
    s = solve(Mk, Nk) # will not work, matrix non-square...
    im = A.A()
    for (i, c) = s
      setcoeff!(im, i-1, c)
    end
    aut = NfRelToNfRelMor(A.A, A.A, im)
    pow_aut = aut^exp_to_test
    if pow_aut(gen(A.A)) != gen(A.A)
      return aut
    end
  end
  error("I can't find the automorphism!")
 
end

function rel_auto(A::ClassField_pp)
  
  @assert isdefined(A, :A)
  
  if degree(A) == degree(A.K)
    #If the cyclotomic extension and the target field are linearly disjoint, it is easy.
    return rel_auto_easy(A)
  else
    #Tricky case
    return rel_auto_intersection(A)
  end
end

function rel_auto(A::ClassField)
  aut = NfRelToNfRelMor[rel_auto(x) for x = A.cyc]
  K = number_field(A)
  g = gens(K)
  Aut = NfRel_nsToNfRel_nsMor[]
  for i=1:length(aut)
    push!(Aut, NfRel_nsToNfRel_nsMor(K, K, [j==i ? aut[i].prim_img.data(g[j]) : g[j] for j=1:length(aut)]))
  end
  return Aut
end


###############################################################################
#
#  Extension of automorphisms from the base field to the class field
#
###############################################################################

#Special case in which I want to extend the automorphisms of a field to
# a cyclotomic extension
function extend_to_cyclotomic(C::CyclotomicExt, tau::NfToNfMor)		
   		
  K = domain(tau)		
  @assert K == base_ring(C.Kr)		
  g = C.Kr.pol		
  tau_g = parent(g)([tau(coeff(g, i)) for i=0:degree(g)])		
  i = 1		
  z = gen(C.Kr)		
  while gcd(i, C.n) != 1 || !iszero(tau_g(z))		
    i *= 1		
    z *= gen(C.Kr) 		
  end		
  return NfRelToNfRelMor(C.Kr, C.Kr, tau, z)		
  		
end

function extend_aut(A::ClassField, tau::T) where T <: Map
  # tau: k       -> k
  #global last_extend = (A, tau)
  k = domain(tau)
  @assert k == codomain(tau)
  @assert k == base_field(A)
  lp = factor(fmpz(degree(A)))
  all_h = [A.A() for x in A.cyc]
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
    # now Cp[im] is of maximal exponent - hence, it should have the maximal
    # big Kummer extension. By construction (above), the set of s-units
    # SHOULD guarantee this....
    # om defintely has the maximal base field, ie. the most roots of 1.
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
    # currently the bigK.gen are needed to ensure enough primes are used:
    # in general, since the degrees of the Kummer extensions can drop when moved
    # to the larger cyclotomic field, we cannot use the degrees of the components
    # as a check. (Try enough primes until the Frobenius generate the full group
    # but we don't know the group.)
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

    Tau = NfRelToNfRelMor(C.Kr, C.Kr, tau, z)
    tau_Ka = NfToNfMor(C.Ka, C.Ka, C.mp[1](Tau(C.mp[1]\gen(C.Ka))))
    #TODO: need the inverse of this or similar...
    # currently, this is not used as it did not work.

    lp = collect(keys(Cp[im].bigK.frob_cache))
    pp = maximum(minimum(x) for x = lp)
    S = Base.Iterators.flatten((lp, PrimeIdealsSet(order(lp[1]), pp, fmpz(-1), indexdivisors=false, ramified=false, degreebound = 1)))

    @assert C.Ka == base_ring(Cp[im].K)

    all_s = []
    all_tau_s = []
    all_emb = []
    for c in Cp
#      println("om: $om -> ", degree(c), " vs ", c.o)
      Cs = cyclotomic_extension(k, Int(degree(c)))
      Emb = NfRelToNfRelMor(Cs.Kr, C.Kr, gen(C.Kr)^div(om, degree(c)))
      emb = inv(Cs.mp[1]) * Emb * C.mp[1]
      a = FacElem(Dict(emb(k) => v for (k,v) = c.a.fac))
      tau_a = FacElem(Dict(tau_Ka(k) => v for (k,v) = a.fac))
      push!(all_emb, (a, tau_a, emb, divexact(om, c.o)))
    end

    G = DiagonalGroup([om for i=1:length(Cp[im].bigK.gen)])
    Q, mQ = quo(G, elem_type(G)[])
    U = DiagonalGroup([om for i = Cp])
    s_gen = elem_type(U)[]
    tau_gen = elem_type(U)[]

    for p = S
      local f
      local fa
      local tfa
      try
        f = can_frobenius(p, Cp[im].bigK).coeff
        fa = [can_frobenius(p, Cp[im].bigK, a[1]) for a = all_emb]
        tfa =[can_frobenius(p, Cp[im].bigK, a[2]) for a = all_emb]
      catch e
        if typeof(e) != BadPrime
          rethrow(e)
        end
        continue
      end
      el = mQ(G(f))
      if iszero(el)
        continue
      end
      Q, mmQ = quo(Q, [el])
      mQ = mQ*mmQ
      push!(s_gen, U(fa))
      push!(tau_gen, U(tfa))
      if order(Q) == 1
        break
      end
    end

    T_grp = DiagonalGroup([om for i= s_gen])
    t_gen = [T_grp([x[i] for x = s_gen]) for i=1:length(Cp)]
    t_tau_gen = [T_grp([x[i] for x = tau_gen]) for i=1:length(Cp)]
    t_corr = [gcd(content(x.coeff), om) for x = t_gen]
    #if any entry in t_corr is != 1, then the degree of the kummer
    #extension has to be lower:
    #support C2 x C8, the generator for the C2 is in the Cylo(8),
    #thus over the larger base field, the extension is trivial
    all_b = []
    for i=1:length(Cp)
      q, mq = quo(T_grp, divexact(Cp[i].o, Int(t_corr[i])))
      @assert domain(mq) == T_grp
      _, ms = sub(q, [mq(x) for x = t_gen])
      fl, lf = haspreimage(ms, mq(t_tau_gen[i]))
      @assert fl
      mu = prod(all_emb[j][1]^lf[j] for j=1:length(Cp)) * inv(all_emb[i][2])
      fl, rt = ispower(mu, divexact(Cp[i].o, Int(t_corr[i])))
      @assert fl
      push!(all_b, (evaluate(rt), lf))
    end
    
    Ka = C.Ka
    KaT, X = PolynomialRing(Ka, "T", cached = false)
    KK, gKK = number_field([X^Int(divexact(Cp[j].o, t_corr[j])) - root(evaluate(all_emb[j][1]), Int(t_corr[j])) for j=1:length(Cp)])
    s = []
    for i in 1:length(Cp)
      _s = gKK[1]
      _s = _s^Int(divexact(om, divexact(Cp[i].o, t_corr[i]))*all_b[i][2][1])
      for j in 2:length(Cp)
        _s = _s * gKK[j]^Int(divexact(om, divexact(Cp[i].o, t_corr[i]))*all_b[i][2][j])
      end
      push!(s, _s)
    end
    h = NfRel_nsToNfRel_nsMor(KK, KK, tau_Ka, [inv(all_b[i][1]) * s[i] for i=1:length(Cp)])

    # now "all" that remains is to restrict h to the subfield, using lin. alg..
    # .. and of course move away form the Cp stuff.

    #TODO: better (more efficient) maps from NfRel -> NfRel_ns in case
    # we're using only one generator
    #Similar: NfRel_ns -> NfRel_ns small gens set -> large gens set
    all_pe =[]
    for jj=1:length(Cp)
      emb = NfRelToNfRel_nsMor(Cp[jj].K, KK, all_emb[jj][3], gens(KK)[jj])
#      println("start:")
#      println(gen(Cp[jj].K), " -> ", emb(gen(Cp[jj].K)))
#      println(Cp[jj].K.pol, " -> ", minpoly(emb(gen(Cp[jj].K))))
      pe = emb(Cp[jj].pe)
      tau_pe = h(pe)
#      println("$(Cp[jj].pe) pe: $pe -> $tau_pe")
#      println(norm(minpoly(Cp[jj].pe)))
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
  

    for jj=2:length(Cp)
      d *= degree(Cp[jj])
      D = copy(B)
      while length(B) < d
        D = [x*all_pe[jj][1] for x = D]
        append!(B, D)
      end
    end
    M = sparse_matrix(Ka)
    for i=1:d
      push!(M, SRow(B[i]))
    end
    AA, gAA = number_field([c.A.pol for c = Cp])
    @assert d == degree(AA)
    @assert d == length(B)
    b_AA = basis(AA)
    Mk = _expand(M, C.mp[1])
    #@hassert :ClassField 2 nullspace(Mk')[1] == 0
    all_im = NfRel_nsElem{nf_elem}[]
    for jj=1:length(Cp)
      N = SRow(all_pe[jj][2])
      Nk = _expand(N, C.mp[1])
      global last_solve = (Mk, Nk, M, N)
      n = solve(Mk, Nk)
      im = sum(v*b_AA[l] for (l, v) = n)
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

#now again, but for embeddnigs, not automorphisms

function extend_hom(A::ClassField, B::ClassField, tau::T) where T <: Map
  # tau: k1       -> k2
  #global last_extend = (A, tau)
  k1 = domain(tau)
  k2 = codomain(tau)
  @assert k1 == base_field(A)
  @assert k2 == base_field(B)
  @assert degree(B) % degree(A) == 0 #actually, this should hold for the exponent
  lp = factor(fmpz(degree(B)))
  all_h = [A.A() for x in A.cyc]
  for (p, v) = lp.fac
    println("doin' $p^$v")
    Cp = [Ap for Ap = A.cyc if degree(Ap) % Int(p) == 0]
    Dp = [Bp for Bp = B.cyc if degree(Bp) % Int(p) == 0]
    h = [extend_hom(X, Cp, tau) for x = Dp]
  end
end

function extend_hom(C::ClassField_pp, D::Array{ClassField_pp, 1}, tau)
    #if it works, then Cp -> Dp should also work
    k2 = codomain(tau)
    k1 = domain(tau)
    i = 1
    om = 0
    im = 0
    while i <= length(D)
      if degree(D[i]) > om
        om = degree(D[i])
        im = i
      end
      i += 1
    end
    # now Dp[im] is of maximal exponent - hence, it should have the maximal
    # big Kummer extension. By construction (above), the set of s-units
    # SHOULD guarantee this....
    # om defintely has the maximal base field, ie. the most roots of 1.
    # Now I want (the images) for all generators in terms of this large Kummer field.
    #
    Dy = cyclotomic_extension(k2, Int(om))
    Cy = cyclotomic_extension(k1, C.degree)
    g = Cy.Kr.pol
    tau_g = k2["x"][1]([tau(coeff(g, i)) for i=0:degree(g)])
    println("g: $g")
    println("tau(g): $tau_g")
    i = 1
    z = gen(Dy.Kr)
    while gcd(i, om) != 1 || !iszero(tau_g(z))
      i *= 1
      z *= gen(Dy.Kr) 
    end
    z_i = i

    z_i_inv = invmod(z_i, om)

    Tau = NfRelToNfRelMor(Cy.Kr, Dy.Kr, tau, z)
    @show tau_Ka = NfToNfMor(Cy.Ka, Dy.Ka, Dy.mp[1](Tau(Cy.mp[1]\gen(Cy.Ka))))

    lp = collect(keys(D[im].bigK.frob_cache))
    pp = maximum(minimum(x) for x = lp)
    S = Base.Iterators.flatten((lp, PrimeIdealsSet(order(lp[1]), pp, fmpz(-1), indexdivisors=false, ramified=false, degreebound = 1)))

    @assert Dy.Ka == base_ring(D[im].K)

    all_s = []
    all_tau_s = []
    all_emb = []
    for c in D
#      println("om: $om -> ", degree(c), " vs ", c.o)
      Cs = cyclotomic_extension(k2, Int(degree(c)))
      Emb = NfRelToNfRelMor(Cs.Kr, Dy.Kr, gen(Dy.Kr)^div(om, degree(c)))
      emb = inv(Cs.mp[1]) * Emb * Dy.mp[1]
      a = FacElem(Dict(emb(k) => v for (k,v) = c.a.fac))
      push!(all_emb, (a, emb, divexact(om, c.o)))
    end
    b = FacElem(Dict(tau_Ka(k) => v for (k,v) = C.a.fac))

    G = DiagonalGroup([om for i=1:length(D[im].bigK.gen)])
    Q, mQ = quo(G, elem_type(G)[])
    U = DiagonalGroup([om for i = D])
    s_gen = elem_type(U)[]
    tau_b = fmpz[]

    for p = S
      local f
      local fa
      local tfa
      try
        f = can_frobenius(p, D[im].bigK).coeff
        fa = [can_frobenius(p, D[im].bigK, a[1]) for a = all_emb]
        tfa = can_frobenius(p, D[im].bigK, b)
      catch e
        if typeof(e) != BadPrime
          rethrow(e)
        end
        continue
      end
      el = mQ(G(f))
      if iszero(el)
        continue
      end
      Q, mmQ = quo(Q, [el])
      mQ = mQ*mmQ
      push!(s_gen, U(fa))
      push!(tau_b, (tfa))
      if order(Q) == 1
        break
      end
    end

    T_grp = DiagonalGroup([om for i= s_gen])
    @show t_gen = [T_grp([x[i] for x = s_gen]) for i=1:length(D)]
    @show t_tau_g = T_grp(tau_b)
    @show t_corr = [gcd(content(x.coeff), om) for x = t_gen]
    @show t_corr_b = gcd(gcd(tau_b), om)
    @assert t_corr_b == 1
    #if any entry in t_corr is != 1, then the degree of the kummer
    #extension has to be lower:
    #support C2 x C8, the generator for the C2 is in the Cylo(8),
    #thus over the larger base field, the extension is trivial

    q, mq = quo(T_grp, divexact(C.o, Int(t_corr_b)))
    @assert domain(mq) == T_grp
    _, ms = sub(q, [mq(x) for x = t_gen])
    @show fl, lf = haspreimage(ms, mq(t_tau_g))
    @assert fl
    mu = prod(all_emb[j][1]^lf[j] for j=1:length(D)) * inv(b)
    fl, rt = ispower(mu, divexact(C.o, Int(t_corr_b)))
    @assert fl
    all_b = (evaluate(rt), lf)
    
    Ka = Dy.Ka
    KaT, X = PolynomialRing(Ka, "T", cached = false)
    KK, gKK = number_field([X^Int(divexact(D[j].o, t_corr[j])) - root(evaluate(all_emb[j][1]), Int(t_corr[j])) for j=1:length(D)])
    s = gKK[1]
    s = s^Int(divexact(D[1].o, C.o)*all_b[2][1])
    for j in 2:length(D)
      s = s * gKK[j]^Int(divexact(D[j].o, C.o)*all_b[2][j])
    end
    h = NfRelToNfRel_nsMor(C.K, KK, tau_Ka, inv(all_b[1]) * s)

    # now "all" that remains is to restrict h to the subfield, using lin. alg..

    all_pe = []
    for jj=1:length(D)
      emb = NfRelToNfRel_nsMor(D[jj].K, KK, tau_Ka, gens(KK)[jj])
      pe = emb(D[jj].pe)
      push!(all_pe, pe)
    end

    B = [KK(1), all_pe[1]]
    d = degree(D[1])
    while length(B) < degree(D[1])
      push!(B, B[end]*all_pe[1])
    end
  

    for jj=2:length(D)
      d *= degree(D[jj])
      _D = copy(B)
      while length(B) < d
        _D = [x*all_pe[jj] for x = _D]
        append!(B, _D)
      end
    end
    M = sparse_matrix(Ka)
    for i=1:d
      push!(M, SRow(B[i]))
    end
    AA, gAA = number_field([c.A.pol for c = D])
    @assert d == degree(AA)
    @assert d == length(B)
    b_AA = basis(AA)
    Mk = _expand(M, Dy.mp[1])
    #@hassert :ClassField 2 nullspace(Mk')[1] == 0
    N = SRow(h(C.pe))
    Nk = _expand(N, Dy.mp[1])
    n = solve(Mk, Nk)
    all_im = sum(v*b_AA[l] for (l, v) = n)

      return all_im

      #=

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
  =#
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
      for l=0:d-1
        N[i, (j-1)*d+l+1] = coeff(a, l)
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
        push!(sr.pos, (j-1)*d+1+l)
        push!(sr.values, c)
      end
    end
  end
  return sr
end

function _expand(M::SMat{nf_elem}, mp::Map)
  Kr = domain(mp)
  k = base_ring(Kr)
  N = sparse_matrix(k)
  for i=1:rows(M)
    sr = _expand(M[i], mp)
    push!(N, sr)
  end
  return N
end

###############################################################################
#
#  Modulus function
#
###############################################################################

@doc Markdown.doc"""
    defining_modulus(CF::ClassField)
> The modulus, ie. an ideal the the set of real places, used to create the
> class field.
"""
function defining_modulus(CF::ClassField)
  return _modulus(CF.rayclassgroupmap)
end 

function defining_modulus(CF::ClassField_pp)
  return _modulus(CF.rayclassgroupmap)
end 

function _modulus(mq::MapRayClassGrp)
  return mq.defining_modulus
end

function _modulus(mq::MapClassGrp)
  return (ideal(order(codomain(mq)), 1), InfPlc[])
end

###############################################################################
#
#  Auxiliary functions (to be moved)
#
###############################################################################

@doc Markdown.doc"""
  base_ring(A::ClassField)
> The maximal order of the field that $A$ is defined over.
"""
function base_ring(A::ClassField)
  return order(defining_modulus(A)[1])
end

@doc Markdown.doc"""
  base_field(A::ClassField)
> The number field that $A$ is defined over.
"""
function base_field(A::ClassField)
  return number_field(base_ring(A))
end

function base_ring(A::ClassField_pp)
  return order(defining_modulus(A)[1])
end

function base_field(A::ClassField_pp)
  return number_field(base_ring(A))
end

@doc Markdown.doc"""
  degree(A::ClassField)
> The degree of $A$ over its base field, ie. the size of the defining ideal group.
"""
function degree(A::ClassField)
  if A.degree==-1
    A.degree=Int(order(codomain(A.quotientmap)))
  end
  return A.degree
end

function degree(A::ClassField_pp)
  if A.degree==-1
    A.degree=Int(order(codomain(A.quotientmap)))
  end
  return A.degree
end

@doc Markdown.doc"""
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

@doc Markdown.doc"""
  factor(a::nf_elem, I::NfOrdIdlSet) -> Dict{NfOrdIdl, fmpz}
> Factors the principal ideal generated by $a$.
"""
function factor(a::nf_elem, I::NfOrdIdlSet)
  return factor(ideal(order(I),  a))
end

@doc Markdown.doc"""
  factor(a::FacElem{nf_elem, AnticNumberField}, I::NfOrdIdlSet) -> Dict{NfOrdIdl, fmpz}
> Factors the principal ideal generated by $a$ by refinind a coprime factorisation.
"""
function factor(a::FacElem{nf_elem, AnticNumberField}, I::NfOrdIdlSet)
  cp = factor_coprime(a, I)
  f = Dict{NfOrdIdl, fmpz}()
  for (I, v) = cp
    lp = factor(I)
    for (p, e) = lp
      f[p] = e*v
    end
  end
  return f
end

@doc Markdown.doc"""
   factor(a::fmpq, ::FlintIntegerRing) -> Fac{fmpz}
> Factor the rational number $a$ into prime numbers
"""
function factor(a::fmpq, ::FlintIntegerRing)
  fn = factor(numerator(a))
  fd = factor(denominator(a))
  for (p,e) = fd.fac
    fn.fac[p] = -e
  end
  return fn
end

@doc Markdown.doc"""
    islocal_norm(r::ClassField, a::NfAbsOrdElem, p::NfAbsOrdIdl) -> Bool
> Tests if $a$ is a local norm at $p$ in the extension implictly given by $r$.
> Currently the conductor cannot have infinite places.
"""
function islocal_norm(r::ClassField, a::NfAbsOrdElem, p::NfAbsOrdIdl)
  m0, minf = conductor(r)
  if length(minf) > 0
    error("not implemented yet")
  end
  m0 = defining_modulus(r)[1] #need the maps...
  @assert isprime(p)
  v1 = valuation(a, p)
  v2 = valuation(m0, p)
  n0 = divexact(m0, p^v2)
  o0 = p^(v1 + v2)
  y = crt(order(p)(1), n0, a, o0)
  y = y*order(p)
  y = divexact(y, p^v1)

  return isone(r.quotientmap(preimage(r.rayclassgroupmap, y)))
end

@doc Markdown.doc"""
    islocal_norm(r::ClassField, a::NfAbsOrdElem) -> Bool
> Tests if $a$ is a local norm at all finite places in the extension implictly given by $r$.
"""
function islocal_norm(r::ClassField, a::NfAbsOrdElem)
  K = base_field(r)
  m0, minf = conductor(r)
  if !ispositive(a, minf)
    return false
  end
  fl = factor(m0*a)
  return all(x -> islocal_norm(r, a, x), keys(fl))
end

function norm_group_map(R::ClassField, r::Array{ClassField, 1}, map = false)
  @assert map != false || all(x -> base_ring(R) == base_ring(x), r)
#  @assert map == false && all(x -> base_ring(R) == base_ring(x), r)

  mR = defining_modulus(R)[1]
  @assert map != false || all(x->mR+defining_modulus(x)[1] == defining_modulus(x)[1], r)

  fR = _compose(R.rayclassgroupmap, inv(R.quotientmap))
  lp, sR = find_gens(MapFromFunc(x->preimage(fR, x), IdealSet(base_ring(R)), domain(fR)),
                             PrimesSet(100, -1), minimum(mR))
  if map == false                           
    h = [hom(sR, [preimage(_compose(x.rayclassgroupmap, inv(x.quotientmap)), p) for p = lp]) for x = r]
  else
    h = [hom(sR, [preimage(_compose(x.rayclassgroupmap, inv(x.quotientmap)), map(p)) for p = lp]) for x = r]
  end
  return h
end

function norm_group_map(R::ClassField, r::ClassField, map = false)
  return norm_group_map(R, [r], map)[1]
end

@doc Markdown.doc"""
    compositum(a::ClassField, b::ClassField) -> ClassField
             *(a::ClassField, b::ClassField) -> ClassField
> The compositum of $a$ and $b$ as a (formal) class field.
"""
function compositum(a::ClassField, b::ClassField)
  @assert base_ring(a) == base_ring(b)
  c = lcm(defining_modulus(a)[1], defining_modulus(b)[1])
  d = lcm(degree(a), degree(b))
  c_inf = union(defining_modulus(a)[2], defining_modulus(b)[2])
  r, mr = ray_class_group(c, c_inf, n_quo = Int(d))
  C = ray_class_field(mr)
  @assert domain(C.rayclassgroupmap) == r
  h = norm_group_map(C, [a,b])
  U = intersect(kernel(h[1])[1], kernel(h[2])[1])
  q, mq = quo(codomain(C.quotientmap), U)
  return ray_class_field(mr, GrpAbFinGenMap(C.quotientmap * mq))
end

@doc Markdown.doc"""
  *(A::ClassField, B::ClassField) -> ClassField
> The compositum of $a$ and $b$ as a (formal) class field.
"""
*(a::ClassField, b::ClassField) = compositum(a, b)

@doc Markdown.doc"""
    intersect(a::ClassField, b::ClassField) -> ClassField
> The intersection of $a$ and $b$ as a class field.
"""
function Base.intersect(a::ClassField, b::ClassField)
  @assert base_ring(a) == base_ring(b)
  c = lcm(defining_modulus(a)[1], defining_modulus(b)[1])
  c_inf = union(defining_modulus(a)[2], defining_modulus(b)[2])
  d = lcm(degree(a), degree(b))

  r, mr = ray_class_group(c, c_inf, n_quo = Int(d))
  C = ray_class_field(mr)
  h = norm_group_map(C, [a,b])
  U = kernel(h[1])[1] + kernel(h[2])[1]
  q, mq = quo(codomain(C.quotientmap), U)
  return ray_class_field(mr, GrpAbFinGenMap(C.quotientmap * mq))
end

@doc Markdown.doc"""
    issubfield(a::ClassField, b::ClassField) -> Bool
> Determines of $a$ is a subfield of $b$.
"""
function issubfield(a::ClassField, b::ClassField)
  @assert base_ring(a) == base_ring(b)
  c = lcm(defining_modulus(a)[1], defining_modulus(b)[1])
  c_inf = union(defining_modulus(a)[2], defining_modulus(b)[2])
  d = lcm(degree(a), degree(b))

  r, mr = ray_class_group(c, c_inf, n_quo = Int(d))
  C = ray_class_field(mr)
  h = norm_group_map(C, [a,b])
  return issubset(kernel(h[2])[1], kernel(h[1])[1])
end

@doc Markdown.doc"""
    ==(a::ClassField, b::ClassField)
> Tests if $a$ and $b$ are equal.
"""
function ==(a::ClassField, b::ClassField)
  @assert base_ring(a) == base_ring(b)
  mq1 = a.quotientmap
  mq2 = b.quotientmap
  if !isisomorphic(codomain(mq1), codomain(mq2))
    return false
  end
  expo = Int(exponent(codomain(mq1)))
  c = lcm(defining_modulus(a)[1], defining_modulus(b)[1])
  c_inf = union(defining_modulus(a)[2], defining_modulus(b)[2])

  r, mr = ray_class_group(c, c_inf, n_quo = expo)
  C = ray_class_field(mr)
  @assert defining_modulus(C) == (c, c_inf)
  h = norm_group_map(C, [a,b])
  return iseq(kernel(h[2])[1], kernel(h[1])[1])
end

@doc Markdown.doc"""
    hilbert_class_field(k::AnticNumberField) -> ClassField
> The Hilbert class field of $k$ as a formal (ray-) class field.
"""
function hilbert_class_field(k::AnticNumberField)
  return ray_class_field(class_group(k)[2])
end

@doc Markdown.doc"""
    ray_class_field(I::NfAbsOrdIdl; n_quo = 0) -> ClassField
> The ray class field modulo $I$. If {{{n_quo}}} is given, then the largest
> subfield of exponent $n$ is computed.
"""
function ray_class_field(I::NfAbsOrdIdl; n_quo = 0)
  return ray_class_field(ray_class_group(I, n_quo = n_quo)[2])
end

@doc Markdown.doc"""
    ray_class_field(I::NfAbsOrdIdl, inf::Array{InfPlc, 1}; n_quo = 0) -> ClassField
> The ray class field modulo $I$ and the infinite places given. If {{{n_quo}}} is given, then the largest
> subfield of exponent $n$ is computed.
"""
function ray_class_field(I::NfAbsOrdIdl, inf::Array{InfPlc, 1}; n_quo = 0)
  return ray_class_field(ray_class_group(I, inf, n_quo = n_quo)[2])
end

@doc Markdown.doc"""
    prime_decomposition_type(C::ClassField, p::NfAbsOrdIdl) -> (Int, Int, Int)
> For a prime $p$ in the base ring of $r$, determine the splitting type of $p$ 
> in $r$. ie. the tuple $(e, f, g)$ giving the ramification degree, the inertia
> and the number of primes above $p$.
"""
function prime_decomposition_type(C::ClassField, p::NfAbsOrdIdl)
  @hassert :ClassField 1 isprime(p)
  mR = C.rayclassgroupmap
  m0 = mR.modulus_fin
  R = domain(mR)

  v = valuation(m0, p)
  if v == 0
    f = order(C.quotientmap(mR\p))
    return (1, f, divexact(degree(C), f))
  end
  r, mr = ray_class_group(divexact(m0, p^v), defining_modulus(C)[2], n_quo = Int(exponent(R)))

  lp, sR = find_gens(MapFromFunc(x->preimage(mR, x), IdealSet(base_ring(C)), domain(mR)),
                             PrimesSet(100, -1), minimum(m0))
  h = hom(sR, [preimage(mr, p) for p = lp])
  k, mk = kernel(GrpAbFinGenMap(C.quotientmap))
  q, mq = quo(r, [h(mk(k[i])) for i=1:ngens(k)])
  f = order(mq(preimage(mr, p)))
  e = divexact(degree(C), order(q))
  return (e, f, divexact(order(q), f))
end

@doc Markdown.doc"""
    iscyclic(C::ClassField)
> Tests if the (relative) automorphism group of $C$ is cyclic (by checking
> the defining ideal group).
"""
function iscyclic(C::ClassField)
  mp = C.quotientmap
  return iscyclic(codomain(mp))
end

@doc Markdown.doc"""
    ring_class_group(O::NfAbsOrd) 
> The ring class group (Picard group) of $O$.    
"""
ring_class_group(O::NfAbsOrd) = picard_group(O)


@doc Markdown.doc"""
    ring_class_field(O::NfAbsOrd) -> ClassField
> The ring class field of $O$, ie. the maximal abelian extension ramifed 
> only at primes dividing the conductor with the automorphism group
> isomorphic to the Picard group.
"""
function ring_class_field(O::NfAbsOrd)
  M = maximal_order(O)
  f = extend(conductor(O), M)
  R, mR = ray_class_group(f)
  P, mP = picard_group(O)
  g, t = find_gens(mR)
  h = hom(t, [mP \ contract(x, O) for x = g], check = true)
  k = kernel(h, true)[1]
  q, mq = quo(R, k)
  return ray_class_field(mR, mq)
end
