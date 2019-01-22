export kummer_extension, ray_class_field, hilbert_class_field, prime_decomposition_type, defining_modulus

add_verbose_scope(:ClassField)
add_assert_scope(:ClassField)
#set_assert_level(:ClassField, 1)

###############################################################################
#
#  Ray Class Field interface
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

###############################################################################
#
#  Number_field interface and reduction to prime power case
#
###############################################################################

@doc Markdown.doc"""
    NumberField(CF::ClassField) -> Hecke.NfRel_ns{Nemo.nf_elem}
> Given a (formal) abelian extension, compute the class field by
> finding defining polynomials
> for all prime power cyclic subfields.
> Note, by type this is always a non-simple extension.
"""
function NumberField(CF::ClassField; redo::Bool = false)
  if isdefined(CF, :A) && !redo
    return CF.A
  end
  
  res = ClassField_pp[]
  G = codomain(CF.quotientmap)
  @assert issnf(G)
  q = [G[i] for i=1:ngens(G)]
  for i=1:ngens(G)
    o = G.snf[i]
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
#  Find small generator of class group
#
###############################################################################

function find_gens(mR::Map, S::PrimesSet, cp::fmpz=fmpz(1))
# mR: SetIdl -> GrpAb (inv of ray_class_group or Frobenius or so)
  ZK = order(domain(mR))
  R = codomain(mR) 
  sR = GrpAbFinGenElem[]
  lp = elem_type(domain(mR))[]

  q, mq = quo(R, sR, false)
  s, ms = snf(q)
  for p in S
    if cp % p == 0 || index(ZK) % p == 0
      continue
    end
    @vprint :ClassField 2 "doin` $p\n"
    lP = prime_decomposition(ZK, p)

    f=R[1]
    for (P, e) = lP
      try
        f = mR(P)
      catch e
        if !isa(e, BadPrime)
          rethrow(e)
        end
        break # try new prime number
      end
      if iszero(mq(f))
        continue
      end
      #At least one of the coefficient of the element 
      #must be invertible in the snf form.
      el = ms\f
      to_be = false
      for w = 1:ngens(s)
        if gcd(s.snf[w], el.coeff[w]) == 1
          to_be = true
          break
        end
      end
      if !to_be
        continue
      end
      push!(sR, f)
      push!(lp, P)
      q, mq = quo(R, sR, false)
      s, ms = snf(q)
    end
    if order(q) == 1   
      break
    end
  end
  return lp, sR
  
end

#Computes a set of prime ideals of the base field of K such that the corresponding Frobenius
#generate the automorphism group
function find_gens(K::KummerExt, S::PrimesSet, cp::fmpz=fmpz(1))
  ZK = maximal_order(base_field(K))
  R = K.AutG 
  sR = GrpAbFinGenElem[]
  lp = NfOrdIdl[]

  q, mq = quo(R, sR, false)
  s, ms = snf(q)
  for p in S
    if cp % p == 0 || index(ZK) % p == 0
      continue
    end
    @vprint :ClassField 2 "doin` $p\n"
    lP = prime_decomposition(ZK, p)

    f = R[1]
    for (P, e) = lP
      try
        f = can_frobenius1(P, K)
      catch e
        if !isa(e, BadPrime)
          rethrow(e)
        end
        continue
      end
      if iszero(mq(f))
        continue
      end
      #At least one of the coefficient of the element 
      #must be invertible in the snf form.
      el = ms\f
      to_be = false
      for w = 1:ngens(s)
        if gcd(s.snf[w], el.coeff[w]) == 1
          to_be = true
          break
        end
      end
      if !to_be
        continue
      end
      push!(sR, f)
      push!(lp, P)
      q, mq = quo(R, sR, false)
      s, ms = snf(q)
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
  
  #cf = Hecke.MapFromFunc(x->can_frobenius1(x, K), IdealSet(ZK), K.AutG)

  mp = c.mp[2]
  cp = lcm(cp, index(maximal_order(domain(mp))))
  ZK = maximal_order(c.Ka)
  #@hassert :ClassField 1 order(domain(cf)) == ZK
  Zk = order(m)
  Id_Zk = Hecke.NfOrdIdlSet(Zk)
  Sp = Hecke.PrimesSet(100, -1, c.n, 1) #primes = 1 mod n, so totally split in cyclo

  @vtime :ClassField 2 lp, sG = find_gens(K, Sp, cp)
  G = K.AutG
  sR = Array{GrpAbFinGenElem, 1}(undef, length(lp))
  for i=1:length(lp)
    p = Id_Zk(intersect_nonindex(mp, lp[i]))
    sR[i] = valuation(norm(lp[i]), norm(p))*CF.quotientmap(preimage(CF.rayclassgroupmap, p))
  end
  @hassert :ClassField 1 order(quo(G, sG, false)[1]) == 1
       # if think if the quo(G, ..) == 1, then the other is automatic
       # it is not, in general it will never be.
       #example: Q[sqrt(10)], rcf of 16*Zk
  # now the map G -> R sG[i] -> sR[i] 
  h = hom(sG, sR)
  return h
end

#This function finds a set S of primes such that we can find a Kummer generator in it.
function _s_unit_for_kummer(C::CyclotomicExt, f::fmpz)
  
  e = C.n
  K = C.Ka
  @vprint :ClassField 2 "Maximal order of cyclotomic extension\n"
  ZK = maximal_order(K)
  @vprint :ClassField 2 "Class group of cyclotomic extension\n"
  @vtime :ClassField 2 c, mc = class_group(ZK)
  allow_cache!(mc)
  @vprint :ClassField 2 "... $c\n"
  c, mq = quo(c, e, false)
  mc = _compose(mc, inv(mq))
  
  lP = Hecke.NfOrdIdl[]
  if f != 1
    lf = factor(f)  
    for p = keys(lf.fac)
       #I remove the primes that can't be in the conductor
       lp = prime_decomposition(ZK, p)
       for (P, s) in lp
         if gcd(norm(P), e) != 1 || gcd(norm(P)-1, e) != 1
           push!(lP, P)
         end 
       end
    end
  end
  g = Array{GrpAbFinGenElem, 1}(undef, length(lP))
  for i = 1:length(lP)
    g[i] = preimage(mc, lP[i])
  end

  q, mq = quo(c, g, false)
  mc = compose(inv(mq), mc)
  
  lP = vcat(lP, find_gens(inv(mc), PrimesSet(100, -1))[1])
  
  @vprint :ClassField 2 "using $lP of length $(length(lP)) for S-units\n"
  if isempty(lP)
    U, mU = unit_group_fac_elem(ZK)
    KK = kummer_extension(e, [mU(U[i]) for i = 1:ngens(U)])
  else
    @vtime :ClassField 2 S, mS = Hecke.sunit_group_fac_elem(lP)
    @vtime :ClassField 2 KK = kummer_extension(e, [mS(S[i]) for i=1:ngens(S)])
  end
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
  @vtime :ClassField 3 KK.eval_mod_nth = nf_elem[evaluate(x) for x in gens_mod_nth]

  return lP, KK
end

function _rcf_find_kummer(CF::ClassField_pp)

  if isdefined(CF, :K)
    return CF.K
  end
  f = defining_modulus(CF)[1]::NfOrdIdl
  @vprint :ClassField 2 "Kummer extension ... with modulus $f\n"
  k1 = nf(order(f))
  e = degree(CF)::Int 
  @assert Hecke.isprime_power(e)

  @vprint :ClassField 2 "Adjoining the root of unity\n"
  C = cyclotomic_extension(k1, e)
  
  #We could use f, but we would have to factor it.
  lP, KK = _s_unit_for_kummer(C, minimum(f))
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
  s, ms = sub(N, GrpAbFinGenElem[sum([n[j, ind]*N[j] for j=1:rows(n)]) for ind=1:i], false)
  ms = Hecke.make_snf(ms)
  H = domain(ms)
  @hassert :ClassField 1 iscyclic(H)
  o = Int(order(H))
  c = 1
  if o < e
    c = div(e, o)
  end
  g = ms(H[1])
  @vprint :ClassField 2 "g = $g\n"
  #@vprint :ClassField 2 "final $n of order $o and e=$e\n"
  a = prod([KK.gen[i]^div(mod(g[i], e), c) for i=1:ngens(N)])
  #@vprint :ClassField 2 "generator $a\n"
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

#This function computes a primitive element for the target extension with the
#roots of unit over the base field and the action of the automorphisms on it.
#The Kummer generator is always primitive! (Carlo and Claus)
function _find_prim_elem(AutA::GrpAbFinGen, AutA_gen::Array{NfRelToNfRelMor{nf_elem,  nf_elem}, 1}, C::CyclotomicExt)
  
  A = domain(AutA_gen[1])
  pe = gen(A)
  Auto = Dict{Hecke.GrpAbFinGenElem, NfRelElem}()
  for j in AutA
    im = grp_elem_to_map(AutA_gen, j, pe)
    Auto[j] = im
  end
  @vprint :ClassField 2 "have action on the primitive element!!!\n"  
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

    This has to be done for enough automorphisms of k(zeta)/k to generate
    the full group. If n=p^k then this is one (for p>2) and n=2, 4 and
    2 for n=2^k, k>2
=#
  e = degree(CF)
  g, mg = unit_group(ResidueRing(FlintZZ, e, cached=false))
  @assert issnf(g)
  @assert (e%8 == 0 && ngens(g)==2) || ngens(g) <= 1
  
  K = C.Ka
  Kr = C.Kr

  if degree(Kr) < order(g)  # there was a common subfield, we
                              # have to pass to a subgroup
    @assert order(g) % degree(Kr) == 0
    f = Kr.pol
    # Can do better. If the group is cyclic (e.g. if p!=2), we already know the subgroup!
    s, ms = sub(g, [x for x in g if iszero(f(gen(Kr)^Int(lift(mg(x)))))], false)
    ss, mss = snf(s)
    g = ss
    #mg = mg*ms*mss
    mg = mss * ms * mg
  end
  
  
  

  @vprint :ClassField 2 "building automorphism group over ground field...\n"
  ng = ngens(g)+1
  AutA_gen = Array{Hecke.NfRelToNfRelMor{nf_elem,  nf_elem}, 1}(undef, ng)
  AutA_rel = zero_matrix(FlintZZ, ng, ng)
  zeta = C.mp[1](gen(Kr))
  n = degree(A)
  @assert e % n == 0

  @vprint :ClassField 2 "... the trivial one (Kummer)\n"
  tau = Hecke.NfRelToNfRelMor{nf_elem,  nf_elem}(A, A, zeta^div(e, n)*gen(A))
  AutA_gen[1] = tau

  AutA_rel[1,1] = n  # the order of tau

  
  @vprint :ClassField 2 "... need to extend $(ngens(g)) from the cyclo ext\n"
  for i = 1:ngens(g)
    si = Hecke.NfRelToNfRelMor{nf_elem, nf_elem}(Kr, Kr, gen(Kr)^Int(lift(mg(g[i]))))
    @vprint :ClassField 2 "... extending zeta -> zeta^$(mg(g[i]))\n"
    to_be_ext = NfToNfMor(K, K, C.mp[1](si(preimage(C.mp[1], gen(K)))))
    sigma = _extend_auto(A, to_be_ext)
    AutA_gen[i+1] = sigma

    @vprint :ClassField 2 "... finding relation ...\n"
    m = gen(A)
    for j = 1:Int(order(g[i]))
      m = sigma(m)
    end
    # now m SHOULD be tau^?(gen(A)), so sigma^order(g[i]) = tau^?
    # the ? is what I want...
    j = 0
    zeta_i = zeta^mod(div(e, n)*(e-1), e)
    mi = coeff(m, 1)
    @hassert :ClassField 1 m == mi*gen(A) 

    while mi != 1
      mul!(mi, mi, zeta_i)
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
  @hassert :ClassField 1 iskummer_extension(K)
  #@assert iskummer_extension(K)
  k = base_ring(K)
  Zk = maximal_order(k)
  zeta, ord = Hecke.torsion_units_gen_order(Zk)
  @assert ord % degree(K) == 0
  zeta = k(zeta)^div(ord, degree(K))

  im_zeta = h(zeta)
  r = 1
  z = deepcopy(zeta)
  while im_zeta != z
    r += 1
    mul!(z, z, zeta)
  end

  a = -coeff(K.pol, 0)
  a = h(a)//a^r
  @vtime :ClassField 3 fl, b = ispower(a, degree(K), with_roots_unity = true)
  @assert fl
  return NfRelToNfRelMor(K, K, h, b*gen(K)^r)
end



function _rcf_descent(CF::ClassField_pp)
  if isdefined(CF, :A)
    return CF.A
  end

  @vprint :ClassField 2 "Descending ...\n"
               
  e = degree(CF)
  k = base_field(CF)
  C = cyclotomic_extension(k, e)
  A = CF.K
  if C.Ka == k
    #There is nothing to do! The extension is already on the right field
    CF.A = A
    CF.pe = gen(A)
    return CF.A
  end
  
  Zk = maximal_order(k)
  ZK = maximal_order(C.Ka)
  
  n = degree(A)
  #@vprint :ClassField 2 "Automorphism group (over ground field) $AutA\n"
  _aut_A_over_k(C, CF)
  
  AutA_gen = CF.AutG
  AutA = GrpAbFinGen(CF.AutR)
  # now we need a primitive element for A/k
  # mostly, gen(A) will do
  
  @vprint :ClassField 2 "\nnow the fix group...\n"
  if iscyclic(AutA)  # the subgroup is trivial to find!
    @vprint :ClassField 2 ".. trivial as automorphism group is cyclic\n"
    s, ms = sub(AutA, e, false)
    @vprint :ClassField 2 "computing orbit of primitive element\n"
    pe = gen(A)
    os = NfRelElem[grp_elem_to_map(AutA_gen, ms(j), pe) for j in s]
  else
    @vprint :ClassField 2 "Computing automorphisms of the extension and orbit of primitive element\n"
    pe, Auto = _find_prim_elem(AutA, AutA_gen, C)
    @vprint :ClassField 2 ".. interesting...\n"
    # want: hom: AutA = Gal(A/k) -> Gal(K/k) = domain(mq)
    #K is the target field.
    # idea: take primes p in k and compare
    # Frob(p, A/k) and preimage(mq, p)
    @assert n == degree(CF.K)
    
    function canFrob(p::NfOrdIdl)
      lP = prime_decomposition(C.mp[2], p)
      P = lP[1][1]
      F, mF = ResidueFieldSmall(ZK, P)
      Ft, t = PolynomialRing(F, cached=false)
      mFp = extend_easy(mF, C.Ka)
      ap = image(mFp, CF.a)
      pol = Ft()
      setcoeff!(pol, 0, -ap)
      setcoeff!(pol, n, one(F))
      Ap = ResidueRing(Ft, pol, cached = false)
      xpe = zero(Ft)
      for i = 0:n-1
        setcoeff!(xpe, i, image(mFp, coeff(pe, i)))
      end
      imF = Ap(xpe)^norm(p)
      res = GrpAbFinGenElem[]
      for (ky, v) in Auto
        xp = zero(Ft)
        @assert coeff(v, n) == 0
        for i = 0:n-1
          setcoeff!(xp, i, image(mFp, coeff(v, i)))
        end
        kp = Ap(xp)
        if kp == imF
          push!(res, ky)
          if length(res) >1
            throw(BadPrime(p))
          end
          #return ky
        end
      end
      return res[1]
      error("Frob not found")  
    end

    @vprint :ClassField 2 "finding Artin map...\n"
    #TODO can only use non-indx primes, easy primes...
    cp = lcm([minimum(defining_modulus(CF)[1]), index(Zk), index(ZK)])
    @vtime :ClassField 2 lp, f = find_gens(MapFromFunc(canFrob, IdealSet(Zk), AutA),
                      PrimesSet(200, -1), cp)
    imgs = GrpAbFinGenElem[image(CF.quotientmap, preimage(CF.rayclassgroupmap, p)) for p = lp]
    h = hom(f, imgs)
    @hassert :ClassField 1 issurjective(h)
    s, ms = kernel(h)
    @vprint :ClassField 2 "... done, have subgroup!\n"
    @vprint :ClassField 2 "computing orbit of primitive element\n"
    os = NfRelElem[Auto[ms(j)] for j in s]
  end
  
  q, mq = quo(AutA, ms.map, false)
  @assert order(q) == degree(CF)
  
  #now, hopefully either norm or trace will be primitive for the target
  #norm, trace relative to s, the subgroup

  AT, T = PolynomialRing(A, "T", cached = false)
  function coerce_down(a::NfRelElem)
    @assert a.data.length <= 1
    b = coeff(a, 0)
    c = preimage(C.mp[1], b)
    @assert c.data.length <= 1
    return coeff(c, 0)
  end
  
  function charpoly(a::NfRelElem)
    @vtime :ClassField 2 o = NfRelElem[grp_elem_to_map(AutA_gen, mq(j), a) for j = q]
    @vtime :ClassField 2 f = prod(T-x for x=o)
    @assert degree(f) == length(o)
    @assert length(o) == e
    @vtime :ClassField 2 g = nf_elem[coerce_down(coeff(f, i)) for i=0:Int(e)]
    return PolynomialRing(parent(g[1]), cached = false)[1](g)
  end

  @vprint :ClassField 2 "trying relative trace\n"
  @assert length(os) > 0
  t = os[1]
  for i = 2:length(os)
    t += os[i]
  end
  CF.pe = t
  #now the minpoly of t - via Galois as this is easiest to implement...
  @vprint :ClassField 2 "char poly...\n"
  f = charpoly(t)
  @vprint :ClassField 2 "... done\n"
  
  if !issquarefree(f)
    os1 = deepcopy(os)
    while !issquarefree(f)
      @vprint :ClassField 2 "trying relative trace of squares\n"
      for i = 1:length(os)
        os1[i] *= os[i]
      end
      t = os1[1]
      for i = 2:length(os)
        t += os1[i]
      end
      CF.pe = t
      #now the minpoly of t - via Galois as this is easiest to implement...
      @vprint :ClassField 2 "min poly...\n"
      f = charpoly(t)
      @vprint :ClassField 2 "... done\n"
    end  
  end
  CF.A = number_field(f, check = false)[1]
  return nothing
end

function grp_elem_to_map(A::Array{NfRelToNfRelMor{nf_elem, nf_elem}, 1}, b::GrpAbFinGenElem, pe::NfRelElem)
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
For a residue field map from a prime ideal, extend the domain of the map
to the entire field.
Requires the prime ideal to be coprime to the index, unramified and
over a small integer. The resulting map can very efficiently be
evaluated using {{{image(map, elem}}}.
The resulting map can be applied to
  * {{{nf_elem}}}
  * {{{FacElem{nf_elem}}}}
Will throw a {{{BadPrime}}} exception if applied to an element in the 
field with a $p$ in the denominator. In the case of {{{FacElem}}}, zero
is also mot permitted (and will produce a {{{BadPrime}}} error.
"""
function extend_easy(f::Hecke.NfOrdToFqNmodMor, K::AnticNumberField)
  nf(domain(f)) != K && error("Number field is not the number field of the order")
  return NfToFqMor_easy(f, K)

  #O = domain(f) #used for the hassert and thus the testing
  z = Hecke.NfToFqNmodMor()
  z.header.domain = K
  z.header.codomain = f.header.codomain

  p = characteristic(z.header.codomain)
  #y = f(NfOrdElem(domain(f), gen(K)))
  Ft, t = PolynomialRing(GF(UInt(p), cached=false), cached=false)
  #K = number_field(domain(f))
#  g = gcd(Ft(K.pol), Ft(K(f.P.gen_two)))
#it would be cool to assert that g is the poly defining the codomain
  #qm1 = size(codomain(f))-1

  function _image(x::NfOrdElem)
    return f(x)
  end
  
  Fq = codomain(f)
  
  function _image(x::nf_elem)
    m = denominator(x)
    if m % p == 0
      throw(BadPrime(p))
    end
    return Fq(Ft(x)) 
  end

  t = Ft()

  function _image(x::FacElem{nf_elem, AnticNumberField})
    D = Dict{fq_nmod, fmpz}()
    for (k, v) = x.fac
      if iszero(v)
        continue
      end
      if denominator(k) % p == 0
        throw(BadPrime(p))
      end
      s = Fq()
      _nf_to_fq!(s, k, Fq, t)
      if iszero(s)
        throw(BadPrime(p))
      end
      if haskey(D, s)
        D[s] += v
      else
        D[s] = v
      end
    end
    return _ev(D, one(Fq))
  end
  
  #=
  s = Fq()
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
  =#

  function _preimage(x::fq_nmod)
    return elem_in_nf(preimage(f, x))
  end

  z.header.image = _image
  z.header.preimage = _preimage

  return z
end

#a stop-gap, mainly for non-monic polynomials
function extend_easy(f::Hecke.NfOrdToFqMor, K::AnticNumberField)
  return extend(f, K)
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
#  Auxiliary functions (to be moved)
#
###############################################################################

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
