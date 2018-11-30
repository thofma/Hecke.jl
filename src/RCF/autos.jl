################################################################################
#
#  Interface
#
################################################################################
@doc Markdown.doc"""
    absolute_automorphism_group(C::ClassField)
  
>  Computes a generating set for the automorphisms of the 
   number field corresponding to C. It assumes that the base field is normal.
   if "check" is true, the function checks if the extension is normal.
"""
function absolute_automorphism_group(C::ClassField, check::Bool = false)
 
  L = number_field(C)
  K = base_field(C)
  autK = automorphisms(K)
  @assert length(autK) == degree(K)
  if check
    @assert isnormal(C)
  end
  id = find_identity(autK, *)
  autK_gen = small_generating_set(autK, *, id)
  return absolute_automorphism_group(C, autK_gen)
end

function absolute_automorphism_group(C::ClassField, aut_gen_of_base_field::Array{NfToNfMor, 1})
  L = number_field(C)
  aut_L_rel = rel_auto(C)::Vector{NfRel_nsToNfRel_nsMor}
  rel_extend = Hecke.new_extend_aut(C, aut_gen_of_base_field)
  rel_gens = vcat(aut_L_rel, rel_extend)
  return rel_gens::Array{NfRel_nsToNfRel_nsMor, 1}
end

function automorphism_groupQQ(C::ClassField)
  return rel_auto(C)
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

@doc Markdown.doc"""
    extend_to_cyclotomic(C::CyclotomicExt, tau::NfToNfMor) -> NfRelToNfRelMor
    
> Given a cyclotomic extension $C$ of a number field $K$ and an automorphism $\tau$ of $K$,
  computes an extension of tau to $C$.

"""
function extend_to_cyclotomic(C::CyclotomicExt, tau::NfToNfMor)		
   		
  K = domain(tau)		
  @assert K == base_ring(C.Kr)
  gKr = gen(C.Kr)
  if euler_phi(C.n) == degree(C.Kr)
    #The extension with the roots of unity is disjoint from K
    #Therefore, the minimal polynomial has coefficient over QQ.
    return NfRelToNfRelMor(C.Kr, C.Kr, tau, gKr)
  end		
  g = C.Kr.pol		
  tau_g = parent(g)([tau(coeff(g, i)) for i=0:degree(g)])	
  i = 1	
  z = deepcopy(gKr)		
  while gcd(i, C.n) != 1 || !iszero(tau_g(z))		
    i += 1		
    mul!(z, z, gKr) 		
  end		
  return NfRelToNfRelMor(C.Kr, C.Kr, tau, z)		
  		
end

function new_extend_aut(A::ClassField, auto::T) where T <: Map
  return new_extend_aut(A, T[auto])[1]
end

function new_extend_aut(A::ClassField, autos::Array{T, 1}) where T <: Map

  # tau: k -> k
  k = domain(autos[1])
  @assert k == codomain(autos[1])
  @assert k == base_field(A)
  lp = factor(fmpz(degree(A)))
  L = number_field(A)
  # I call number field because to extend the automorphism I need the 
  all_imgs = Array{Array{NfRel_nsElem{nf_elem}, 1}, 1}(undef, length(autos))
  #Initialize the array
  for i=1:length(autos)
    all_imgs[i] = [L() for i=1:length(A.cyc)]
  end
  lG = gens(L)
  #P-Sylow subgroups are invariant, I can reduce to the prime power case.
  res = Array{NfRel_nsToNfRel_nsMor, 1}(undef, length(autos))
  for (p, v) = lp.fac
    imgs = extend_aut_pp(A, autos, p)
    # The output are the images of the cyclic components in A.A
    indices = Array{Int, 1}(undef, length(imgs[1]))
    j = 1
    for i = 1:length(imgs[1])
      while degree(A.cyc[j]) % Int(p) != 0
        j += 1
      end
      indices[i] =  j
      j += 1
    end
    #I need to embed Ap in L
    Ap = parent(imgs[1][1])
    emb = NfRel_nsToNfRel_nsMor(Ap, L, [lG[indices[i]] for i = 1:length(indices)])
    for j = 1:length(autos)
      for i = 1:length(imgs[j])
        all_imgs[j][indices[i]] = emb(imgs[j][i])
      end
    end
  end
  for i = 1:length(res)
    res[i] = NfRel_nsToNfRel_nsMor(L, L, autos[i], all_imgs[i])
  end
  return res
  
end

#Find a prime ideal P such that the Frobenius generates the Galois group of the extension.
function find_frob(A::ClassField_pp, K::KummerExt, emb::NfToNfMor) 
  
  m = defining_modulus(A)[1]
  d = A.o
  K1 = kummer_extension(d, [A.a])
  k1 = base_field(K1)
  O1 = maximal_order(k1)
  k = base_field(K)
  O = maximal_order(k)
  Sp = Hecke.PrimesSet(200, -1)
  cp = lcm([discriminant(O), minimum(m), index(O), index(O1)])
  P = ideal(O, 1)
  for p in Sp
    if cp % p == 0
      continue
    end
    lp = prime_decomposition(O1, p)
    for i = 1:length(lp)
      try
        z = can_frobenius(lp[i][1], K1)
        if order(z) != d
          continue
        end
        lP = prime_decomposition_nonindex(emb, lp[i][1])
        P = lP[1][1]
        zK = can_frobenius(P, K)
      catch e
        if typeof(e) != BadPrime
          rethrow(e)
        end
        continue
      end
      return P
    end
  end
  error("Something strange is happening")
end

function find_frob(A::ClassField_pp) 
  
  m = defining_modulus(A)[1]
  d = A.o
  K1 = kummer_extension(d, [A.a])
  k1 = base_field(K1)
  O = maximal_order(k1)
  Sp = Hecke.PrimesSet(200, -1)
  cp = lcm([minimum(m), index(O), discriminant(O)])
  for p in Sp
    if cp % p == 0
      continue
    end
    lp = prime_decomposition(O, p)
    for i = 1:length(lp)
      try
        zK1 = can_frobenius(lp[i][1], K1)
        if order(zK1) != d
          continue
        end
      catch e
        if typeof(e) != BadPrime
          rethrow(e)
        end
        continue
      end
      return lp[i][1]
    end
  end
  error("Something strange is happening")
end

function find_gens(A::ClassField, cp::fmpz = fmpz(1))
  
  mR = A.rayclassgroupmap
  mQ = A.quotientmap
  O = order(codomain(mR))
  R = codomain(mQ) 
  m = mR.defining_modulus[1]
  mm = lcm(minimum(m), cp)

  sR = GrpAbFinGenElem[]
  lp = NfOrdIdl[]
  q, mq = quo(R, sR, false)
  if isdefined(mR, :prime_ideal_cache)
    S = mR.prime_ideal_cache
  else
    S = prime_ideals_up_to(O, max(1000,100*clog(discriminant(O),10)^2))
    mR.prime_ideal_cache = S
  end
  for P in S
    if gcd(minimum(P), mm) != 1
      continue
    end
    if haskey(mR.prime_ideal_preimage_cache, P)
      f = mR.prime_ideal_preimage_cache[P]
    else
      f = mR\P
      mR.prime_ideal_preimage_cache[P] = f
    end
    f1 = mQ(f)
    if iszero(mq(f1))
      continue
    end
    push!(sR, f1)
    push!(lp, P)
    q, mq = quo(R, sR, false)
    if order(q) == 1 
      break
    end
  end
  @assert order(q)==1
  return lp, sR
end

function find_gens(KK::KummerExt, gens_imgs::Array{Array{FacElem{nf_elem}, 1}, 1}, m::fmpz)

  K = base_field(KK)
  O = maximal_order(K)
  els = GrpAbFinGenElem[]
  Q, mQ = quo(KK.AutG, els)
  Sp = Hecke.PrimesSet(200, -1)
  cp = lcm(discriminant(O), m)
  frob_gens = NfOrdIdl[]
  for q in Sp
    if cp % q == 0
      continue
    end
    lp = prime_decomposition(O, q)
    for i = 1:length(lp)
      try
        z = can_frobenius(lp[i][1], KK)
        if iszero(mQ(z))
          continue
        end
        for x in gens_imgs
          for y in x
            can_frobenius(lp[i][1], KK, y)
          end
        end
        push!(frob_gens, lp[i][1])
        push!(els, z)
      catch e
        if typeof(e) != BadPrime
          rethrow(e)
        end
        continue
      end
      Q, mQ = quo(KK.AutG, els)
      if order(Q) == 1
        break
      end
    end
    if order(Q) == 1
      break
    end
  end
  return frob_gens
end

function extend_aut_pp(A::ClassField, autos::Array{T, 1}, p::fmpz) where T <: Map
  
  Cp = ClassField_pp[x for x in A.cyc if degree(x) % Int(p) == 0]
  AA, gAA = number_field([c.A.pol for c = Cp])
  #Main Idea: I extend tau to the big kummer extension KK and then I restrict it to AA.
  k = base_field(A)
  d = maximum(degree(x) for x in Cp)
  C = cyclotomic_extension(k, d)
  O = maximal_order(C.Ka)
  # C is the base field of the kummer extension generated
  # by all the cyclic components.
  # I extend the automorphisms to C
  Autos_abs = Array{NfToNfMor, 1}(undef, length(autos))
  for i = 1:length(autos)
    aut = extend_to_cyclotomic(C, autos[i])
    Autos_abs[i] = NfToNfMor(C.Ka, C.Ka, C.mp[1](aut(C.mp[1]\gen(C.Ka))))
  end
  #I compute the embeddings of the small cyclotomic extensions into the others
  abs_emb = Array{NfToNfMor, 1}(undef, length(Cp))
  for i = 1:length(Cp)
    if degree(Cp[i]) == d
      abs_emb[i] = NfToNfMor(C.Ka, C.Ka, gen(C.Ka))
    else
      Cs = cyclotomic_extension(k, degree(Cp[i]))
      emb = NfRelToNfRelMor(Cs.Kr, C.Kr, gen(C.Kr)^div(d, degree(Cp[i])))
      img = C.mp[1](emb(Cs.mp[1]\(gen(Cs.Ka))))
      abs_emb[i] = NfToNfMor(Cs.Ka, C.Ka, img)
    end
  end

  #Now, I can compute the corresponding Kummer extension over the big cyclotomic field.
  m = minimum(defining_modulus(A)[1])
  incs = Array{NfRelToNfRel_nsMor, 1}(undef, length(Cp))
  if gcd(d, m) == 1 || d == minimum(degree(x) for x in Cp)
    #the extension and the cyclotomic extensions are linearly disjoint!
    exps = Array{Int, 1}(undef, length(Cp))
    gens = Array{FacElem{nf_elem, AnticNumberField}, 1}(undef, length(Cp))
    for i = 1:length(Cp) 
      if degree(Cp[i]) == d 
        gens[i] = Cp[i].a
        exps[i] = Cp[i].o
      else
        a = FacElem(Dict(abs_emb[i](ke) => v for (ke,v) = Cp[i].a.fac))
        exps[i] = Cp[i].o
        gens[i] = a
      end
    end
    KK = kummer_extension(exps, gens)
    K, gK = number_field(KK)
    #I need the inclusions of the single extensions Cp[i].K in K
    for i = 1:length(Cp)
      incs[i] = NfRelToNfRel_nsMor(Cp[i].K, K, abs_emb[i], gK[i])
    end
  else
    #Difficult case. Think about it...
    error("Not yet implemented")
  end
  
  # I want extend the automorphisms to KK
  # First, I find a set of primes such that their Frobenius generates the Galois group of KK
  act_on_gens = Array{Array{FacElem{nf_elem}, 1}, 1}(undef, length(KK.gen))
  for i = 1:length(KK.gen)
    act_on_gen_i = Array{FacElem{nf_elem}, 1}(undef, length(autos))
    for j = 1:length(autos)
      act_on_gen_i[j] = FacElem(Dict(Autos_abs[j](ke) => v for (ke, v) in KK.gen[i]))
    end
    act_on_gens[i] = act_on_gen_i
  end
  frob_gens = find_gens(KK, act_on_gens, m)
  
  autos_extended = Array{NfRel_nsToNfRel_nsMor, 1}(undef, length(autos))
  #I will compute a possible image cyclic component by cyclic component
  for w = 1:length(autos)
    images_KK = Array{Tuple{GrpAbFinGenElem, FacElem{nf_elem, AnticNumberField}}, 1}(undef, length(Cp))
    for i = 1:length(Cp)
      images_KK[i] = extend_auto(KK, act_on_gens[i][w], Int(order(KK.AutG[i])), frob_gens)
    end
  
    #Now, I can define the automorphism on K
    images_K = Array{NfRel_nsElem{nf_elem}, 1}(undef, length(images_KK))
    for i = 1:length(images_K)
      s = K(evaluate(images_KK[i][2]))
      for j = 1:length(Cp)
        mul!(s, s, gK[j]^Int(images_KK[i][1][j]))
      end
      images_K[i] = s
    end
    autos_extended[w] = NfRel_nsToNfRel_nsMor(K, K, Autos_abs[w], images_K)
  end
  res = restriction(K, Cp, autos_extended, incs)
  return res
  
end

function restriction(K::NfRel_ns{nf_elem}, Cp::Array{ClassField_pp, 1}, autos::Array{NfRel_nsToNfRel_nsMor, 1}, incs::Array{NfRelToNfRel_nsMor, 1})
  
  C = cyclotomic_extension(base_field(Cp[1]), maximum(degree(x) for x in Cp))
  #First, I compute the images in K of the generators of the class fields
  # and their images under the automorphisms
  gK = gens(K)
  all_pe = Array{Tuple{NfRel_nsElem, Array{NfRel_nsElem, 1}}, 1}(undef, length(Cp))
  for j = 1:length(Cp)
    pe = incs[j](Cp[j].pe)
    tau_pe = Array{NfRel_nsElem, 1}(undef, length(autos))
    for i = 1:length(tau_pe)
      tau_pe[i] = autos[i](pe)
    end
    all_pe[j] = (pe, tau_pe)
  end
  #AA is the target field 
  AA, gAA = number_field([c.A.pol for c = Cp], cached = false)
  #And now, linear algebra to compute the restriction
  #I need the product basis fo all the primitive elements of Cp
  B = Array{NfRel_nsElem, 1}(undef, degree(AA))
  B[1] = K(1)
  for i = 2:degree(Cp[1])
    B[i] = all_pe[1][1]*B[i-1]
  end
  ind = degree(Cp[1])
  for jj = 2:length(Cp)
    el = all_pe[jj][1]
    for i = 2:degree(Cp[jj])
      for j = 1:ind
        B[(i-1)* ind + j] = B[j]* el 
      end
      el *= all_pe[jj][1]
    end
    ind *= degree(Cp[jj])
  end
  #Now, I construct the corresponding sparse matrix
  M = sparse_matrix(base_field(K))
  for i = 1:degree(AA)
    push!(M, SRow(B[i]))
  end

  b_AA = basis(AA)
  Mk = _expand(M, C.mp[1])
  #@hassert :ClassField 2 nullspace(Mk')[1] == 0
  all_im = Array{Array{NfRel_nsElem{nf_elem}, 1}, 1}(undef, length(autos))
  for i = 1:length(autos)
    all_imCp = Array{NfRel_nsElem{nf_elem}, 1}(undef, length(Cp))
    for jj=1:length(Cp)
      N = SRow(all_pe[jj][2][i])
      Nk = _expand(N, C.mp[1])
      n = solve(Mk, Nk)
      im = sum(v*b_AA[l] for (l, v) = n)
      all_imCp[jj] = im
    end
    all_im[i] = all_imCp
  end
  return all_im

end


function extend_auto(KK::KummerExt, tau_a::FacElem{nf_elem, AnticNumberField}, k::Int, frob_gens::Array{NfOrdIdl, 1})

  #Compute the action of the Frobenius on the generators and on tau(a)
  imgs_rhs = Array{Int, 1}(undef, length(frob_gens))
  imgs_lhs = Array{GrpAbFinGenElem, 1}(undef, length(frob_gens))
  i = 0
  for P in frob_gens
    i += 1
    imgs_lhs[i] = can_frobenius(P, KK)
    imgs_rhs[i] = can_frobenius(P, KK, tau_a)*divexact(KK.n, k)
  end
  # Now, I have to solve the system.
  # Careful! I have to multiply the components with their difference with the exponent :(
  G = KK.AutG
  #In H, I need a copy for every relation I have
  H = DiagonalGroup([KK.n for i = 1:length(imgs_rhs)])
  imgs = Array{GrpAbFinGenElem, 1}(undef, ngens(G))
  for i = 1:length(KK.gen)
    m = Array{Int, 1}(undef, length(imgs_lhs))
    d = divexact(KK.n, order(G[i]))
    for j = 1:length(imgs_lhs)
      m[j] = imgs_lhs[j][i]*d
    end
    imgs[i] = H(m)
  end
  mp = hom(gens(G), imgs, check = true)
  b = H(imgs_rhs)
  fl, el = haspreimage(mp, b)
  @assert fl

  #Now, I need the element of the base field
  prod_gens = prod(KK.gen[i]^(-el[i]*div(Int(order(KK.AutG[i])), k)) for i = 1:length(KK.gen))
  #TODO: Compute the support before calling ispower
  prod_gens *= tau_a
  fl2, rt = ispower(prod_gens, k)
  @assert fl2
  return el, rt
  
end


function extend_aut(A::ClassField, tau::T) where T <: Map
  # tau: k -> k
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
    Tau = extend_to_cyclotomic(C, tau)
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

################################################################################
#
#  Embeddings
#
################################################################################

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

