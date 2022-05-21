################################################################################
#
#  Interface
#
################################################################################
@doc Markdown.doc"""
    absolute_automorphism_group(C::ClassField)

 Computes a generating set for the automorphisms of the
   number field corresponding to $C$. It assumes that the base field is normal.
   If "check" is true, the function checks if the extension is normal.
"""
function absolute_automorphism_group(C::ClassField, check::Bool = false)
  L = number_field(C)
  K = base_field(C)
  autK = automorphisms(K)
  @assert length(autK) == degree(K)
  if check
    @assert is_normal(C)
  end
  autK_gen = small_generating_set(autK)
  return absolute_automorphism_group(C, autK_gen)
end

function absolute_automorphism_group(C::ClassField, aut_gen_of_base_field::Vector{NfToNfMor})
  L = number_field(C)
  @vprint :ClassField 1 "Computing rel_auto "
  @vtime :ClassField 1 aut_L_rel = rel_auto(C)::Vector{NfRelNSToNfRelNSMor_nf_elem}
  if is_cyclic(C) && length(aut_L_rel) > 1
    aut = aut_L_rel[1]
    for i = 2:length(aut_L_rel)
      aut *= aut_L_rel[i]
    end
    aut_L_rel = NfRelNSToNfRelNSMor_nf_elem[aut]
  end
  @vprint :ClassField 1 "Extending automorphisms"
  @vtime :ClassField 1 rel_extend = Hecke.new_extend_aut(C, aut_gen_of_base_field)
  rel_gens = vcat(aut_L_rel, rel_extend)::Vector{NfRelNSToNfRelNSMor_nf_elem}
  C.AbsAutGrpA = rel_gens
  return rel_gens::Vector{NfRelNSToNfRelNSMor_nf_elem}
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
  M = sparse_matrix(base_field(A.K))
  b = A.K(1)
  push!(M, SRow(b))
  for i=2:degree(A)
    b *= A.pe
    push!(M, SRow(b))
  end
  tau = hom(A.K, A.K, A.bigK.zeta*gen(A.K), check = true)
  N = SRow(tau(A.pe))
  C = cyclotomic_extension(base_field(A), degree(A))
  Mk = _expand(M, pseudo_inv(C.mp[1]))
  Nk = _expand(N, pseudo_inv(C.mp[1]))
  s = solve(Mk, Nk) # will not work, matrix non-square...
  im = A.A()
  r = degree(C.Kr)
  for (i, c) = s
    setcoeff!(im, i-1, c)
  end
  return hom(A.A, A.A, im, check = false)

end

function rel_auto_intersect(A::ClassField_pp)

  # In the computation of the class field, I saved the
  # automorphisms of A.K over k.
  # Now, I have to search for the one that generates the Galois
  # group of the target field over k
  C = cyclotomic_extension(base_field(A), degree(A))
  if !isdefined(A, :AutG)
    _aut_A_over_k(C, A)
  end
  G, mG = snf(abelian_group(A.AutR))
  #Now, I restrict them to A.A
  M = sparse_matrix(base_field(A.K))
  b = A.K(1)
  push!(M, SRow(b))
  for i = 2:degree(A)
    b *= A.pe
    push!(M, SRow(b))
  end
  Mk = _expand(M, pseudo_inv(C.mp[1]))
  # One of the automorphisms must generate the group, so I check the order.
  for j = 1:ngens(G)
    if !divisible(G.snf[j], fmpz(degree(A)))
      continue
    end
    #Construct the automorphism
    gener = mG(G[j])
    elem = A.pe
    for i = 1:ncols(A.AutR)
      if !iszero(gener[i])
        for s = 1:Int(gener[i])
          elem = A.AutG[i](elem)
        end
      end
    end
    N = SRow(elem)
    Nk = _expand(N, pseudo_inv(C.mp[1]))
    s = solve(Mk, Nk) # will not work, matrix non-square...
    im = A.A()
    for (i, c) = s
      setcoeff!(im, i-1, c)
    end
    return hom(A.A, A.A, im, check = false)
  end
  error("I can't find the automorphism!")

end

function rel_auto_generic(A::ClassField_pp)
  K = A.A
  imgs = roots(K.pol, K)
  homs = morphism_type(K)[hom(K, K, x, check = false) for x in imgs]
  return small_generating_set(homs, *)[1]
end


function rel_auto(A::ClassField_pp)
  @assert isdefined(A, :A)
  if !isdefined(A, :K)
    return rel_auto_generic(A)
  elseif degree(A) == degree(A.K)
    #If the cyclotomic extension and the target field are linearly disjoint, it is easy.
    return rel_auto_easy(A)
  else
    #Tricky case
    return rel_auto_intersect(A)
  end
end

function rel_auto(A::ClassField)
  aut = Vector{morphism_type(NfRel{nf_elem})}(undef, length(A.cyc))
  for i = 1:length(aut)
    aut[i] = rel_auto(A.cyc[i])
  end
  K = number_field(A)
  g = gens(K)
  Aut = Vector{morphism_type(K)}(undef, length(aut))
  for i = 1:length(aut)
    imgs = Vector{NfRelNSElem{nf_elem}}(undef, length(aut))
    for j = 1:length(imgs)
      if j == i
        imgs[j] = image_primitive_element(aut[i]).data(g[j])
      else
        imgs[j] = g[j]
      end
    end
    Aut[i] = hom(K, K, imgs)
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

Given a cyclotomic extension $C$ of a number field $K$ and an automorphism $\tau$ of $K$,
  computes an extension of $\tau$ to $C$.

"""
function extend_to_cyclotomic(C::CyclotomicExt, tau::NfToNfMor)
  K = domain(tau)
  @assert K == base_field(C.Kr)
  gKr = gen(C.Kr)
  if euler_phi(C.n) == degree(C.Kr)
    #The extension with the roots of unity is disjoint from K
    #Therefore, the minimal polynomial has coefficient over QQ.
    return hom(C.Kr, C.Kr, tau, gKr)
  end
  g = C.Kr.pol
  tau_g = parent(g)([tau(coeff(g, i)) for i=0:degree(g)])
  i = 1
  z = deepcopy(gKr)
  while gcd(i, C.n) != 1 || !iszero(tau_g(z))
    i += 1
    mul!(z, z, gKr)
  end
  return hom(C.Kr, C.Kr, tau, z)

end

function new_extend_aut(A::ClassField, auto::T) where T <: Map
  return new_extend_aut(A, T[auto])[1]
end

function new_extend_aut(A::ClassField, autos::Vector{T}) where T <: Map
  # tau: k -> k
  k = domain(autos[1])
  @assert k == codomain(autos[1])
  @assert k == base_field(A)
  lp = factor(fmpz(degree(A)))
  L = number_field(A)
  # I call number field because to extend the automorphism I need the defining polynomials
  all_imgs = Vector{Vector{NfRelNSElem{nf_elem}}}(undef, length(autos))
  #Initialize the array
  for i=1:length(autos)
    all_imgs[i] = Vector{NfRelNSElem{nf_elem}}(undef, length(A.cyc))#[L() for i=1:length(A.cyc)]
  end
  lG = gens(L)
  #P-Sylow subgroups are invariant, I can reduce to the prime power case.
  res = Vector{NfRelNSToNfRelNSMor_nf_elem}(undef, length(autos))
  for (p, v) = lp.fac
    @vprint :ClassField 1 "Extending auto pp ..."
    @vtime :ClassField 1 imgs = extend_aut_pp(A, autos, p)
    # The output are the images of the cyclic components in A.A
    indices = Vector{Int}(undef, length(imgs[1]))
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
    emb = hom(Ap, L, NfRelNSElem{nf_elem}[lG[indices[i]] for i = 1:length(indices)])
    for j = 1:length(autos)
      for i = 1:length(imgs[j])
        all_imgs[j][indices[i]] = emb(imgs[j][i])
      end
    end
  end
  for i = 1:length(res)
    res[i] = hom(L, L, autos[i], all_imgs[i])
    #@hassert :NfOrd 1 is_consistent(res[i])
  end
  return res

end

################################################################################
#
#  Frobenius generating the automorphisms of the Kummer extension
#
################################################################################

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
  cp = lcm([discriminant(O), minimum(m, copy = false), index(O), index(O1)])
  P = ideal(O, 1)
  for p in Sp
    if cp % p == 0
      continue
    end
    lp = prime_decomposition(O1, p)
    for i = 1:length(lp)
      try
        z = canonical_frobenius(lp[i][1], K1)
        if order(z) != d
          continue
        end
        lP = prime_decomposition_nonindex(emb, lp[i][1])
        P = lP[1][1]
        zK = canonical_frobenius(P, K)
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
        zK1 = canonical_frobenius(lp[i][1], K1)
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

#Finds prime such that the Frobenius automorphisms generate the automorphism group of the kummer extension
function find_gens(KK::KummerExt, gens_imgs::Vector{Vector{FacElem{nf_elem, AnticNumberField}}}, coprime_to::fmpz, idx::Int = 1)
  K = base_field(KK)
  O = maximal_order(K)
  els = GrpAbFinGenElem[]
  Q, mQ = quo(KK.AutG, els, false)
  s, ms = snf(Q)
  Sp = Hecke.PrimesSet(1000, -1)
  cp = lcm(discriminant(O), coprime_to)
  frob_gens = NfOrdIdl[]
  for q in Sp
    if cp % q == 0
      continue
    end
    lp = prime_decomposition(O, q)
    for i = 1:length(lp)
      try
        z = canonical_frobenius(lp[i][1], KK)
        el_in_quo = ms\(mQ(z))
        if iszero(el_in_quo)
          continue
        end
        found = false
        for i = 1:ngens(s)
          if is_coprime(s.snf[i], el_in_quo[i])
            found = true
            break
          end
        end
        if !found
          continue
        end
        for x in gens_imgs
          for y in x
            canonical_frobenius(lp[i][1], KK, y)
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
      Q, mQ = quo(KK.AutG, els, false)
      s, ms = snf(Q)
      if order(s) == idx
        break
      end
    end
    if order(s) == idx
      break
    end
  end
  return frob_gens
end

#extension of automorphisms in the case of extensions of exponent 2
function extend_aut2(A::ClassField, autos::Vector{NfToNfMor})
  Cp = [x for x in A.cyc if degree(x) % 2 == 0]
  autos_extended = Vector{Vector{NfRelNSElem{nf_elem}}}(undef, length(autos))
  AA, gAA = number_field([c.A.pol for c in Cp], check = false)
  if length(Cp) == 1
    for i = 1:length(autos)
      fl, el = is_power(autos[i](Cp[1].a)*inv(Cp[1].a), 2)
      @assert fl
      autos_extended[i] = NfRelNSElem{nf_elem}[AA(evaluate(el))*gAA[1]]
    end
    return autos_extended
  end
  KK = kummer_extension([2 for i = 1:length(Cp)], [x.a for x in Cp])
  act_on_gens = Vector{Vector{FacElem{nf_elem, AnticNumberField}}}(undef, length(KK.gen))
  for i = 1:length(KK.gen)
    act_on_gen_i = Vector{FacElem{nf_elem, AnticNumberField}}(undef, length(autos))
    for j = 1:length(autos)
      act_on_gen_i[j] = FacElem(Dict(autos[j](ke) => v for (ke, v) in KK.gen[i]))
    end
    act_on_gens[i] = act_on_gen_i
  end
  frob_gens = find_gens(KK, act_on_gens, minimum(defining_modulus(A)[1]))
  #I will compute a possible image cyclic component by cyclic component
  for w = 1:length(autos)
    images_KK = Vector{Tuple{GrpAbFinGenElem, FacElem{nf_elem, AnticNumberField}}}(undef, length(Cp))
    for i = 1:length(Cp)
      fl, coord, rt = _find_embedding(KK, act_on_gens[i][w], 2, frob_gens)
      @assert fl
      images_KK[i] = (coord, rt)
    end

    #Now, I can define the automorphism on AA
    images_K = Vector{NfRelNSElem{nf_elem}}(undef, length(images_KK))
    for i = 1:length(images_K)
      s = AA(evaluate(images_KK[i][2]))
      for j = 1:length(Cp)
        mul!(s, s, gAA[j]^Int(images_KK[i][1][j]))
      end
      images_K[i] = s
    end
    autos_extended[w] = images_K
  end
  return autos_extended

end

function extend_generic(A::ClassField, autos::Vector{NfToNfMor}, p::fmpz)
  Cp = [x1 for x1 in A.cyc if degree(x1) % Int(p) == 0]
  A, gA = number_field([c.A.pol for c in Cp], check = false)
  rts = Vector{Vector{NfRelNSElem{nf_elem}}}(undef, length(autos))
  for i = 1:length(autos)
    imgs = Vector{NfRelNSElem{nf_elem}}(undef, length(Cp))
    for j = 1:length(gA)
      pol = map_coefficients(autos[i], Cp[j].A.pol)
      imgs[j] = roots(pol, A)[1]
    end
    rts[i] = imgs
  end
  return rts
end

function check_disjoint_cyclotomic(A::ClassField, p::fmpz)
  e = ppio(fmpz(exponent(A)), p)[1]
  K = base_field(A)
  mr = A.rayclassgroupmap
  mq = A.quotientmap
  x = PolynomialRing(FlintZZ, "x")[2]
  f = cyclotomic(Int(e), x)
  fK = map_coefficients(K, f)
  s, ms = norm_group(fK, mr, false, cached = false)
  mp = ms*mq
  i, mi = image(mp)
  return Int(divexact(order(codomain(mq)), order(i)))
end

function extend_aut_pp(A::ClassField, autos::Vector{NfToNfMor}, p::fmpz)
  Cp = [x1 for x1 in A.cyc if degree(x1) % Int(p) == 0]
  if !all(x -> isdefined(x, :a), Cp)
    return extend_generic(A, autos, p)
  end
  d = maximum(degree(x) for x in Cp)
  if d == 2
    return extend_aut2(A, autos)
  end

  m = minimum(defining_modulus(A)[1])
  ind_image = 1
  if !isone(gcd(d, m)) && d != minimum(degree(x) for x in Cp)
    #Difficult case. First, we check that the extension and
    #the cyclotomic extension are disjoint
    ind_image = check_disjoint_cyclotomic(A, p)
    if !isone(ind_image)
      return extend_autos_hard_case(A, autos, p, ind_image)
    end
  end

  AA, gAA = number_field([c.A.pol for c in Cp], check = false)
  #Main Idea: I extend tau to the big kummer extension KK and then I restrict it to AA.
  k = base_field(A)
  C = cyclotomic_extension(k, d)
  KC = absolute_simple_field(C)
  # C is the base field of the kummer extension generated
  # by all the cyclic components.
  # I extend the automorphisms to C

  Autos_abs = Vector{NfToNfMor}(undef, length(autos))
  for i = 1:length(autos)
    aut = extend_to_cyclotomic(C, autos[i])
    Autos_abs[i] = hom(KC, KC, C.mp[1]\(aut(C.mp[1](gen(KC)))), check = false)
  end

  #I compute the embeddings of the small cyclotomic extensions into the others
  abs_emb = Vector{NfToNfMor}(undef, length(Cp))
  for i = 1:length(Cp)
    dCp = degree(Cp[i])
    if dCp == d
      abs_emb[i] = id_hom(KC)
    else
      Cs = cyclotomic_extension(k, dCp)
      emb = hom(Cs.Kr, C.Kr, gen(C.Kr)^div(d, dCp), check = false)
      img = C.mp[1]\(emb(Cs.mp[1](gen(Cs.Ka))))
      abs_emb[i] = hom(Cs.Ka, KC, img, check = false)
    end
  end

  #Now, I can compute the corresponding Kummer extension over the big cyclotomic field.
  exps = Vector{Int}(undef, length(Cp))
  gens = Vector{FacElem{nf_elem, AnticNumberField}}(undef, length(Cp))
  for i = 1:length(Cp)
    if degree(Cp[i]) == d
      gens[i] = Cp[i].a
      exps[i] = Cp[i].o
    else
      D = Dict{nf_elem, fmpz}()
      for (ke,v) in Cp[i].a
        D[abs_emb[i](ke)] = v
      end
      a = FacElem(D)
      exps[i] = Cp[i].o
      gens[i] = a
    end
  end
  KK = kummer_extension(exps, gens)
  K, gK = number_field(KK)
  #I need the inclusions of the single extensions Cp[i].K in K
  incs = Vector{NfRelToNfRelNSMor_nf_elem}(undef, length(Cp))
  for i = 1:length(Cp)
    incs[i] = hom(Cp[i].K, K, abs_emb[i], gK[i])
  end

  # I want extend the automorphisms to KK
  # First, I find a set of primes such that their Frobenius generates the Galois group of KK
  act_on_gens = Vector{Vector{FacElem{nf_elem, AnticNumberField}}}(undef, length(KK.gen))
  for i = 1:length(KK.gen)
    act_on_gen_i = Vector{FacElem{nf_elem, AnticNumberField}}(undef, length(autos))
    for j = 1:length(autos)
      D1 = Dict{nf_elem, fmpz}()
      for (ke, v) in KK.gen[i]
        D1[Autos_abs[j](ke)] = v
      end
      act_on_gen_i[j] = FacElem(D1)
    end
    act_on_gens[i] = act_on_gen_i
  end
  frob_gens = find_gens(KK, act_on_gens, minimum(defining_modulus(A)[1]))

  autos_extended = Vector{morphism_type(K, K)}(undef, length(autos))
  #I will compute a possible image cyclic component by cyclic component
  for w = 1:length(autos)
    images_KK = Vector{Tuple{GrpAbFinGenElem, FacElem{nf_elem, AnticNumberField}}}(undef, length(Cp))
    for i = 1:length(Cp)
      fl, coord_img_emb, rt_img_emb = _find_embedding(KK, act_on_gens[i][w], Int(order(KK.AutG[i])), frob_gens)
      @assert fl
      images_KK[i] = (coord_img_emb, rt_img_emb)
    end

    #Now, I can define the automorphism on K
    images_K = Vector{NfRelNSElem{nf_elem}}(undef, length(images_KK))
    for i = 1:length(images_K)
      s = K(evaluate(images_KK[i][2]))
      for j = 1:length(Cp)
        mul!(s, s, gK[j]^Int(images_KK[i][1][j]))
      end
      images_K[i] = s
    end
    autos_extended[w] = hom(K, K, Autos_abs[w], images_K)
    #@hassert :NfOrd 1 is_consistent(autos_extended[w])
  end
  res = restriction(K, Cp, autos_extended, incs)
  return res

end

###############################################################################
#
#  Restriction of automorphisms
#
###############################################################################

#This function restricts the automorphisms in autos to the number field generated by the class fields in Cp
# incs are the inclusions of the class fields in K
function restriction(K::NfRelNS{nf_elem}, Cp::Vector{ClassField_pp{S, T}}, autos::Vector{NfRelNSToNfRelNSMor_nf_elem}, incs::Vector{NfRelToNfRelNSMor_nf_elem}) where {S, T}

  C = cyclotomic_extension(base_field(Cp[1]), maximum(degree(x) for x in Cp))
  #First, I compute the images in K of the generators of the class fields
  # and their images under the automorphisms
  gK = gens(K)
  all_pe = Vector{Tuple{NfRelNSElem{nf_elem}, Vector{NfRelNSElem{nf_elem}}}}(undef, length(Cp))
  for j = 1:length(Cp)
    pe = incs[j](Cp[j].pe)
    tau_pe = Vector{typeof(pe)}(undef, length(autos))
    for i = 1:length(tau_pe)
      tau_pe[i] = autos[i](pe)
    end
    all_pe[j] = (pe, tau_pe)
  end
  #AA is the target field
  AA, gAA = number_field([c.A.pol for c = Cp], cached = false, check = false)
  #And now, linear algebra to compute the restriction
  #I need the product basis fo all the primitive elements of Cp
  B = Vector{NfRelNSElem}(undef, degree(AA))
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
  for i = 1:length(B)
    push!(M, SRow(B[i]))
  end

  b_AA = basis(AA)
  Mk = _expand(M, pseudo_inv(C.mp[1]))
  all_im = Vector{Vector{NfRelNSElem{nf_elem}}}(undef, length(autos))
  for i = 1:length(autos)
    all_imCp = Vector{NfRelNSElem{nf_elem}}(undef, length(Cp))
    for jj=1:length(Cp)
      N = SRow(all_pe[jj][2][i])
      Nk = _expand(N, pseudo_inv(C.mp[1]))
      n = solve(Mk, Nk)
      im = sum(v*b_AA[l] for (l, v) = n)
      all_imCp[jj] = im
    end
    all_im[i] = all_imCp
  end
  return all_im

end

function _find_embedding(KK::KummerExt, el::FacElem{nf_elem, AnticNumberField}, ord_el::Int, frob_gens::Vector{NfOrdIdl})
  #Compute the action of the Frobenius on the generators and on tau(a)
  imgs_rhs = Vector{Int}(undef, length(frob_gens))
  imgs_lhs = Vector{GrpAbFinGenElem}(undef, length(frob_gens))
  i = 0
  for P in frob_gens
    i += 1
    imgs_lhs[i] = canonical_frobenius(P, KK)
    imgs_rhs[i] = canonical_frobenius(P, KK, el)*divexact(KK.n, ord_el)
  end
  # Now, I have to solve the system.
  # Careful! I have to multiply the components with their difference with the exponent :(
  G = KK.AutG
  #In H, I need a copy for every relation I have
  H = abelian_group(fmpz[KK.n for i = 1:length(imgs_rhs)])
  imgs = Vector{GrpAbFinGenElem}(undef, ngens(G))
  for i = 1:length(KK.gen)
    m = Vector{Int}(undef, length(imgs_lhs))
    d = divexact(KK.n, order(G[i]))
    for j = 1:length(imgs_lhs)
      m[j] = imgs_lhs[j][i]*d
    end
    imgs[i] = H(m)
  end
  mp = hom(gens(G), imgs, check = true)
  b = H(imgs_rhs)
  fl, coord = haspreimage(mp, b)
  if !fl
    return false, coord, el
  end

  #Now, I need the element of the base field
  prod_gens = KK.gen[1]^(div(-coord[1]*ord_el, Int(order(KK.AutG[1]))))
  for i = 2:length(KK.gen)
    mul!(prod_gens, prod_gens, KK.gen[i]^(div(-coord[i]*ord_el, Int(order(KK.AutG[i])))))
  end
  mul!(prod_gens, prod_gens, el)
  fl2, rt = is_power(prod_gens, ord_el, with_roots_unity = true)
  return fl2, coord, rt
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
    Cp = [Ap for Ap = A.cyc if degree(Ap) % Int(p) == 0]
    Dp = [Bp for Bp = B.cyc if degree(Bp) % Int(p) == 0]
    h = [extend_hom(X, Cp, tau) for x = Dp]
  end
end

function extend_hom(C::ClassField_pp, D::Vector{ClassField_pp}, tau)
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
    @show tau_Ka = hom(Cy.Ka, Dy.Ka, Dy.mp[1]\(Tau(Cy.mp[1](gen(Cy.Ka)))), check = false)

    lp = collect(keys(D[im].bigK.frob_cache))
    pp = maximum(minimum(x) for x = lp)
    S = Base.Iterators.flatten((lp, PrimeIdealsSet(order(lp[1]), pp, fmpz(-1), indexdivisors=false, ramified=false, degreebound = 1)))

    @assert Dy.Ka == base_field(D[im].K)

    all_s = []
    all_tau_s = []
    all_emb = []
    for c in D
#      println("om: $om -> ", degree(c), " vs ", c.o)
      Cs = cyclotomic_extension(k2, Int(degree(c)))
      Emb = hom(Cs.Kr, Dy.Kr, gen(Dy.Kr)^div(om, degree(c)), check = false)
      emb = Cs.mp[1] * Emb * pseudo_inv(Dy.mp[1])
      a = FacElem(Dict(emb(k) => v for (k,v) = c.a.fac))
      push!(all_emb, (a, emb, divexact(om, c.o)))
    end
    b = FacElem(Dict(tau_Ka(k) => v for (k,v) = C.a.fac))

    G = abelian_group([om for i=1:length(D[im].bigK.gen)])
    Q, mQ = quo(G, elem_type(G)[])
    U = abelian_group([om for i = D])
    s_gen = elem_type(U)[]
    tau_b = fmpz[]

    for p = S
      local f
      local fa
      local tfa
      try
        f = canonical_frobenius(p, D[im].bigK).coeff
        fa = [canonical_frobenius(p, D[im].bigK, a[1]) for a = all_emb]
        tfa = canonical_frobenius(p, D[im].bigK, b)
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

    T_grp = abelian_group([om for i= s_gen])
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
    fl, rt = is_power(mu, divexact(C.o, Int(t_corr_b)))
    @assert fl
    all_b = (evaluate(rt), lf)

    Ka = Dy.Ka
    KaT, X = PolynomialRing(Ka, "T", cached = false)
    KK, gKK = number_field([X^Int(divexact(D[j].o, t_corr[j])) - root(evaluate(all_emb[j][1]), Int(t_corr[j])) for j=1:length(D)], check = false)
    s = gKK[1]
    s = s^Int(divexact(D[1].o, C.o)*all_b[2][1])
    for j in 2:length(D)
      s = s * gKK[j]^Int(divexact(D[j].o, C.o)*all_b[2][j])
    end
    h = NfRelToNfRelNSMor(C.K, KK, tau_Ka, inv(all_b[1]) * s)

    # now "all" that remains is to restrict h to the subfield, using lin. alg..

    all_pe = []
    for jj=1:length(D)
      emb = hom(D[jj].K, KK, tau_Ka, gens(KK)[jj], check = false)
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
    AA, gAA = number_field([c.A.pol for c = D], check = false)
    @assert d == degree(AA)
    @assert d == length(B)
    b_AA = basis(AA)
    Mk = _expand(M, pseudo_inv(Dy.mp[1]))
    #@hassert :ClassField 2 nullspace(transpose(Mk))[1] == 0
    N = SRow(h(C.pe))
    Nk = _expand(N, pseudo_inv(Dy.mp[1]))
    n = solve(Mk, Nk)
    all_im = sum(v*b_AA[l] for (l, v) = n)

      return all_im

      #=

    im = NfRelNSElem{nf_elem}[]
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
    emb = NfRelNSToNfRelNSMor(KK, A.A, im)
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
  return NfRelNSToNfRelNSMor(A.A, A.A, tau, all_h)
  =#
end

#M is over K, mp: K -> K/k, expand M into a matrix over k
function _expand(M::Generic.Mat{nf_elem}, mp::Map)
  Kr = domain(mp)
  Ka = codomain(mp)
  k = base_field(Kr)
  d = degree(Kr)
  N = zero_matrix(k, nrows(M), ncols(M) * d)
  for i=1:nrows(M)
    for j = 1:ncols(M)
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
  k = base_field(Kr)
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
  k = base_field(Kr)
  N = sparse_matrix(k)
  for i=1:nrows(M)
    sr = _expand(M[i], mp)
    push!(N, sr)
  end
  return N
end

################################################################################
#
#  Extend auto - intersection with cyclotomic extension not trivial
#
################################################################################

function extend_autos_hard_case(A::ClassField, autos::Vector{NfToNfMor}, p::fmpz, deg_intersection::Int)
  error("Not yet implemented")
  Cp = [x1 for x1 in A.cyc if degree(x1) % Int(p) == 0]
  k = base_field(A)
  C = cyclotomic_extension(k, d)
  KC = absolute_simple_field(C)
  # C is the base field of the kummer extension generated
  # by all the cyclic components.
  # I extend the automorphisms to C
  Autos_abs = Vector{NfToNfMor}(undef, length(autos))
  for i = 1:length(autos)
    aut = extend_to_cyclotomic(C, autos[i])
    Autos_abs[i] = hom(KC, KC, C.mp[1]\(aut(C.mp[1](gen(KC)))), check = false)
  end

  #I compute the embeddings of the small cyclotomic extensions into the others
  abs_emb = Vector{NfToNfMor}(undef, length(Cp))
  for i = 1:length(Cp)
    dCp = degree(Cp[i])
    if dCp == d
      abs_emb[i] = id_hom(KC)
    else
      Cs = cyclotomic_extension(k, dCp)
      emb = hom(Cs.Kr, C.Kr, gen(C.Kr)^div(d, dCp), check = false)
      img = C.mp[1]\(emb(Cs.mp[1](gen(Cs.Ka))))
      abs_emb[i] = hom(Cs.Ka, KC, img, check = false)
    end
  end

  #Now, I can compute the corresponding Kummer extension over the big cyclotomic field.
  exps = Vector{Int}(undef, length(Cp))
  gens = Vector{FacElem{nf_elem, AnticNumberField}}(undef, length(Cp))
  for i = 1:length(Cp)
    if degree(Cp[i]) == d
      gens[i] = Cp[i].a
      exps[i] = Cp[i].o
    else
      D = Dict{nf_elem, fmpz}()
      for (ke,v) in Cp[i].a
        D[abs_emb[i](ke)] = v
      end
      a = FacElem(D)
      exps[i] = Cp[i].o
      gens[i] = a
    end
  end
  KK = kummer_extension(exps, gens)
  #Now, KK is not a real kummer extension. There are relations. We need to find them.
  #We know that the right degree of the translation of Cp to C is degree(Cp)/idx
  #So we compute Frobenius automorphisms until we generate a subgroup with the right subgroup.

  act_on_gens = Vector{Vector{FacElem{nf_elem, AnticNumberField}}}(undef, length(KK.gen))
  for i = 1:length(KK.gen)
    act_on_gen_i = Vector{FacElem{nf_elem, AnticNumberField}}(undef, length(autos))
    for j = 1:length(autos)
      D1 = Dict{nf_elem, fmpz}()
      for (ke, v) in KK.gen[i]
        D1[Autos_abs[j](ke)] = v
      end
      act_on_gen_i[j] = FacElem(D1)
    end
    act_on_gens[i] = act_on_gen_i
  end
  frob_gens = find_gens(KK, act_on_gens, minimum(defining_modulus(A)[1]), deg_intersection)
  #Now, I can create a proper kummer extension.
  s, ms = sub(KK.AutG, GrpAbFinGenElem[canonical_frobenius(x, KK) for x in frob_gens])
  @assert order(s) == divexact(order(KK.AutG), deg_intersection)
  S, mS = snf(s)
  gens_real_KK = Vector{FacElem{nf_elem, AnticNumberField}}(undef, ngens(S))
  for i = 1:ngens(S)
    imgSi = mS(S[i])
    gens_real_KK[i] = prod(KK.gens[j]^imgSi[j] for j = 1:ngens(KK))
  end
  KK_real = kummer_extension(gens_real_KK, S.snf)
  new_act_on_gens = Vector{Vector{FacElem{nf_elem, AnticNumberField}}}(undef, length(KK.gen))
  for i = 1:length(KK.gen)
    act_on_gen_i = Vector{FacElem{nf_elem, AnticNumberField}}(undef, length(autos))
    for j = 1:length(autos)
      D1 = Dict{nf_elem, fmpz}()
      for (ke, v) in KK.gen[i]
        D1[Autos_abs[j](ke)] = v
      end
      act_on_gen_i[j] = FacElem(D1)
    end
    new_act_on_gens[i] = act_on_gen_i
  end
  @show find_frob = find_gens(KK_real, new_act_on_gens, minimum(defining_modulus(A)[1]))
  error("stop")
  AA, gAA = number_field(KK_real)
  #I now need the embedding of Cp into KK_real



end
