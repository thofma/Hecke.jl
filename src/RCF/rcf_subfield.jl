function number_field_over_subfield(C::ClassField_pp; using_norm_relation::Bool = true, using_stark_units::Bool = false)
  K = base_field(C)
  subs = principal_subfields(K)
  subs = [x for x in subs if degree(x[1]) != degree(K)]
  if isempty(subs)
    if using_norm_relation
      return ray_class_field_cyclic_pp_Brauer(C)
    else
      return ray_class_field_cyclic_pp(C)
    end
  end
  fl = false
  fl, C1 = translate_extension(subs[1][2], C)
  i = 1
  while !fl && i <= length(subs)-1
    i += 1
    fl, C1 = translate_extension(subs[i][2], C)
  end
  if !fl
    if using_norm_relation
      return ray_class_field_cyclic_pp_Brauer(C)
    else
      return ray_class_field_cyclic_pp(C)
    end
  end
  number_field_over_subfield(C1)
  translate_up(subs[i][2], C, C1)
  return C
end


function translate_extension(mL::NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}, C::ClassField_pp)
  L = domain(mL)
  OL = maximal_order(L)
  K = codomain(mL)
  OK = maximal_order(K)
  n = Int(exponent(C))
  ordext = Int(degree(C))
  d = divexact(discriminant(OK), discriminant(OL)^(divexact(degree(K), degree(L))))
  f = factor(ideal(OL, d))
  F = factor(ideal(OK, d))
  mR = C.rayclassgroupmap
  fM0 = copy(factored_modulus(C))
  fm0 = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}()
  for (p, v) in fM0
    p1 = Hecke.intersect_prime(mL, p)
    if !haskey(fm0, p1)
      if is_coprime(minimum(p1, copy = false), n)
        fm0[p1] = 1
      else
        fm0[p1] = v
      end
    end
    ep = divexact(ramification_index(p), ramification_index(p1))
    fM0[p] = ep*v
  end
  #Now, I have problems, so I need to add the ramification of the other extension.
  for (p, v) in f
    if !haskey(fm0, p)
      if isone(gcd(minimum(p), n))
        fm0[p] = 1
      else
        fm0[p] = v
      end
    else
      if !isone(gcd(minimum(p), n))
        fm0[p] = max(v, fm0[p])
      end
    end
    lPP = prime_decomposition(mL, p)
    for (P, vP) in lPP
      if haskey(fM0, P)
        fM0[P] = max(fM0[P], 2*vP*fm0[p])
      else
        fM0[P] = vP*fm0[p]*2
      end
    end
  end
  infplc = InfPlc[]
  if iszero(mod(n, 2))
    infplc = real_places(L)
  end
  @vprintln :ClassField 3 "Checking if I can compute the field over a subfield"
  r, mr = Hecke.ray_class_group(OL, fm0, infplc, n_quo = n)
  if exponent(r) < n || order(r) < degree(C)
    return false, C
  end
  #Now, the norm group of K over L
  @vtime :ClassField 3 ngL, mngL = Hecke.norm_group(mL, mr)
  @hassert :ClassField 1 is_divisible_by(divexact(ZZRingElem(degree(codomain(mL))), degree(domain(mL))), divexact(order(r), order(ngL)))
  if !is_divisible_by(order(ngL), degree(C)) || !is_divisible_by(exponent(C), n)
    return false, C
  end
  #Finally, the norm group of C over L
  #I use the usual strategy, as in check_abelian_extension
  for (p, v) in F
    if is_coprime(minimum(p, copy = false), degree(C))
      fM0[p] = 1
    else
      if haskey(fM0, p)
        fM0[p] = max(v, fM0[p])
      else
        fM0[p] = v
      end
    end
  end
  inf_plc2 = InfPlc[]
  if !isempty(infplc)
    inf_plc2 = real_places(K)
  end
  @vtime :ClassField 3 RM, mRM = ray_class_group(OK, fM0, inf_plc2, n_quo = n)
  @vtime :ClassField 3 lP, gS = Hecke.find_gens(mRM, coprime_to = minimum(defining_modulus(mR)[1]))
  listn = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[norm(mL, x) for x in lP]
  # Create the map between R and r by taking norms
  preimgs = Vector{FinGenAbGroupElem}(undef, length(listn))
  for i = 1:length(preimgs)
    preimgs[i] = mr\listn[i]
  end
  proj = hom(gS, preimgs)
  #compute the norm group of C in RM
  prms = Vector{FinGenAbGroupElem}(undef, length(lP))
  for i = 1:length(lP)
    prms[i] = C.quotientmap(mR\lP[i])
  end
  RMtoR = hom(gS, prms)
  k, mk = kernel(RMtoR, false)
  @hassert :ClassField 1 is_isomorphic(cokernel(mk, false)[1], codomain(C.quotientmap))
  mp = mk*proj
  ck, mck = cokernel(mp, false)
  #If everything could work, then ck should be the direct product of the abelian extension I am searching for and
  #the maximal abelian subextension of K/L
  G1 = snf(cokernel(mngL, false)[1])[1]
  G2 = snf(codomain(C.quotientmap))[1]
  if !has_quotient(ck, map(Int, vcat(G1.snf, G2.snf)))
    return false, C
  end
  s, ms = image(mngL*mck, false)
  fl, ms1 = has_complement(ms)
  @assert fl
  mq1 = cokernel(ms1, false)[2]
  mqq = mck * mq1
  @hassert :ClassField 1 domain(mqq) == r
  C1 = ClassField_pp{MapRayClassGrp, FinGenAbGroupHom}()
  C1.quotientmap = mqq
  C1.rayclassgroupmap = mr
  return true, C1
end


function translate_up(mL::NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}, C::ClassField_pp, C1::ClassField_pp)
  K = base_field(C)
  Ky = polynomial_ring(K, "y", cached = false)[1]
  L = domain(mL)
  d = degree(C1)
  CEK = cyclotomic_extension(K, d)
  CEL = cyclotomic_extension(L, d)
  img = gen(CEK.Kr)
  if degree(CEK.Kr) != euler_phi(d)
    pp = map_coefficients(mL, CEL.Kr.pol, cached = false)
    while !iszero(pp(img))
      mul!(img, img, gen(CEK.Kr))
    end
  end
  mrel = hom(CEL.Kr, CEK.Kr, mL, img)
  #@hassert :Fields 1 is_consistent(mrel)
  g = mrel(CEL.mp[1](gen(CEL.Ka)))
  mp = hom(CEL.Ka, CEK.Ka, CEK.mp[1]\(g), check = false)
  #Then, the fac elem corresponding to the generator of the Kummer Extension
  C.a = FacElem(Dict{AbsSimpleNumFieldElem, ZZRingElem}(mp(x) => v for (x, v) in C1.a))
  #Now, the Kummer extension
  Lzeta = codomain(mp)
  Lt = polynomial_ring(Lzeta, "t", cached = false)[1]
  d1 = degree(C1.K)
  coeffs = Vector{AbsSimpleNumFieldElem}(undef, d1 + 1)
  coeffs[1] = mp(coeff(C1.K.pol, 0))
  for s = 2:length(coeffs)-1
    coeffs[s] = zero(Lzeta)
  end
  coeffs[end] = one(Lzeta)
  C.K = number_field(Lt(coeffs), cached = false, check = false)[1]
  #The target extension
  fdef = map_coefficients(mL, C1.A.pol, parent = Ky, cached = false)
  C.A = number_field(fdef, cached = false, check = false)[1]
  #Now, the primitive element of the target extension seen in Cpp.K
  mrel2 = hom(C1.K, C.K, mp, gen(C.K))
  C.pe = mrel2(C1.pe)
  CEKK = cyclotomic_extension(K, d)
  @hassert :ClassField 1 iszero(map_coefficients(CEKK.mp[2], fdef, cached = false)(C.pe))
  C.o = d1
  return nothing
end
