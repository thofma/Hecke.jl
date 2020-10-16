################################################################################
#
#  final computation of the maximal order and automorphisms
#
################################################################################


function _simplify_components(L::Hecke.NfRelNS{nf_elem}, autL::Vector{Hecke.NfRelNSToNfRelNSMor{nf_elem}})
  if ngens(L) == 1
    return L, autL
  end
  to_simplify = Int[]
  for i = 1:length(L.pol)
    if total_degree(L.pol[i]) > 2
      push!(to_simplify, i)
    end
  end
  if isempty(to_simplify)
    return L, autL
  end
  pols = Vector{Generic.Poly{nf_elem}}(undef, ngens(L))
  maps = Vector{NfRelNSElem{nf_elem}}(undef, ngens(L))
  for i = 1:length(pols)
    Li, mLi = component(L, i)
    if !(i in to_simplify)
      pols[i] = Li.pol
      maps[i] = L[i]
      continue
    end
    Linew, mLinew = simplify(Li)
    pols[i] = Linew.pol
    maps[i] = mLi(mLinew.prim_img)
  end
  Lnew, gLnew = number_field(pols, cached = false, check = false)
  iso = hom(Lnew, L, maps)
  inv_iso = inv(iso) 
  autsLnew = Vector{Hecke.NfRelNSToNfRelNSMor{nf_elem}}(undef, length(autL))
  for i = 1:length(autL)
    autsLnew[i] = iso*autL[i]*inv_iso
  end
  return Lnew, autsLnew
end


function _from_relative_to_abs_with_embedding(L1::Hecke.NfRelNS{nf_elem}, autL1::Array{Hecke.NfRelNSToNfRelNSMor{nf_elem}, 1}, use_simplify::Bool = true)
  if use_simplify 
    @vtime :Fields 3 L, autL = _simplify_components(L1, autL1)
  else
    L, autL = L1, autL1
  end
  S, mS = simple_extension(L)
  K, mK, MK = absolute_field(S, cached = false)
  #First, we compute the maximal order of the absolute field.
  #We start from the maximal orders of the relative extension and of the base field.
  #FALSE: Since the computation of the relative maximal order is slow, I prefer to bring to the absolute field the elements
  # generating the equation order.
  pols = L.pol
  gL = gens(L)
  B = Array{nf_elem, 1}(undef, degree(K))
  B[1] = K(1)
  ind = total_degree(pols[1])
  genjj = mK\(mS\gL[1])
  for i = 2:ind
    B[i] = genjj*B[i-1]
  end
  for jj = 2:length(pols)
    genjj = mK\(mS\gL[jj])
    el = deepcopy(genjj)
    new_deg = total_degree(pols[jj])
    for i = 2:new_deg
      for j = 1:ind
        B[(i-1)* ind + j] = B[j]* el 
      end
      mul!(el, el, genjj)
    end
    ind *= new_deg
  end

  #Now, I add the elements of the maximal order
  OB = maximal_order(base_field(S))
  for i = 1:degree(OB)
    el = MK(OB.basis_nf[i])
    for j = 1:ind
      B[(i-1)* ind + j] = B[j] * el 
    end
  end
  @vprint :Fields 2 "Product basis computed\n"
  #Now, we compute the maximal order. Then we simplify.
  #We simplify only if the degree of the field is lower than 30
  
  BasisMat = basis_matrix(B, FakeFmpqMat)
  @vtime :Fields 3 Hecke.hnf_modular_eldiv!(BasisMat.num, BasisMat.den, :lowerleft)
  NewBMat = FakeFmpqMat(BasisMat.num, BasisMat.den)
  @vtime :Fields 3 Ostart = NfAbsOrd(K, NewBMat)
  Ostart.index = divexact(NewBMat.den^degree(K), prod_diagonal(NewBMat.num))
  Ostart.gen_index = fmpq(Ostart.index)
  Ostart.disc = divexact(numerator(discriminant(K)), Ostart.index^2)
  ram_primes_rel = numerator(norm(discriminant(L)))
  ram_primes_down = Hecke.ramified_primes(OB)
  for p in ram_primes_down
    if isone(gcd(p, ram_primes_rel))
      push!(Ostart.primesofmaximality, p) 
    end
  end
  @vtime :Fields 3 O1 = MaximalOrder(Ostart)
  O1.ismaximal = 1
  Hecke._set_maximal_order_of_nf(K, O1)
  if use_simplify
    #simplify takes care of translating the order.
    @vtime :Fields 3 Ks, mKs = Hecke.simplify(K, cached = false)
  else
    Ks = K
    mKs = id_hom(K)
  end
  #I want also the embedding of the old field into the new one. 
  #It is enough to find the image of the primitive element.
  k = base_field(S)
  a = MK(gen(k)) 
  embed = hom(k, Ks, mKs\a, check = false)
  #@assert iszero(k.pol(img_a)) 
  @vprint :Fields 3 "MaximalOrder Computed. Now Automorphisms\n"
  #Now, the automorphisms.
  # I need both generators and the whole group. 
  autos = Array{NfToNfMor, 1}(undef, length(autL))
  el = mS(mK(mKs.prim_img))
  el1 = mS(mK(gen(K)))
  for i=1:length(autL)
    #@assert iszero(K.pol(mK(mS\(autL[i](el1)))))
    x = mKs\(mK\(mS\(autL[i](el))))
    #@assert Ks.pol(y) == 0
    autos[i] = hom(Ks, Ks, x, check = false)
  end
  @vprint :Fields 2 "Finished\n"
  #@assert codomain(embed) == Ks
  return Ks, autos, embed
end 

###############################################################################
#
#  From relative to absolute
#
###############################################################################

function Base.:(*)(f::NfAbsToNfAbsNS, g::NfAbsNSToNfAbsNS)
  @assert codomain(f) == domain(g)
  return hom(domain(f), codomain(g), g(f.prim_img))
end

function _relative_to_absoluteQQ(L::NfRelNS{nf_elem}, auts::Vector{NfRelNSToNfRelNSMor{nf_elem}})
  K, gK = number_field(NfAbsNS, L)
  Ks, mKs = simplified_simple_extension(K, isabelian = true)
  #Now, I have to translate the automorphisms.
  #First, to automorphisms of K.
  autsK = Vector{NfAbsNSToNfAbsNS}(undef, length(auts))
  Qxy = parent(K.pol[1])
  for i = 1:length(auts)
    embs = Vector{NfAbsNSElem}(undef, ngens(K))
    imgs = auts[i].emb
    for j = 1:length(imgs)
      embs[j] = K(map_coeffs(FlintQQ, imgs[j].data, parent = Qxy))
    end
    autsK[i] = hom(K, K, embs, check = false)
  end
  #Final step: translate the automorphisms to Ks
  _compute_preimage(mKs)
  autsKs = Vector{NfToNfMor}(undef, length(autsK))
  for i = 1:length(autsK)
    autsKs[i] = hom(Ks, Ks, mKs\((mKs*autsK[i]).prim_img), check = false)
  end
  return Ks, autsKs
end

function _relative_to_absolute(L::NfRelNS{nf_elem}, auts::Vector{NfRelNSToNfRelNSMor{nf_elem}})
  Ls, mLs = simplified_simple_extension(L)
  Ks, mKs, mks = simplified_absolute_field(Ls)
  KstoL = mKs*mLs
  _compute_preimage(KstoL)
  #Now, I have to translate the automorphisms.
  #First, to automorphisms of K.
  autsKs = Vector{NfToNfMor}(undef, length(auts))
  imggen = KstoL(gen(Ks))
  for i = 1:length(auts)
    autsKs[i] = hom(Ks, Ks, KstoL\(auts[i](imggen)))
  end
  return Ks, autsKs
end

function Base.:(*)(f::Hecke.NfRelToNfRelNSMor, g::Hecke.NfRelNSToNfRelNSMor)
  return hom(domain(f), codomain(g), g(f(gen(domain(f)))))
end


function Base.:(*)(f::Hecke.NfToNfRel, g::Hecke.NfRelToNfRelNSMor)
  @assert codomain(f) === domain(g)
  return hom(domain(f), codomain(g), g(f(gen(domain(f)))))
end

function hom(K::AnticNumberField, L::NfRelNS{nf_elem}, img_gen::NfRelNSElem{nf_elem})
  return Hecke.NfToNfRelNSMor(K, L, img_gen)
end

function image(f::Hecke.NfToNfRelNSMor, a::nf_elem)
  K = parent(a)
  Qx = parent(K.pol)
  return evaluate(Qx(a), f.img_gen)
end

function preimage(phi::Hecke.NfToNfRelNSMor, a::NfRelNSElem{nf_elem})
  @assert isdefined(phi, :preimg_base_field) && isdefined(phi, :preimgs)
  f = data(a)
  K = codomain(phi)
  k = base_field(K)
  R = parent(k.pol)
  g = map_coeffs(x -> evaluate(R(x), phi.preimg_base_field), f)
  return evaluate(g, phi.preimgs)
end


function _compute_preimage(f::NfToNfRelNSMor)
  K = domain(f)
  L = codomain(f)
  el = one(L)
  M = zero_matrix(FlintQQ, degree(K), degree(K))
  M[1, 1] = 1
  a = f.img_gen
  for i = 2:degree(K)
    el *= a
    v = absolute_coordinates(el)
    for j = 1:degree(K)
      M[i, j] = v[j]
    end
  end
  N = zero_matrix(FlintQQ, ngens(L)+1, degree(K))
  gk = L(gen(base_field(L)))
  v = absolute_coordinates(gk)
  for j = 1:degree(K)
    N[1, j] = v[j]
  end
  gL = gens(L)
  for i = 1:length(gL)
    v = absolute_coordinates(gL[i])
    for j = 1:degree(K)
      N[i+1, j] = v[j]
    end
  end
  fl, x = can_solve(M, N, side = :left)
  x1, den = _fmpq_mat_to_fmpz_mat_den(x)
  f.preimg_base_field = Nemo.elem_from_mat_row(K, x1, 1, den)
  f.preimgs = Vector{nf_elem}(undef, length(gL))
  for i = 1:length(gL)
    f.preimgs[i] = Nemo.elem_from_mat_row(K, x1, i+1, den)
  end
  return nothing
end