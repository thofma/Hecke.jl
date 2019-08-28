

add_verbose_scope(:Fields)
add_assert_scope(:Fields)

add_verbose_scope(:FieldsNonFancy)

mutable struct FieldsTower
  field::AnticNumberField
  generators_of_automorphisms::Vector{NfToNfMor}
  subfields::Vector{NfToNfMor}
  ramified_primes::Vector{fmpz}
  
  #Solvable embedding problems for the extension
  #They are here to improve the conductor computation
  imgs_autos::Vector{Main.ForeignGAP.MPtr}
  auts_for_conductors::Vector{Main.ForeignGAP.MPtr}
  proj_ext::Main.ForeignGAP.MPtr
  
  function FieldsTower(K::AnticNumberField, auts::Vector{NfToNfMor}, subfields::Vector{NfToNfMor})
    z = new()
    z.field = K
    z.generators_of_automorphisms = auts
    z.subfields = subfields
    return z
  end

end

include("./brauer.jl")
include("./merge.jl")
include("./abelian_layer.jl")
include("./read_write.jl")

Generic.degree(F::FieldsTower) = degree(F.field)
Hecke.maximal_order(F::FieldsTower) = maximal_order(F.field)

function ramified_primes(F::FieldsTower)
  if !isdefined(F, :ramified_primes)
    f = factor(discriminant(maximal_order(F.field)))
    F.ramified_primes = collect(keys(f.fac))
  end
  return F.ramified_primes
end

###############################################################################
#
#  From automorphisms to permutation groups
#
###############################################################################

function perm_grp(G::Vector{Hecke.NfRel_nsToNfRel_nsMor{nf_elem}})
  
  n = length(G)
  G1 = closure(G, *)
  Dc = Vector{Tuple{Hecke.NfRel_nsToNfRel_nsMor, Int}}(undef, length(G1))
  for i = 1:length(G1)
    Dc[i] = (G1[i], i)
  end
  D = Dict{Hecke.NfRel_nsToNfRel_nsMor, Int}(Dc)
  permutations = Array{Array{Int, 1},1}(undef, n)
  for s = 1:n
    perm = Array{Int, 1}(undef, length(G1))
    for i = 1:length(G1)
      a = G[s]*G1[i]
      perm[i] = D[a]
    end
    permutations[s] = perm
  end
  return _perm_to_gap_grp(permutations)
end


function perm_grp(G::Array{Hecke.NfToNfMor, 1})
  #TODO: I don't need the closure. I only need the images in the residue ring.
  K = domain(G[1])
  n = length(G)
  G1 = closure(G, degree(K))
  #First, find a good prime
  p = 11
  d = numerator(discriminant(K.pol))
  while mod(d, p) == 0
    p = next_prime(p)
  end
  R = GF(p, cached = false)
  Rx, x = PolynomialRing(R, "x", cached = false)
  fmod = Rx(K.pol)
  pols = gfp_poly[Rx(g.prim_img) for g in G]
  for g in G1
    if g in G
      continue
    end
    push!(pols, Rx(g.prim_img))
  end
  Dcreation = Vector{Tuple{gfp_poly, Int}}(undef, length(pols))
  for i = 1:length(pols)
    Dcreation[i] = (pols[i], i)
  end
  D = Dict{gfp_poly, Int}(Dcreation)
  @assert length(D) == degree(K)
  permutations = Array{Array{Int, 1},1}(undef, n)
  for s = 1:n
    perm = Array{Int, 1}(undef, length(G1))
    for i = 1:length(G1)
      perm[i] = D[Hecke.compose_mod(pols[s], pols[i], fmod)]
    end
    permutations[s] = perm
  end
  return _perm_to_gap_grp(permutations)

end

function _from_autos_to_perm(G::Array{Hecke.NfToNfMor,1})
  
  K = domain(G[1])
  @assert degree(K) == length(G)
  n = length(G)
  #First, find a good prime
  p = 2
  d = numerator(discriminant(K.pol))
  while mod(d, p) == 0
    p = next_prime(p)
  end
  R = GF(p, cached = false)
  Rx, x = PolynomialRing(R, "x", cached = false)
  fmod = Rx(K.pol)
  pols = Vector{Tuple{gfp_poly, Int}}(undef, n)
  for i = 1:n
    pols[i] = (Rx(G[i].prim_img), i)
  end
  D = Dict{gfp_poly, Int}(pols)
  permutations = Array{Array{Int, 1},1}(undef, n)
  for s = 1:n
    perm = Array{Int, 1}(undef, n)
    for i = 1:n
      perm[i] = D[Hecke.compose_mod(pols[i][1], pols[s][1], fmod)]
    end
    permutations[s] = perm
  end
  return permutations
  
end

function _perm_to_gap_grp(perm::Array{Array{Int, 1},1})
  g = Main.ForeignGAP.MPtr[]
  for x in perm
    z = _perm_to_gap_perm(x)
    push!(g, z)
  end
  A = GAP.Globals.Group(GAP.julia_to_gap(g))
  return A  
end

function _perm_to_gap_perm(x::Array{Int, 1})
  z = GAP.Globals.PermList(GAP.julia_to_gap(x))
  return z
end

function IdGroup(autos::Array{NfToNfMor, 1})
  G = _from_autos_to_perm_grp(autos)
  return GAP.Globals.IdGroup(G)
end


################################################################################
#
#  final computation of the maximal order and automorphisms
#
################################################################################

function _from_relative_to_abs_with_embedding(L::Hecke.NfRel_ns{T}, autL::Array{Hecke.NfRel_nsToNfRel_nsMor{T}, 1}) where T
  
  S, mS = simple_extension(L)
  K, mK, MK = absolute_field(S, false)
  
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
  Ostart.index = divexact(NewBMat.den^degree(K), prod(NewBMat.num[i, i] for i = 1:degree(K)))
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
  
  @vtime :Fields 3 Ks, mKs = Hecke.simplify(K)
  #Now, we have to construct the maximal order of this field.
  #I am computing the preimages of mKs by hand, by inverting the matrix.
  @vtime :Fields 3 begin
  arr_prim_img = Array{nf_elem, 1}(undef, degree(Ks))
  arr_prim_img[1] = K(1)
  arr_prim_img[2] = mKs.prim_img
  for i = 3:degree(Ks)
    arr_prim_img[i] = arr_prim_img[i-1]*mKs.prim_img
  end
  M1 = inv(basis_matrix(arr_prim_img, FakeFmpqMat))
  end
  if isdefined(O1, :lllO)
    O2 = NfAbsOrd(Ks, basis_matrix(O1.lllO, copy = false)*M1)
    O2.lllO = O2
  else
    O2 = NfAbsOrd(Ks, basis_matrix(O1, copy = false)*M1)
  end
  O2.ismaximal = 1
  @assert isdefined(O1, :disc)
  O2.disc = O1.disc
  O2.index = root(divexact(numerator(discriminant(Ks)), O2.disc), 2)
  @vtime :Fields 3 OLLL = lll(O2)
  Hecke._set_maximal_order_of_nf(Ks, OLLL)
  #I want also the embedding of the old field into the new one. 
  #It is enough to find the image of the primitive element.
  k = base_field(S)
  a = MK(gen(k)) 
  M = zero_matrix(FlintZZ, 1, degree(Ks))
  Hecke.elem_to_mat_row!(M, 1, denominator(a), a)
  mul!(M, M, M1.num)
  img_a = Hecke.elem_from_mat_row(Ks, M, 1, M1.den*denominator(a))
  embed = NfToNfMor(k, Ks, img_a)
  #@assert iszero(k.pol(img_a)) 
  @vprint :Fields 3 "MaximalOrder Computed. Now Automorphisms\n"
  #Now, the automorphisms.
  # I need both generators and the whole group. 
  autos = Array{NfToNfMor, 1}(undef, length(autL))
  el = mS(mK(mKs.prim_img))
  el1 = mS(mK(gen(K)))
  for i=1:length(autL)
    #@assert iszero(K.pol(mK(mS\(autL[i](el1)))))
    x = mK\(mS\(autL[i](el)))
    Hecke.elem_to_mat_row!(M, 1, denominator(x), x)
    mul!(M, M, M1.num)
    y = Hecke.elem_from_mat_row(Ks, M, 1, M1.den*denominator(x) )
    #@assert Ks.pol(y) == 0
    autos[i] = Hecke.NfToNfMor(Ks, Ks, y)
  end
  #And the generators are done. Now the closure
  @vtime :Fields 3 Hecke._set_automorphisms_nf(Ks, closure(autos, degree(Ks)))
  #Hecke._set_automorphisms_nf(Ks, autsKs)
  @vprint :Fields 2 "Finished\n"
    #@assert codomain(embed) == Ks
  return Ks, autos, embed
 
end 


###############################################################################
#
#  Split Extensions
#
###############################################################################

function _split_extension(G::Array{Hecke.NfToNfMor, 1}, mats::Array{Hecke.GrpAbFinGenMap, 1})
  
  gtype = map(Int, domain(mats[1]).snf)
  G1 = perm_grp(G)
  gensG1 = GAP.Globals.GeneratorsOfGroup(G1)
  A = GAP.Globals.AbelianGroup(GAP.julia_to_gap(gtype))
  gens = GAP.Globals.GeneratorsOfGroup(A)
  auts = Array{Main.ForeignGAP.MPtr, 1}(undef, length(mats))
  for i = 1:length(mats)
    images = Array{Main.ForeignGAP.MPtr, 1}(undef, length(gtype))
    for j = 1:length(gtype)
      g = GAP.Globals.Identity(A)
      for k = 1:length(gtype)
        if !iszero(mats[i].map[j,k])
          g *= gens[k]^Int(mats[i].map[j,k])
        end
      end
      images[j] = g
    end
    auts[i] = GAP.Globals.GroupHomomorphismByImages(A, A, gens, GAP.julia_to_gap(images))
  end  
  AutGrp = GAP.Globals.Group(GAP.julia_to_gap(auts))
  mp = GAP.Globals.GroupHomomorphismByImages(G1, AutGrp, gensG1, GAP.julia_to_gap(auts))
  return GAP.Globals.SplitExtension(G1, mp, A)

end

###############################################################################
#
#  Check group extension
#
###############################################################################

function check_group_extension(TargetGroup::Main.ForeignGAP.MPtr, autos::Array{NfToNfMor, 1}, res_act::Array{GrpAbFinGenMap, 1})
  
  GS = domain(res_act[1])
  expo = Int(GS.snf[end])
  K = domain(autos[1])
  d = degree(K)
  com, uncom = ppio(expo, d)
  
  if com == 1  
    # I only need to check the split extension, since the second cohomology group is
    # trivial, regardless of the action
    H = _split_extension(autos, res_act)
    return GAP.Globals.IdGroup(H) == TargetGroup
  end
  
  if uncom == 1
    #Need a cohomological check. Only useful in the prime power case.
    return true
  end
  
  # I check the split extension related to only uncom
  #Now, I have to check if the split extension is isomorphic to IdH
  Qn, mQn = quo(GS, uncom)
  S1, mS1 = snf(Qn)
  new_res_act = Array{GrpAbFinGenMap, 1}(undef, length(res_act))
  for i = 1:length(res_act)
    Mat = mS1.map*mQn.imap*res_act[i].map*mQn.map*mS1.imap
    Hecke.reduce_mod_snf!(Mat, S1.snf)
    new_res_act[i] = hom(S1, S1, Mat)
  end
  H = _split_extension(autos, new_res_act)
  return GAP.Globals.IdGroup(H) == TargetGroup
  
end


###############################################################################
#
#  Interface to find Fields
#
###############################################################################

function field_extensions(list::Vector{FieldsTower}, bound::fmpz, IsoE1::Main.ForeignGAP.MPtr, l::Array{Int, 1}, only_real::Bool)

  grp_to_be_checked = Dict{Int, Main.ForeignGAP.MPtr}()
  d = degree(list[1])
  n = lcm(l)
  com, uncom = ppio(n, d)
  fac = factor(n)
  for (p, v) in fac
    grp_to_be_checked[Int(p)] = _construct_grp(IsoE1, Int(p)^v)
  end
  if uncom != 1
    IsoCheck = _construct_grp(IsoE1, uncom)
  else
    IsoCheck = IsoE1
  end
  final_list = FieldsTower[]
  for (j, x) in enumerate(list)   
    @vprint :Fields 1 "Field $(j)/$(length(list)): $(x.field.pol)"
    @vprint :FieldsNonFancy 1 "Field $(j)/$(length(list)): $(x.field.pol)\n"
    append!(final_list, field_extensions(x, bound, IsoCheck, l, only_real, grp_to_be_checked, IsoE1))
  end 
  return final_list

end

debf = []

function field_extensions(x::FieldsTower, bound::fmpz, IsoE1::Main.ForeignGAP.MPtr, l::Array{Int, 1}, only_real::Bool, grp_to_be_checked::Dict{Int, Main.ForeignGAP.MPtr}, IsoG::Main.ForeignGAP.MPtr)
  
  list_cfields = _abelian_normal_extensions(x, l, bound, IsoE1, only_real, IsoG)
  if isempty(list_cfields)
    @vprint :Fields 1 "\e[1F$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())Number of new fields found: 0\n\n"
    @vprint :FieldsNonFancy 1 "Number of new fields found: 0\n"
    return Vector{FieldsTower}()
  end
  push!(debf, (list_cfields, x.generators_of_automorphisms, grp_to_be_checked))
  list = from_class_fields_to_fields(list_cfields, x.generators_of_automorphisms, grp_to_be_checked)
  @vprint :Fields 1 "Computing maximal orders"
  @vprint :FieldsNonFancy 1 "Computing maximal orders\n"
  final_list = Vector{FieldsTower}(undef, length(list))
  for j = 1:length(list)
    fld, autos, embed = _from_relative_to_abs_with_embedding(list[j][1], list[j][2])
    previous_fields = Array{NfToNfMor, 1}(undef, length(x.subfields)+1)
    for s = 1:length(x.subfields)
      previous_fields[s] = x.subfields[s]
    end
    previous_fields[end] = embed 
    final_list[j] = FieldsTower(fld, autos, previous_fields)
  end
  @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())"
  @vprint :Fields 1 "Number of new fields found: $(length(final_list))\n\n"
  @vprint :FieldsNonFancy 1 "Number of new fields found: $(length(final_list))\n"
  return final_list
  
end




###############################################################################
#
#  Interface
#
###############################################################################
function fields_direct_product(g1, g2, red, redfirst, absolute_bound; only_real = false)
  b1 = root(absolute_bound, g2[1])
  b2 = root(absolute_bound, g1[1])
  l2 = fields(g2[1], g2[2], b2, only_real = only_real)
  if isempty(l2)
    return FieldsTower[]
  end
  if g1 == g2
    return _merge(l2, l2, absolute_bound, red, redfirst)
  end
  l1 = fields(g1[1], g1[2], b1, only_real = only_real)
  if isempty(l1)
    return FieldsTower[]
  end
  return _merge(l1, l2, absolute_bound, red, redfirst)
end


function fields(a::Int, b::Int, absolute_bound::fmpz; using_direct_product::Bool = true, only_real::Bool = false)
  
  @assert absolute_bound > 0
  if a == 1
    @assert b == 1
    Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
    K, a = NumberField(x-1, cached = false)
    g = NfToNfMor(K, K, K(1))
    return FieldsTower[FieldsTower(K, NfToNfMor[g], Array{NfToNfMor, 1}())]
  end
  G = GAP.Globals.SmallGroup(a, b)
  @assert GAP.Globals.IsSolvable(G)
  if using_direct_product
    g1, g2, red, redfirst = direct_product_decomposition(G, (a, b))
    if g2 != (1, 1)    
      return fields_direct_product(g1, g2, red, redfirst, absolute_bound; only_real = false)
    end
  end
  @vprint :Fields 1 "Doing Group ($a, $b) with bound $absolute_bound\n"
  @vprint :FieldsNonFancy 1 "Doing Group ($a, $b) with bound $absolute_bound\n"
  L = GAP.Globals.DerivedSeries(G)
  lvl = _real_level(L)
  #First step by hand
  l = GAP.gap_to_julia(Vector{Int64}, GAP.Globals.AbelianInvariants(G))
  @vprint :Fields 1 "contructing abelian extensions with invariants $l \n" 
  @vprint :FieldsNonFancy 1 "contructing abelian extensions with invariants $l \n" 
  #@vtime :Fields 2 
  list = abelian_extensionsQQ(l, root(absolute_bound, div(a,prod(l))), (lvl > 1 || only_real))
  if isempty(list)
    return list
  end
  @vprint :Fields 1 "First step completed\n \n"
  @vprint :FieldsNonFancy 1 "First step completed\n \n"
  for i = 2:length(L)-1
    H1 = GAP.Globals.FactorGroup(L[i], L[i+1])
    E1 = GAP.Globals.FactorGroup(L[1], L[i+1])
    l = GAP.gap_to_julia(Vector{Int64}, GAP.Globals.AbelianInvariants(H1))
    @vprint :Fields 1 "contructing abelian extensions with invariants $l \n" 
    @vprint :FieldsNonFancy 1 "contructing abelian extensions with invariants $l \n" 
    o = divexact(a, GAP.Globals.Size(E1))
    bound = root(absolute_bound, o)
    IsoE1 = GAP.Globals.IdGroup(E1)
    @vprint :Fields 1 "Number of fields at the $i -th step: $(length(list)) \n"
    @vprint :FieldsNonFancy 1 "Number of fields at the $i -th step: $(length(list)) \n"
    lG = snf(DiagonalGroup(l))[1]
    invariants = map(Int, lG.snf) 
    onlyreal = (lvl > i || only_real)
    #First, I search for obstruction.
    if iscyclic(lG) 
      @vprint :Fields 1 "Computing obstructions\n"
      @vprint :FieldsNonFancy 1 "Computing obstructions\n"
      #@vtime :Fields 1 
      list = check_Brauer_obstruction(list, L, i, invariants[1])
      @vprint :Fields 1 "Fields to check: $(length(list))\n\n"
      @vprint :FieldsNonFancy 1 "Fields to check: $(length(list))\n\n"
    end
    if isempty(list)
      return FieldsTower[]
    end
    list = field_extensions(list, bound, IsoE1, invariants, onlyreal)
    @vprint :Fields 1 "Step $i completed\n"
    @vprint :FieldsNonFancy 1 "Step $i completed\n"
    if isempty(list)
      return FieldsTower[]
    end
  end
  return list
  
end

function fields(list::Vector{FieldsTower}, G, absolute_bound::fmpz; only_real::Bool = false)
  L = GAP.Globals.DerivedSeries(G)
  lvl = _real_level(L)
  #First step by hand
  for i = 2:length(L)-1
    E1 = GAP.Globals.FactorGroup(L[1], L[i+1])
    if GAP.Globals.Size(E1) != degree(list[1].field)
      continue
    end
    H1 = GAP.Globals.FactorGroup(L[i], L[i+1])
    l = GAP.gap_to_julia(Vector{Int64}, GAP.Globals.AbelianInvariants(H1))
    @vprint :Fields 1 "contructing abelian extensions with invariants $l \n" 
    @vprint :FieldsNonFancy 1 "contructing abelian extensions with invariants $l \n" 
    o = divexact(GAP.Globals.Size(G), GAP.Globals.Size(E1))
    bound = root(absolute_bound, o)
    IsoE1 = GAP.Globals.IdGroup(E1)
    @vprint :Fields 1 "Number of fields at the $i -th step: $(length(list)) \n"
    @vprint :FieldsNonFancy 1 "Number of fields at the $i -th step: $(length(list)) \n"
    lG = snf(DiagonalGroup(l))[1]
    invariants = map(Int, lG.snf) 
    onlyreal = (lvl > i || only_real)
    #First, I search for obstruction.
    if iscyclic(lG) 
      @vprint :Fields 1 "Computing obstructions\n"
      @vprint :FieldsNonFancy 1 "Computing obstructions\n"
      #@vtime :Fields 1 
      list = check_Brauer_obstruction(list, L, i, invariants[1])
      @vprint :Fields 1 "Fields to check: $(length(list))\n\n"
      @vprint :FieldsNonFancy 1 "Fields to check: $(length(list))\n\n"
    end
    if isempty(list)
      return FieldsTower[]
    end
    list = field_extensions(list, bound, IsoE1, invariants, onlyreal)
    @vprint :Fields 1 "Step $i completed\n"
    @vprint :FieldsNonFancy 1 "Step $i completed\n"
    if isempty(list)
      return FieldsTower[]
    end
  end
  return list
end
