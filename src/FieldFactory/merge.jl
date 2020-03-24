###############################################################################
#
#  Direct product decomposition
#
###############################################################################

function direct_product_decomposition(G::GAP.GapObj, ab::Tuple{Int, Int})

  decompositions = Tuple{GAP.GapObj, GAP.GapObj}[]
  if GAP.Globals.IsAbelian(G)
    return ab, (1, 1), 1, 1
  end
  n = ab[1]
  subs = GAP.Globals.NormalSubgroups(G)
  #First, I collect all the possible decompositions
  decompositions = Tuple{GAP.GapObj, GAP.GapObj}[]
  for i = 1:length(subs)
    g1 = subs[i]
    if isone(GAP.Globals.Size(g1))
      continue
    end
    o1 = GAP.Globals.Size(g1)
    for j = 1:length(subs)
      g2 = subs[j]
      if isone(GAP.Globals.Size(g2))
        continue
      end
      o2 = GAP.Globals.Size(g2)
      if o1*o2 != n
        continue
      end
      if isone(GAP.Globals.Size(GAP.Globals.Intersection(g1, g2)))
        push!(decompositions, (g1, g2))
      end
    end
  end
  if isempty(decompositions)
    return ab, (1, 1) , 1, 1
  end
  
  #We pass to the list with the group ID
  grp_id_list = Vector{Tuple{Tuple{Int, Int}, Tuple{Int, Int}}}(undef, length(decompositions))
  for i = 1:length(grp_id_list)
    grp_id_list[i] = (GAP.gap_to_julia(Tuple{Int, Int}, GAP.Globals.IdGroup(decompositions[i][1])), GAP.gap_to_julia(Tuple{Int, Int}, GAP.Globals.IdGroup(decompositions[i][2])))  
  end

  res1 = grp_id_list[1][1]
  res2 = grp_id_list[1][2]
  if length(grp_id_list) == 1
    return res1, res2, 1, 1
  end
  #I count the redundancy, i.e. the number of possible decompositions of the same type.
  red = 1
  for i = 2:length(grp_id_list)
    l1 = grp_id_list[i][1]
    l2 = grp_id_list[i][2]
    if min(l1[1], l2[1]) > min(res1[1], res2[1])
      red = 1
      res1 = l1
      res2 = l2
    else
      if l1 == res1 && l2 == res2
        red += 1 
      end
    end
  end
  #Finally, I count the numer of times a single subgroup appears in the lists.
  redfirst = 1
  ind = 1
  for i = 1:length(decompositions)
    if grp_id_list[i] == (res1, res2)
      ind = i
      break
    end
  end
  for i = ind+1:length(decompositions)
    if decompositions[i][1] == decompositions[ind][1]
      redfirst += 1
    end
  end
  return res1, res2, red, redfirst

end

###############################################################################
#
#  Merging fields
#
###############################################################################

function _to_composite(x::FieldsTower, y::FieldsTower, abs_disc::fmpz)

  Kns, mx, my = NumberField(x.field, y.field, cached = false, check = false)
  K, mK = simple_extension(Kns, check = false)

  #First, compute the maximal order
  O1 = maximal_order(x.field)
  B1 = basis(O1, copy = false)
  O2 = maximal_order(y.field)
  B2 = basis(O2, copy = false)
  imagesx = Array{nf_elem, 1}(undef, length(B1))
  imagesy = Array{nf_elem, 1}(undef, length(B2))
  for i = 1:degree(x.field)
    imagesx[i] = mK\(mx(B1[i].elem_in_nf))
  end
  for i = 1:degree(y.field)
    imagesy[i] = mK\(my(B2[i].elem_in_nf))
  end
  prod_bas = Hecke.product_basis(imagesx, imagesy)
  fac = factor(gcd(discriminant(O1), discriminant(O2)))
  lp = collect(keys(fac.fac))
  MatOrd = basis_matrix(prod_bas, FakeFmpqMat)
  discr = fmpz(1)
  if istotally_real(x.field) && istotally_real(y.field)
    discr = abs(discriminant(O1)^degree(O2) * discriminant(O2)^degree(O1))
  else
    discr = (-1)^divexact(degree(K), 2) * abs(discriminant(O1)^degree(O2) * discriminant(O2)^degree(O1))
  end 
  inde = root(divexact(numerator(discriminant(K)), discr), 2)
  MatOrdNum = MatOrd.num
  Hecke.hnf_modular_eldiv!(MatOrdNum, MatOrd.den, :lowerleft)
  OK = NfOrd(K, FakeFmpqMat(MatOrdNum, MatOrd.den))
  #Careful: we need to compute also the sign of the discriminant!
  OK.disc = discr
  OK.index = inde  
  OK.gen_index = fmpq(OK.index)
  if !isempty(lp)
    OK = Hecke.pmaximal_overorder_at(OK, lp)
  end
  OK.ismaximal = 1
  Hecke._set_maximal_order_of_nf(K, OK)
  if abs(discriminant(OK)) > abs_disc
    return false, x
  end

  # Now, I have to translate the automorphisms.
  # Easy thing: first, I write the automorphisms of the non simple extension
  # Then translating them is straightforward.
  autK = Array{NfToNfMor, 1}(undef, length(x.generators_of_automorphisms)+ length(y.generators_of_automorphisms))
  el = mK.prim_img
  for i = 1:length(x.generators_of_automorphisms)
    ima = mx(x.generators_of_automorphisms[i].prim_img)
    autns = Hecke.NfAbsNSToNfAbsNS(Kns, Kns, NfAbsNSElem[ima, gens(Kns)[2]])
    ima = mK\(autns(el))
    autK[i] = NfToNfMor(K, K, ima)
  end
  for j = 1:length(y.generators_of_automorphisms)
    ima = my(y.generators_of_automorphisms[j].prim_img)
    autns = Hecke.NfAbsNSToNfAbsNS(Kns, Kns, NfAbsNSElem[gens(Kns)[1], ima])
    ima = mK\(autns(el))
    autK[j+length(x.generators_of_automorphisms)] = NfToNfMor(K, K, ima)
  end
  
  #Last thing: I have to add the maps of the subfields!
  emb1 = NfToNfMor(x.field, K, mK\(mx.prim_img))
  emb2 = NfToNfMor(y.field, K, mK\(my.prim_img))
  l1 = append!(NfToNfMor[emb1, emb2], x.subfields)
  embs = append!(l1, y.subfields)
  return true, FieldsTower(K, autK, embs)
  
end

function simplify!(x::FieldsTower)
  K = x.field
  OK = maximal_order(K)
  Ks, mKs = simplify(K, cached = false)
  #I need to translate everything...
  mKi = inv(mKs)
  #First, translate the lll of the maximal order
  if isdefined(OK, :lllO)
    OKs = NfOrd(nf_elem[mKi(y) for y in basis(OK.lllO, K)])
    OKs.lllO = OKs
  else
    OKs = lll(NfOrd(nf_elem[mKi(y) for y in basis(OK, K)])) 
  end
  OKs.ismaximal = 1
  OKs.disc = OK.disc
  OKs.index = root(divexact(numerator(discriminant(Ks.pol)), OKs.disc), 2)
  Hecke._set_maximal_order(Ks, OKs)
  gens_autos = NfToNfMor[hom(Ks, Ks, mKi(el(mKs.prim_img)), check = true) for el in x.generators_of_automorphisms]
  for i = 1:length(x.subfields)
    if codomain(x.subfields[i]) == K
      x.subfields[i] = x.subfields[i]*mKi
    end
  end
  x.field = Ks
  x.generators_of_automorphisms = gens_autos
  return nothing
end

#merge function when all the fields are automatically linearly disjoint
function _easy_merge(list1, list2, absolute_bound::fmpz, simpl::Bool = false)

  res = FieldsTower[]
  @vprint :Fields 1 "Number of candidates = $(length(list1)*length(list2)) \n"
  ind = 0
  for x in list1
    ind += 1
    @vprint :Fields 1 "Doing field $(ind)/$(length(list1))"
    for y in list2
      check_bound_disc(x, y, absolute_bound) || continue
      fl, composite = _to_composite(x, y, absolute_bound)
      if fl
        if simpl
          simplify!(composite)
        end
        push!(res, composite)
      end
    end
    @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())"
  end
  return res
  
end

function _disjoint_ab_subs(list1::Vector{FieldsTower}, list2::Vector{FieldsTower})
  
  deg_ab_sub1 = 1
  deg_ab_sub2 = 1
  for i = 1:length(list1[1].subfields)
    if degree(domain(list1[1].subfields[i])) == 1
      deg_ab_sub1 *= degree(codomain(list1[1].subfields[i]))
    end
  end
  for i = 1:length(list2[1].subfields)
    if degree(domain(list2[1].subfields[i])) == 1
      deg_ab_sub2 *= degree(codomain(list2[1].subfields[i]))
    end
  end  
  return deg_ab_sub1, deg_ab_sub2, gcd(deg_ab_sub1, deg_ab_sub2) == 1
  
end

function check_bound_disc(K::FieldsTower, L::FieldsTower, bound::fmpz)
  #First, I check the bound for the fields
  if !new_check_disc(K, L, bound)
    @hassert :Fields 1 !_to_composite(K, L, bound)[1]
    return false
  end
  #In the other cases, before returning true, I try to check if the
  #maximal abelian subextension is admissible
  Kab = maximal_abelian_subextension(K)
  Lab = maximal_abelian_subextension(L)
  disc_comp = abs(discriminant(maximal_order(Kab[1])))
  deg = degree(Kab[1])
  for i = 2:length(Kab)
    disc_new = abs(discriminant(maximal_order(Kab[i])))
    d = gcd(disc_new, disc_comp)
    if issquare(d)
      d = root(d, 2)
    end
    n = ppio(disc_comp, d)[2]^(degree(Kab[i]))*ppio(disc_new, d)[2]^deg
    ld = factor(d)
    for (q, v) in ld
      vnum = degree(Kab[i])*valuation(disc_comp, q) + deg*valuation(disc_new, q)
      vden = 2*(deg*degree(Kab[i])-1)*valuation(d, q)
      vfirst = vnum - vden
      v1 = degree(Kab[i])*valuation(disc_comp, q)
      v2 = deg*valuation(disc_new, q)
      vsecond = max(v1, v2)
      vd = max(vfirst, vsecond)
      n *= q^vd
    end
    disc_comp = n
    deg *= degree(Kab[i])
  end
  for i = 1:length(Lab)
    disc_new = abs(discriminant(maximal_order(Lab[i])))
    d = gcd(disc_new, disc_comp)
    if issquare(d)
      d = root(d, 2)
    end
    n = ppio(disc_comp, d)[2]^(degree(Lab[i]))*ppio(disc_new, d)[2]^deg
    ld = factor(d)
    for (q, v) in ld
      vnum = degree(Lab[i])*valuation(disc_comp, q) + deg*valuation(disc_new, q)
      vden = 2*(deg*degree(Lab[i])-1)*valuation(d, q)
      vfirst = vnum - vden
      v1 = degree(Lab[i])*valuation(disc_comp, q)
      v2 = deg*valuation(disc_new, q)
      vv = max(v1, v2)
      vd = max(vfirst, vv)
      n *= q^vd
    end
    disc_comp = n
    deg *= degree(Lab[i])
  end
  bound_max_ab_subext = root(bound, divexact(degree(K.field)*degree(L.field), deg))
  if disc_comp <= bound_max_ab_subext
    return true
  else
    @hassert :Fields 1 !_to_composite(K, L, bound)[1]
    return false
  end
end

function new_check_disc(K::FieldsTower, L::FieldsTower, absolute_bound::fmpz)
  Kf = K.field
  OKf = maximal_order(Kf)
  Lf = L.field
  OLf = maximal_order(Lf)
  d1 = discriminant(maximal_order(Kf))
  d2 = discriminant(maximal_order(Lf))
  g1 = gcd(d1, d2)
  wild, g = ppio(g1, fmpz(degree(Kf)*degree(Lf)))
  disc1 = abs(ppio(d1, g1)[2])^degree(Lf)
  disc2 = abs(ppio(d2, g1)[2])^degree(Kf)
  disc = disc1*disc2
  if disc > absolute_bound
    return false
  end
  lf = factor(g)
  ramification_indices = Vector{Tuple{fmpz, Int}}(undef, length(lf))
  ind = 1
  for (p, v) in lf
    pd1 = prime_decomposition_type(OKf, Int(p))
    pd2 = prime_decomposition_type(OLf, Int(p))
    ramification_indices[ind] = (p, lcm(pd1[1][2], pd2[1][2]))
    ind += 1
  end

  for i = 1:length(ramification_indices)
    expo = (ramification_indices[i][2] - 1)*divexact(degree(Kf)*degree(Lf), ramification_indices[i][2])
    disc *= ramification_indices[i][1]^expo
  end
  if disc > absolute_bound
    return false
  end
  lwild = factor(wild)
  for (q, v) in lwild
    v1 = valuation(d1, q)
    v2 = valuation(d2, q)
    valnum = degree(Lf)*v1 + degree(Kf)*v2  
    valden = valuation(g1, q)
    if iseven(valden)
      valden = divexact(valden, 2)
    end
    valden *= (2*degree(Lf)*degree(Kf) -2)
    if valnum - valden > max(degree(Lf)*v1, degree(Kf)*v2)
      disc *= q^(valnum-valden)
    else
      disc *= q^max(degree(Lf)*v1, degree(Kf)*v2)
    end
  end
  return disc <= absolute_bound
end

function maximal_abelian_subextension(F::FieldsTower)
  fields = AnticNumberField[]
  for x in F.subfields
    if degree(domain(x)) == 1
      push!(fields, codomain(x))
    end
  end
  return fields
end


function check_norm_group_and_disc(lfieldsK::Array{AnticNumberField, 1}, lfieldsL::Array{AnticNumberField, 1}, bound::fmpz)

  target_deg = prod(degree(x) for x in lfieldsK) * prod(degree(x) for x in lfieldsL)
  discK = lcm([discriminant(maximal_order(x)) for x in lfieldsK])
  discL = lcm([discriminant(maximal_order(x)) for x in lfieldsL])
  modulo = Int(lcm(discK, discL))
  y = PolynomialRing(QQ, "y", cached = false)[2]
  K = NumberField(y-1, cached = false)[1]
  O = maximal_order(K)
  n_quo1 = lcm(Int[degree(x) for x in lfieldsK])
  n_quo2 = lcm(Int[degree(x) for x in lfieldsL])
  r, mr = Hecke.ray_class_groupQQ(O, modulo, true, lcm(n_quo1, n_quo2))
  Kt = PolynomialRing(K, "t", cached = false)[1]
  h = change_base_ring(K, lfieldsK[1].pol, parent = Kt)
  S, mS = norm_group(h, mr, cached = false)
  for i = 2:length(lfieldsK)
    h = map_coeffs(K, lfieldsK[i].pol, parent = Kt)
    s, ms = norm_group(h, mr, cached = false)
    S, mS = intersect(ms, mS)
  end
  for i = 1:length(lfieldsL)
    h = map_coeffs(K, lfieldsL[i].pol, parent = Kt)
    s, ms = norm_group(h, mr, cached = false)
    S, mS = intersect(ms, mS)
  end
  Q, mQ = cokernel(mS, false)
  if order(Q) != target_deg
    return false
  else
    C = ray_class_field(mr, mQ)
    return Hecke.discriminant_conductorQQ(O, C, modulo, bound, Int(order(Q)))
  end

end

function _first_sieve(list1::Vector{FieldsTower}, list2::Vector{FieldsTower}, absolute_bound::fmpz, redfirst::Int)
  ab1, ab2, fl = _disjoint_ab_subs(list1, list2)
  bound_max_ab_sub = root(absolute_bound, divexact(degree(list1[1])*degree(list2[1]), ab1*ab2))
  D = Dict{Tuple{Set{fmpz}, Set{fmpz}, Bool}, Array{Tuple{Int, Int}, 1}}() #The boolean true means real
  for i1 = 1:length(list1)
    @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())Combinations with field $(i1)/$(length(list1)) of the first list"
    @vprint :FieldsNonFancy 1 "Fields $(i1)/$(length(list1))\n"
    K = list1[i1]
    DK = Dict{Tuple{Set{fmpz}, Set{fmpz}}, Array{Int, 1}}()
    rK = ramified_primes(K)
    lfieldsK = maximal_abelian_subextension(K)
    rK1 = Set(fmpz[])
    for x in lfieldsK
      rK1 = union(rK1, Hecke.ramified_primes(maximal_order(x)))
    end
    #First, I only check for disjointness
    for i2 = 1:length(list2)
      L = list2[i2]
      check_bound_disc(K, L, absolute_bound) || continue
      #First, I check if the discriminants are coprime
      rL = Hecke.ramified_primes(L)
      lfieldsL = maximal_abelian_subextension(L)
      rL1 = Set(fmpz[])
      for x in lfieldsL
        rL1 = union(rL1, Hecke.ramified_primes(maximal_order(x)))
      end
      fl = false
      if isempty(intersect(rL1, rK1))
        fl = true
      elseif length(lfieldsL) == 1 && length(lfieldsK) == 1
        if degree(lfieldsL[1]) == 2 && degree(lfieldsK[1]) == 2 && discriminant(maximal_order(lfieldsK[1])) != discriminant(maximal_order(lfieldsL[1]))
          fl = true
        elseif Hecke.islinearly_disjoint(lfieldsK[1], lfieldsL[1])
          fl = true
        end
      elseif check_norm_group_and_disc(lfieldsK, lfieldsL, bound_max_ab_sub)
        fl = true
      end
      if fl
        k =  Set(vcat(rK, rL))
        k1 = union(rK1, rL1)
        if haskey(DK, (k, k1))
          push!(DK[(k, k1)],  i2)
        else
          DK[(k, k1)] = Int[i2]
        end
      end
    end
    #Now, I sieve also by infinite places.
    for (k, v) in DK
      if length(v) < redfirst
        continue
      end
      if !istotally_real(K.field)
        ar = Array{Tuple{Int, Int}, 1}(undef, length(v))
        for j = 1:length(v)
          ar[j] = (i1, v[j])
        end
        if haskey(D, (k[1], k[2], false))
          append!(ar, D[(k[1], k[2], false)])  
        end
        D[(k[1], k[2], false)] = ar
      else
        ar_real = Array{Tuple{Int, Int}, 1}()
        ar_not_real = Array{Tuple{Int, Int}, 1}()
        for j = 1:length(v)
          if istotally_real(list2[v[j]].field)
            push!(ar_real, (i1, v[j]))
          else
            push!(ar_not_real, (i1, v[j]))
          end
        end
        if !isempty(ar_real)
          if haskey(D, (k[1], k[2], true))
            append!(ar_real, D[(k[1], k[2], true)])  
          end
          D[(k[1], k[2], true)] = ar_real
        end
        if !isempty(ar_not_real)
          if haskey(D, (k[1], k[2], false))
            append!(ar_not_real, D[(k[1], k[2], false)])  
          end
          D[(k[1], k[2], false)] = ar_not_real
        end
      end
    end
  end
  return D
end

function _some_combinatorics(l::Vector{Tuple{Int, Int}}, red1, red2)
  #every entry must appear multiples of red1 or red2 times.
  while true
    entries1 = Dict{Int, Int}()
    entries2 = Dict{Int, Int}()
    for i = 1:length(l)
      if !haskey(entries1, l[i][1])
        entries1[l[i][1]] = 1
      else
        entries1[l[i][1]] += 1
      end
      if !haskey(entries2, l[i][2])
        entries2[l[i][2]] = 1
      else
        entries2[l[i][2]] += 1
      end
    end
    done = false
    for (k, v) in entries1
      if red1 <= v
        continue
      end
      done = true
      #remove all the tuples
      filter!(x -> x[1] != k, l)
    end
    for (k, v) in entries2
      if red1 > v
        done = true
        filter!(x -> x[2] != k, l)
      end
    end
    if !done
      break
    end
  end
  return l
end

function sieve_by_discriminant(list1, list2, v)

  d1 = degree(list1[1].field)
  d2 = degree(list2[1].field)
  D = Dict{fmpz, Vector{Int}}()
  
  for i = 1:length(v)
    candidate = abs(discriminant(maximal_order(list1[v[i][1]].field))^d2)*abs(discriminant(maximal_order(list2[v[i][2]].field))^d1)
    found = false
    for (d, l) in D
      if _differ_by_square(d, candidate)
        push!(l, i)
        found = true
        break
      end
    end 
    if !found
      D[candidate] = Int[i]
    end
  end
  res = Vector{Vector{Tuple{Int, Int}}}()
  for val in values(D)
    to_push = Vector{Tuple{Int, Int}}(undef, length(val))
    for i = 1:length(val)
      to_push[i] = v[val[i]]
    end
    push!(res, to_push)
  end
  return res
end

function _differ_by_square(n::fmpz, m::fmpz)
  return issquare(divexact(fmpq(n), fmpq(m)))
end

function sieve_by_norm_group(list1::Vector{FieldsTower}, list2::Vector{FieldsTower}, v::Vector{Tuple{Int, Int}}, ramified_primes::Vector{Int})

  target_deg = prod(degree(x) for x in maximal_abelian_subextension(list1[1])) * prod(degree(x) for x in maximal_abelian_subextension(list2[1]))
  expo = lcm(vcat([degree(x) for x in maximal_abelian_subextension(list1[1])], [degree(x) for x in maximal_abelian_subextension(list2[1])]))
  modulo = 1
  for p in ramified_primes
    if !divisible(expo, p)
      modulo *= p
    else
      bound_disc = valuation_bound_discriminant(ppio(expo, p)[1], p)
      bound_exp = div(bound_disc, (p-1)*p^(valuation(expo, p)-1))
      modulo *= p^bound_exp
    end
  end
  K = rationals_as_number_field()[1]
  O = maximal_order(K)
  r, mr = Hecke.ray_class_groupQQ(O, modulo, true, expo)
  Kt = PolynomialRing(K, "t", cached = false)[1]
  norm_groups = Vector{GrpAbFinGen}(undef, length(v))
  for i = 1:length(v)
    lfieldsK = maximal_abelian_subextension(list1[v[i][1]])
    lfieldsL = maximal_abelian_subextension(list2[v[i][2]])
    h = change_base_ring(K, lfieldsK[1].pol, parent = Kt)
    S = norm_group(h, mr)[1]
    for i = 2:length(lfieldsK)
      h = change_base_ring(K, lfieldsK[i].pol, parent = Kt)
      s = norm_group(h, mr)[1]
      S = intersect(s, S)
    end
    for i = 1:length(lfieldsL)
      h = change_base_ring(K, lfieldsL[i].pol, parent = Kt)
      s = norm_group(h, mr)[1]
      S = intersect(s, S)
    end
    norm_groups[i] = S
  end
  #Now that I have the norm groups, I need to compare them.
  done = falses(length(v))
  res = Vector{Vector{Tuple{Int, Int}}}()
  for i = 1:length(v)
    if done[i]
      continue
    end
    done[i] = true
    S = norm_groups[i]
    new_v = Vector{Tuple{Int, Int}}()
    push!(new_v, v[i])
    for j = i+1:length(v)
      if done[j]
        continue
      end
      if iseq(S, norm_groups[j])
        done[j] = true
        push!(new_v, v[j])
      end
    end
    push!(res, new_v)
  end
  return res
end

function refine_clusters(list1, list2, clusters, red, redfirst, redsecond)
  new_clusters = Vector{Vector{Tuple{Int, Int}}}()
  for i = 1:length(clusters)
    v1 = _some_combinatorics(clusters[i], redfirst, redsecond)
    if length(v1) < red
      continue
    end
    if length(v1) == red
      push!(new_clusters, v1)
      continue
    end
    mK = maximal_abelian_subextension(list1[v1[1][1]])
    mL = maximal_abelian_subextension(list2[v1[1][2]])
    ram_primes = Int[]
    for s = 1:length(mK)
      ram_primes = map(Int, collect(unique(vcat(ram_primes, ramified_primes(maximal_order(mK[s]))))))
    end
    for s = 1:length(mL)
      ram_primes = map(Int, collect(unique(vcat(ram_primes, ramified_primes(maximal_order(mL[s]))))))
    end
    lv = sieve_by_norm_group(list1, list2, v1, ram_primes)
    for s = 1:length(lv)
      vnew = _some_combinatorics(lv[s], redfirst, redsecond)
      if length(vnew) >= red
        push!(new_clusters, vnew)
      end
    end
  end
  return new_clusters
end


function _merge(list1::Vector{FieldsTower}, list2::Vector{FieldsTower}, absolute_bound::fmpz, red::Int, redsecond::Int, simpl::Bool = false)

  if red == 1
    #All the fields are automatically linearly disjoint
    @vprint :Fields 1 "All the fields are linearly disjoint, easy case \n"
    @vprint :FieldsNonFancy 1 "All the fields are linearly disjoint, easy case \n"
    return _easy_merge(list1, list2, absolute_bound, simpl)
  end

  redfirst = divexact(red, redsecond)
  #Bad case: a mess.
  #I check that the maximal abelian subextensions are linearly disjoint.
  #Working with polynomials may be more expensive.
  #Since I am working with abelian extensions, I can compute the norm groups and see there if the norm groups are correct.
  @vprint :Fields 1 "Merging fields\n"
  @vprint :Fields 1 "Number of fields: $(length(list1)*length(list2))\n"
  @vprint :FieldsNonFancy 1 "Merging fields\n"
  @vprint :FieldsNonFancy 1 "Number of fields: $(length(list1)*length(list2))\n"
  @vprint :Fields 1 "Redundancy: $(red), $(redfirst), $(redsecond)\n"
  @vprint :FieldsNonFancy 1 "Redundancy: $(red), $(redfirst), $(div(red, redfirst))\n"

  res = FieldsTower[]
  D1 = _first_sieve(list1, list2, absolute_bound, redfirst)
  if isempty(D1)
    return res
  end
  clusters = Vector{Tuple{Int, Int}}[x for x in values(D1)]
  @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())Candidates after first sieve: $(sum(length(x) for x in clusters))\n"
  
  @vprint :Fields 1 "Sieving by discriminant\n"
  #Now, I sieve by discriminant
  clusters1 = Vector{Vector{Tuple{Int, Int}}}()
  for v in clusters
    append!(clusters1, sieve_by_discriminant(list1, list2, v))
  end
  @vprint :Fields 1 "Candidates: $(sum(length(x) for x in clusters1))\n"
  
  @vprint :Fields 1 "Sieving by maximal abelian subextension\n"
  new_clusters = refine_clusters(list1, list2, clusters1, red, redfirst, redsecond)
  if isempty(new_clusters)
    return res
  end
  @vprint :Fields 1 "Candidates: $(sum(length(x) for x in new_clusters))\n"
  @vprint :Fields 1 "Sieving by prime_splitting\n"
  fields_to_be_computed = _sieve_by_prime_splitting(list1, list2, new_clusters, red, redfirst, redsecond)

  @vprint :Fields 1 "Computing maximal order of $(length(fields_to_be_computed)) fields\n"
  for i = 1:length(fields_to_be_computed)
    @vprint :Fields 1 "Doing $(i) / $(length(fields_to_be_computed))"
    pair = fields_to_be_computed[i]
    fl, candidate = _to_composite(list1[pair[1]], list2[pair[2]], absolute_bound)
    if fl
      if simpl
        simplify!(candidate)
      end
      push!(res, candidate)
    end
    @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())"
  end
  @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())Fields found: $(length(res))\n"
  @vprint :FieldsNonFancy 1 "Fields found: $(length(res))\n"
  return res
end

function _sieve_by_prime_splitting(list1, list2, clusters, red, redfirst, redsecond)
  fields_to_be_computed = Vector{Tuple{Int, Int}}()
  d1 = degree(list1[1].field)
  d2 = degree(list2[1].field)
  total = length(clusters)
  @vprint :Fields 1 "\n Number of clusters: $(total)\n"
  nclu = 0
  for v in clusters
    nclu += 1
    if length(v) == red
      push!(fields_to_be_computed, v[1])
      continue
    end
    if length(v) < red
      continue
    end
    @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol()) Doing cluster $(nclu)/$(total) of length $(length(v))"
    p = next_prime(1000)
    iso_classes = Vector{Int}[Int[i for i = 1:length(v)]]
    while true
      splitting_types = Dict{Tuple{Int, Int}, Vector{Int}}()
      for i = 1:length(v)
        pd1 = prime_decomposition_type(maximal_order(list1[v[i][1]].field), p)
        if pd1[1][2] != 1
          break
        end
        f1 = pd1[1][1]
        pd2 = prime_decomposition_type(maximal_order(list2[v[i][2]].field), p)
        if pd2[1][2] != 1
          break
        end
        f2 = pd2[1][1]
        f = lcm(f1, f2)
        r = divexact(d1*d2, f)
        if haskey(splitting_types, (r, f))
          push!(splitting_types[(r, f)], i)
        else
          splitting_types[(r, f)] = Int[i]
        end
      end
      if all(x -> length(x) <= red, values(splitting_types))
        #I intersect the data with the one that I already have
        for vals in values(splitting_types)
          to_be = intersect_infos(vals, iso_classes)
          for j in to_be
            if length(j) == red
              push!(fields_to_be_computed, v[j[1]])
            end
          end
        end
        break
      else
        #I save the information provided by the splitting
        new_iso_classes = Vector{Int}[]
        for vals in values(splitting_types)
          append!(new_iso_classes, intersect_infos(vals, iso_classes))
        end
        iso_classes = new_iso_classes
        if all(x -> length(x) <= red, iso_classes)
          for j in iso_classes
            if length(j) == red
              push!(fields_to_be_computed, v[j[1]])
            end
          end
          break
        else
          p = next_prime(p)
        end
      end
    end 
  end
  @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())"
  return fields_to_be_computed
end

function intersect_infos(v::Vector{Int}, iso_classes::Vector{Vector{Int}})
  res = Vector{Vector{Int}}()
  for w in iso_classes
    r = collect(intersect(v, w))
    if !isempty(r)
      push!(res, r)
    end
  end
  return res
end
