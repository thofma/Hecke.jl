using Random


###############################################################################
#
#  Direct product decomposition
#
###############################################################################

function direct_product_decomposition(G::Main.ForeignGAP.MPtr, ab::Tuple{Int, Int})

  decompositions = Tuple{Main.ForeignGAP.MPtr, Main.ForeignGAP.MPtr}[]
  if GAP.Globals.IsAbelian(G)
    return ab, (1, 1), 1, 1
  end
  n = ab[1]
  subs = GAP.Globals.NormalSubgroups(G)
  #First, I collect all the possible decompositions
  decompositions = Tuple{Main.ForeignGAP.MPtr, Main.ForeignGAP.MPtr}[]
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
  grp_id_list = Array{Tuple{Main.ForeignGAP.MPtr, Main.ForeignGAP.MPtr}, 1}(undef, length(decompositions))
  for i = 1:length(grp_id_list)
    grp_id_list[i] = (GAP.Globals.IdGroup(decompositions[i][1]), GAP.Globals.IdGroup(decompositions[i][2]))  
  end

  l1 = grp_id_list[1][1]
  a1 = l1[1]
  b1 = l1[2]
  l2 = grp_id_list[1][2]
  a2 = l2[1]
  b2 = l2[2]
  if length(grp_id_list) == 1
    return (a1, b1), (a2, b2), 1, 1
  end
  #I count the redundancy, i.e. the number of possible decompositions of the same type.
  red = 1
  for i = 2:length(grp_id_list)
    l1 = grp_id_list[i][1]
    a11 = l1[1]
    b11 = l1[2]
    l2 = grp_id_list[i][2]
    a21 = l2[1]
    b21 = l2[2]
    if min(a11, a21) > min(a1, a2)
      red = 1
      a1 = a11
      b1 = b11
      a2 = a21
      b2 = b21
    else
      if (a11, b11) == (a1, b1) && (a21, b21) == (a2, b2)
        red += 1 
      end
    end
  end
  #Finally, I count the numer of times a single subgroup appears in the lists.
  redfirst = 1
  GID_first = [a1, b1]
  GID_second = [a2, b2]
  ind = 1
  for i = 1:length(decompositions)
    if GAP.Globals.IdGroup(decompositions[i][1]) == GID_first && GAP.Globals.IdGroup(decompositions[i][2]) == GID_second
      ind = i
      break
    end
  end
  for i = ind+1:length(decompositions)
    if decompositions[i][1] == decompositions[ind][1]
      redfirst += 1
    end
  end
  return (a1, b1), (a2, b2), red, redfirst

end

###############################################################################
#
#  Merging fields
#
###############################################################################

function _to_composite(x::FieldsTower, y::FieldsTower)
  
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
  OK = NfAbsOrd(K, FakeFmpqMat(MatOrdNum, MatOrd.den))
  #Careful: we need to compute also the sign of the discriminant!
  OK.disc = discr
  OK.index = inde  
  OK.gen_index = fmpq(OK.index)
  if !isempty(lp)
    OK = Hecke.pmaximal_overorder_at(OK, lp)
  end
  OK.ismaximal = 1
  Hecke._set_maximal_order_of_nf(K, OK)

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
  
  #Computing closure of the automorphisms
  all_autos = Vector{NfToNfMor}(undef, degree(K))
  ind = 1
  aut1 = automorphisms(x.field, copy = false)
  aut2 = automorphisms(y.field, copy = false)
  for a1 in aut1
    for a2 in aut2
      ima1 = mx(a1.prim_img)
      ima2 = my(a2.prim_img)
      autns = Hecke.NfAbsNSToNfAbsNS(Kns, Kns, NfAbsNSElem[ima1, ima2])
      ima = mK\(autns(el))
      all_autos[ind] = NfToNfMor(K, K, ima)
      ind += 1
    end
  end
  Hecke._set_automorphisms_nf(K, all_autos)

  #Last thing: I have to add the maps of the subfields!
  emb1 = NfToNfMor(x.field, K, mK\(mx.prim_img))
  emb2 = NfToNfMor(y.field, K, mK\(my.prim_img))
  l1 = append!(NfToNfMor[emb1, emb2], x.subfields)
  embs = append!(l1, y.subfields)
  return FieldsTower(K, autK, embs)
  
end

#merge function when all the fields are automatically linearly disjoint
function _easy_merge(list1, list2, absolute_bound::fmpz)

  res = FieldsTower[]
  for x in list1
    for y in list2
      check_bound_disc(x, y, absolute_bound) || continue
      composite = _to_composite(x, y)
      if abs(discriminant(maximal_order(composite.field))) <= absolute_bound
        push!(res, composite)
      end
    end
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
  dK = degree(K)
  dL = degree(L)
  discK = abs(discriminant(maximal_order(K)))
  discL = abs(discriminant(maximal_order(L)))
  d = gcd(discK, discL)
  if issquare(d)
    d = root(d, 2)
  end
  d = d^(2*dK*dL - 2)
  d1 = gcd(discK^dL, discL^dK)
  d = gcd(d, d1)
  n = discK^dL * discL^dK
  return div(n, d) <= bound
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
  n_quo1 = lcm([degree(x) for x in lfieldsK])
  n_quo2 = lcm([degree(x) for x in lfieldsL])
  r, mr = Hecke.ray_class_groupQQ(O, modulo, true, lcm(n_quo1, n_quo2))
  Kt = PolynomialRing(K, "t", cached = false)[1]
  h = change_ring(lfieldsK[1].pol, Kt)
  S = norm_group(h, mr)[1]
  for i = 2:length(lfieldsK)
    h = change_ring(lfieldsK[i].pol, Kt)
    s = norm_group(h, mr)[1]
    S = intersect(s, S)
  end
  for i = 1:length(lfieldsL)
    h = change_ring(lfieldsL[i].pol, Kt)
    s = norm_group(h, mr)[1]
    S = intersect(s, S)
  end
  Q, mQ = quo(r, S)
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
    rK = Hecke.ramified_primes(maximal_order(K))
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
      rL = Hecke.ramified_primes(maximal_order(L))
      lfieldsL = maximal_abelian_subextension(L)
      rL1 = Set(fmpz[])
      for x in lfieldsL
        rL1 = union(rL1, Hecke.ramified_primes(maximal_order(x)))
      end
      if length(lfieldsL) == 1 && length(lfieldsK) == 1
        if degree(lfieldsL[1]) == 2 && degree(lfieldsK[1]) == 2
          if isempty(intersect(rL1, rK1)) || discriminant(maximal_order(lfieldsK[1])) != discriminant(maximal_order(lfieldsL[1]))
            k =  Set(vcat(rK, rL))
            k1 = union(rK1, rL1)
            if haskey(DK, (k, k1))
              push!(DK[(k, k1)],  i2)
            else
              DK[(k, k1)] = Int[i2]
            end
          end
        else
          if isempty(intersect(rL1, rK1)) || Hecke.islinearly_disjoint(lfieldsK[1], lfieldsL[1])
            k =  Set(vcat(rK, rL))
            k1 = union(rK1, rL1)
            if haskey(DK, (k, k1))
              push!(DK[(k, k1)],  i2)
            else
              DK[(k, k1)] = Int[i2]
            end
          end
        end
      else
        if isempty(intersect(rL1, rK1)) || check_norm_group_and_disc(lfieldsK, lfieldsL, bound_max_ab_sub)
          k =  Set(vcat(rK, rL))
          k1 = union(rK1, rL1)
          if haskey(DK, (k, k1))
            push!(DK[(k, k1)],  i2)
          else
            DK[(k, k1)] = Int[i2]
          end
        end
      end
    end
    #Now, I look at the length of the lists. I know that this must be divisible by redfirst...
    for (k, v) in DK
      if length(v) < redfirst
        continue
      else 
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
  end
  return D
end

function _second_sieve(list1::Vector{FieldsTower}, list2::Vector{FieldsTower}, absolute_bound::fmpz, red::Int, redsecond::Int, D::Dict)
  redfirst = divexact(red, redsecond)
  res = FieldsTower[]
  indD = 0
  lD = length(D)
  for v in values(D)
    indD += 1
    @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())Cluster $(indD)/$(lD) of length $(length(v))"
    @vprint :FieldsNonFancy 1 "Cluster $(indD)/$(lD) of length $(length(v))\n"
    if length(v) < red
      continue
    elseif length(v) == red
      @vtime :Fields 2 composite = _to_composite(list1[v[1][1]], list2[v[1][2]])
      disccomp = abs(discriminant(maximal_order(composite)))
      if disccomp <= absolute_bound
        push!(res, composite)
      end
    else
      number_expected_fields = div(length(v), red)
      to_discard = 0
      small_res = FieldsTower[]
      small_res_ind = Tuple{Int, Int}[]
      permu = randperm(length(v))
      for idx = 1:length(v)
        if length(small_res) == number_expected_fields || idx + to_discard > length(v)
          break
        end
        i = permu[idx]
        #I compute the field only if at least redfirst first fields appear in the list
        # and at least red/redfirst second fields appear
        ind1 = v[i][1]
        cnt = 1
        for j = i+1:length(v)
          if v[j][1] == ind1
            cnt += 1
          end
          if cnt == redfirst
            break
          end
        end
        if cnt != redfirst
          to_discard -= 1
          continue
        end
        ind2 = v[i][2]
        cnt = 1
        for j = i+1:length(v)
          if v[j][2] == ind2
            cnt += 1
          end
          if cnt == redsecond
            break
          end
        end
        if cnt != redsecond
          to_discard -= 1
          continue
        end
        @vtime :Fields 2 composite = _to_composite(list1[v[i][1]], list2[v[i][2]])
        disccomp = abs(discriminant(maximal_order(composite)))
        if disccomp <= absolute_bound
          #Check if I already have that field.
          found = false
          for j = 1:length(small_res)
            fj = small_res[j].field
            if first_check_isom(fj, composite.field)
              if v[i][1] != small_res_ind[j][1] && !Hecke.issubfield_normal(list1[v[i][1]].field, fj)[1] 
                continue
              elseif v[i][2] != small_res_ind[j][2] && !Hecke.issubfield_normal(list2[v[i][2]].field, fj)[1]
                continue
              else
                found = true
                break
              end
            end
          end
          if found 
            to_discard -= 1
            continue
          end
          to_discard += redfirst - 1
          push!(small_res, composite)
          push!(small_res_ind, (v[i][1], v[i][2]))
        end
      end
      append!(res, small_res)
    end
  end
  return res


end

function _merge(list1::Vector{FieldsTower}, list2::Vector{FieldsTower}, absolute_bound::fmpz, red::Int, redsecond::Int)

  if red == 1
    #All the fields are automatically linearly disjoint
    @vprint :Fields 1 "All the fields are linearly disjoint, easy case \n"
    @vprint :FieldsNonFancy 1 "All the fields are linearly disjoint, easy case \n"
    return _easy_merge(list1, list2, absolute_bound)
  end

  redfirst = divexact(red, redsecond)
  if redfirst < redsecond
    #switch the lists
    return _merge(list2, list1, absolute_bound, red, redfirst)
  end
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
  D = _first_sieve(list1, list2, absolute_bound, redfirst)
  if isempty(D)
    return res
  end
  @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())"
  
  nfields_after = sum(length(v) for v in values(D))
  @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())Fields after first part of sieving: $(nfields_after)\n"
  @vprint :FieldsNonFancy 1 "Fields after first part of sieving: $(nfields_after)\n"
  
  res = _second_sieve(list1, list2, absolute_bound, red, redsecond, D)
  
  @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())Fields found: $(length(res))\n"
  @vprint :FieldsNonFancy 1 "Fields found: $(length(res))\n"
  return res
  
end

function first_check_isom(K::AnticNumberField, L::AnticNumberField)
  OK = maximal_order(K)
  OL = maximal_order(L)
  if discriminant(OK) != discriminant(OL)
    return false
  end
  
  p = 200
  cnt = 1
  while cnt < 20
    cnt += 1
    p = next_prime(p)
    lp1 = prime_decomposition_type(OK, p)
    lp2 = prime_decomposition_type(OL, p)
    if length(lp1) != length(lp2)
      return false
    end
    if lp1[1] != lp2[1]
      return false
    end
  end
  return true
end
