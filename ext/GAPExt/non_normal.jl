function to_non_normal(l::Vector{FieldsTower}, G::GAP.GapObj, deg::Int)
  for x in l
    assure_automorphisms(x)
    assure_isomorphism(x, G)
  end
  lC = GAP.Globals.ConjugacyClassesSubgroups(G)
  ind = 0
  for i = 1:length(lC)
    r = GAP.Globals.Representative(lC[i])
    if GAP.Globals.Size(r) == divexact(degree(l[1].field), deg) && GAP.Globals.Size(GAP.Globals.Core(G, r)) == 1
      ind = i
      break
    end
  end
  if iszero(ind)
    error("Representation not possible")
  end
  rep = GAP.Globals.Representative(lC[ind])
  ffields = Vector{AbsSimpleNumField}(undef, length(l))
  for i = 1:length(ffields)
    ffields[i] = fixed_field(l[i], rep)
  end
  return ffields
end

function fixed_field(x::FieldsTower, H::GAP.GapObj)
  gH = GAP.Globals.SmallGeneratingSet(H)

  auts = morphism_type(AbsSimpleNumField, AbsSimpleNumField)[]
  found = 0
  D = x.isomorphism
  autsx = automorphism_list(number_field(x))
  i = 0
  while length(gH) != found
    i += 1
    if D[autsx[i]] in gH
      push!(auts, autsx[i])
      found += 1
    end
  end
  return fixed_field(number_field(x), auts)[1]
end

function _find_discriminant_bound(n, i, disc)
  Gt = GAP.Globals.TransitiveGroup(n, i)
  @assert GAP.Globals.IsSolvable(Gt)
  id = GAP.Globals.IdGroup(Gt)
  G1 = GAP.Globals.SmallGroup(id)
  lC = GAP.Globals.ConjugacyClassesSubgroups(G1)
  ind = 0
  for k = 1:length(lC)
    H = GAP.Globals.Representative(lC[k])
    if GAP.Globals.Index(G1, H) != n
      continue
    end
    core = GAP.Globals.Core(G1, H)
    if !isone(GAP.Globals.Size(core))
      continue
    end
    mp = GAP.Globals.FactorCosetAction(G1, H)
    idT = GAP.Globals.TransitiveIdentification(GAP.Globals.Image(mp))
    if idT == i
      ind = i
      break
    end
  end
  cg = lC[ind]
  H = GAP.Globals.Representative(cg)
  conjs = GAP.Globals.Elements(cg)
  #I check if it is a Frobenius group!
  isfrobenius = true
  for i = 1:length(conjs)
    for j = i+1:length(conjs)
      if GAP.Globals.Size(GAP.Globals.Intersection(conjs[i], conjs[j])) != 1
        isfrobenius = false
        break
      end
    end
    if !isfrobenius
      break
    end
  end
  if isfrobenius
    @show "Frobenius!"
    #In this case, we can find a better bound for the closure!
    m = divexact(id[1], n)
    bdisc = disc^(2*m*n-m)
    return root(bdisc, n-1)
  end
  j = 1
  for i = 2:length(conjs)
    H = GAP.Globals.Intersection(H, conjs[i])
    j += 1
    if GAP.Globals.Size(H) == 1
      break
    end
  end
  return disc^(j*divexact(id[1], n))
end


function fields_transitive_group(n::Int, i::Int, disc::ZZRingElem)
  Gt = GAP.Globals.TransitiveGroup(n, i)
  @assert GAP.Globals.IsSolvable(Gt)
  id = GAP.Globals.IdGroup(Gt)
  G1 = GAP.Globals.SmallGroup(id)
  @show disc_NC = _find_discriminant_bound(n, i, disc)
  lf = fields(id[1], id[2], disc_NC)
  ln = to_non_normal(lf, G1, n)
  indices = Int[]
  for i = 1:length(ln)
    if abs(discriminant(maximal_order(ln[i]))) <= disc
      push!(indices, i)
    end
  end
  return ln[indices]
end
