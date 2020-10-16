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
  ffields = Vector{AnticNumberField}(undef, length(l))
  for i = 1:length(ffields)
    ffields[i] = fixed_field(l[i], rep)
  end
  return ffields
end

function fixed_field(x::FieldsTower, H::GAP.GapObj)
  gH = GAP.Globals.SmallGeneratingSet(H)

  auts = NfToNfMor[]
  found = 0 
  D = x.isomorphism
  autsx = automorphisms(number_field(x))
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