function galois_group_non_normal(A::ClassField, ::QQField)
  k = number_field(A)
  ka, mka = absolute_simple_field(k)
  au = automorphism_list(k)
  G, S = galois_group(ka)

  Qt = parent(defining_polynomial(ka))
  gn = mka(gen(ka))
  si = [Qt(preimage(mka, x(gn))) for x = au]

  #g is the galois group over Q, we now want the subgroup A/k
  #the group of the base field
  r = roots(S, 2)
  @show length(r)
  @show length(r), G
  s, ms = sub(G, [G([findfirst(isequal(y(x)), r) for x = r]) for y = si])
  o = orbits(s)
  @assert all(x->length(o[1]) == length(x), o)
  @show o, [x.seeds for x = o]
  q = Oscar.GaloisGrp.action_on_block_system(G, [x.seeds for x = o])  
  #the small_knot is correct, hopefully, if
  # kernel(q) == image(ms) 
  return ms, q
end
