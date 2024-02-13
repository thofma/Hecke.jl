#function show(io::IO, M::ResidueRingPolyMap)
#  println(io, "Map $(domain(M)) -> $(codomain(M)): gen -> $(M.gen_image)")
#  if isdefined(M, :coeff_map)
#    println(io, "using coeff map: ", M.coeff_map)
#  end
#end
#
#function ResidueRingPolyMap_image(M::ResidueRingPolyMap{D, C}, a::EuclideanRingResidueRingElem{T}) where {D, C, T}
#  #a should be in the domain of M...
#  if isdefined(M, :coeff_map)
#    I = codomain(M)(0)
#    for i=degree(a.data):-1:0
#      I = I*M.gen_image + M.coeff_map(coeff(a.data, i))
#    end
#  else
#    I = codomain(M)(0)
#    for i=degree(a.data):-1:0
#      I = I*M.gen_image + coeff(a.data, i)
#    end
#  end
#  return I
#end
#
#function ResidueRingPolyMap_preimage(M::ResidueRingPolyMap{D, C}, a::EuclideanRingResidueRingElem{T}) where {D, C, T}
#  #a should be in the codomain of M...
#  #
#  # a good 1st attempt. If many preimages are needed, the matrix Mt
#  # and the rref or whatever solve is used should be cached and reused.
#  #
#  R = codomain(M)
#  parent(a) == R || error("mixed rings in preimage")
#  g = gens(domain(M))
#  im_gen = map(x->M(x), g) ## possibly should be cached and stored
#  ## need to write the elements in a matrix, solve the eqn for a
#  Mt = zero_matrix(base_ring(base_ring(R)), degree(R.modulus), degree(R.modulus))
#  for i=1:degree(R.modulus)
#    elem_to_mat_row!(Mt, i, im_gen[i])
#  end
#  b = zero_matrix(base_ring(base_ring(R)), 1, degree(R.modulus))
#  elem_to_mat_row!(b, 1, a)
#  s = Nemo._solve_rational(Mt', b') # why, oh why is solve operating on columns????
#  if isa(s, Tuple) ## again, why, oh why is solve doing things differently
#                   ## over rings than fields?
#    s = s[1] * inv(s[2]) # all rings here (type) are actually fields (math)
#  end
#  ## need a version returning a bool to test is solution exists
#  ## without an error!
#  if isdefined(M, :coeff_map)
#    s = sum([preimage(M.coeff_map, s[i,1])*g[i] for i=1:length(g)])
#  else
#    s = sum([s[i,1]*g[i] for i=1:length(g)])
#  end
#  @assert parent(s) == domain(M)
#  return s
#end
#
