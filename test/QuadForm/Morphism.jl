@testset "Morphism" begin
  L = integer_lattice(gram = zero_matrix(ZZ, 0, 0))
  @test_throws ArgumentError minimum(L)
  @test (@inferred short_vectors(L, 1)) == []
  @test (@inferred short_vectors(L, 1, 2)) == []

  G = ZZ[2 1 -1 -1 -1 1 1 -1 0 0 0 0 0 0 0 0; 1 2 -1 -1 -1 1 1 -1 0 0 0 0 0 0 0 0; -1 -1 2 0 1 0 -1 1 0 0 0 0 0 0 0 0; -1 -1 0 2 1 -1 0 0 0 0 0 0 0 0 0 0; -1 -1 1 1 2 0 -1 0 0 0 0 0 0 0 0 0; 1 1 0 -1 0 2 0 -1 0 0 0 0 0 0 0 0; 1 1 -1 0 -1 0 2 -1 0 0 0 0 0 0 0 0; -1 -1 1 0 0 -1 -1 2 0 0 0 0 0 0 0 0; 0 0 0 0 0 0 0 0 2 1 1 0 1 1 1 0; 0 0 0 0 0 0 0 0 1 2 1 0 1 1 0 0; 0 0 0 0 0 0 0 0 1 1 2 0 0 0 1 0; 0 0 0 0 0 0 0 0 0 0 0 2 1 0 -1 0; 0 0 0 0 0 0 0 0 1 1 0 1 4 1 0 1; 0 0 0 0 0 0 0 0 1 1 0 0 1 4 0 0; 0 0 0 0 0 0 0 0 1 0 1 -1 0 0 8 1; 0 0 0 0 0 0 0 0 0 0 0 0 1 0 1 18]
  L = integer_lattice(gram=G)
  @test length(shortest_vectors(L)) == 127

  A2 = root_lattice(:A, 2)
  Hecke.assert_has_automorphisms(A2, redo=true, try_small=false)
  @test automorphism_group_order(A2) == 12

  L = integer_lattice(gram=ZZ[3 1 -1 1 1 0 -1 -1 0 -1 1 0 -1 1 0 0 -1 1 1 -1 0 0 0 0 0 0; 1 3 1 1 0 1 0 0 -1 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1; -1 1 3 -1 0 0 0 1 -1 0 1 0 0 0 0 0 0 -1 -1 1 0 0 1 -1 1 1; 1 1 -1 3 1 1 -1 0 0 1 0 1 0 0 1 0 0 0 1 -1 0 1 0 1 0 0; 1 0 0 1 3 1 -1 1 1 0 0 0 -1 1 0 0 -1 1 1 -1 0 0 1 0 1 0; 0 1 0 1 1 3 1 0 1 0 0 1 0 1 0 0 0 0 0 0 1 0 0 0 0 1; -1 0 0 -1 -1 1 3 -1 1 0 -1 0 1 0 0 0 0 0 0 1 0 0 -1 0 -1 0; -1 0 1 0 1 0 -1 3 0 0 0 0 0 0 0 0 1 0 0 0 0 0 1 0 1 0; 0 -1 -1 0 1 1 1 0 3 -1 -1 1 -1 1 0 -1 0 1 1 0 0 1 0 1 0 0; -1 0 0 1 0 0 0 0 -1 3 0 0 1 -1 0 0 0 0 0 0 0 0 0 0 0 0; 1 1 1 0 0 0 -1 0 -1 0 3 0 0 1 0 0 0 0 0 0 0 0 1 0 1 1; 0 0 0 1 0 1 0 0 1 0 0 3 -1 0 0 -1 0 0 0 0 0 1 0 0 0 1; -1 0 0 0 -1 0 1 0 -1 1 0 -1 3 -1 0 0 0 -1 0 0 0 0 0 0 -1 -1; 1 0 0 0 1 1 0 0 1 -1 1 0 -1 3 0 0 0 0 1 0 1 0 0 0 1 0; 0 0 0 1 0 0 0 0 0 0 0 0 0 0 3 1 1 0 0 0 -1 1 0 1 0 0; 0 0 0 0 0 0 0 0 -1 0 0 -1 0 0 1 3 0 0 0 0 0 -1 0 0 1 0; -1 0 0 0 -1 0 0 1 0 0 0 0 0 0 1 0 3 0 -1 1 0 0 0 1 0 0; 1 0 -1 0 1 0 0 0 1 0 0 0 -1 0 0 0 0 3 1 0 -1 0 0 1 0 0; 1 0 -1 1 1 0 0 0 1 0 0 0 0 1 0 0 -1 1 3 -1 0 1 0 1 0 -1; -1 0 1 -1 -1 0 1 0 0 0 0 0 0 0 0 0 1 0 -1 3 0 0 -1 0 0 1; 0 0 0 0 0 1 0 0 0 0 0 0 0 1 -1 0 0 -1 0 0 3 0 0 -1 0 0; 0 0 0 1 0 0 0 0 1 0 0 1 0 0 1 -1 0 0 1 0 0 3 0 1 0 0; 0 0 1 0 1 0 -1 1 0 0 1 0 0 0 0 0 0 0 0 -1 0 0 3 0 1 0; 0 0 -1 1 0 0 0 0 1 0 0 0 0 0 1 0 1 1 1 0 -1 1 0 3 0 0; 0 0 1 0 1 0 -1 1 0 0 1 0 -1 1 0 1 0 0 0 0 0 0 1 0 3 1; 0 1 1 0 0 1 0 0 0 0 1 1 -1 0 0 0 0 0 -1 1 0 0 0 0 1 3])
  Hecke.__assert_has_automorphisms(L; use_everything=true);
  @test 18720000 == L.automorphism_group_order

  A = [[2 -1 0 0 0 0; -1 2 -1 0 0 0; 0 -1 2 -1 0 0; 0 0 -1 2 -1 0; 0 0 0 -1 2 0; 0 0 0 0 0 20], [2 0 0 0 -1 -1; 0 2 0 -1 0 -1; 0 0 2 -1 1 0; 0 -1 -1 4 1 2; -1 0 1 1 4 1; -1 -1 0 2 1 4], [2 -1 1 0 0 0; -1 2 -1 0 0 0; 1 -1 2 0 0 0; 0 0 0 2 0 0; 0 0 0 0 2 1; 0 0 0 0 1 8], [2 1 -1 -1 0 0; 1 2 -1 -1 0 0; -1 -1 2 1 0 0; -1 -1 1 2 0 0; 0 0 0 0 2 0; 0 0 0 0 0 12], [2 -1 0 0 0 -1; -1 2 0 0 0 0; 0 0 2 0 1 0; 0 0 0 2 1 0; 0 0 1 1 4 0; -1 0 0 0 0 4], [2 -1 1 0 -1 -1; -1 2 -1 0 1 1; 1 -1 2 0 0 0; 0 0 0 2 0 0; -1 1 0 0 4 1; -1 1 0 0 1 6], [2 -1 1 1 -1 0; -1 2 -1 -1 0 0; 1 -1 2 0 0 0; 1 -1 0 2 -1 0; -1 0 0 -1 2 0; 0 0 0 0 0 30]]
  # Genus representatives of some genus
  L = [integer_lattice(gram=matrix(QQ,6,6,i),cached=false) for i in A]
  # mass formula
  @test sum(1//automorphism_group_order(i) for i in L) == mass(genus(L[1]))
  # hardcoded orders
  orders = ZZRingElem[2880, 64, 384, 960, 192, 384, 7680]
  @test  orders == automorphism_group_order.(L)
  # test different options
  for i in L
    Hecke.__assert_has_automorphisms(i; use_everything=false, compress=false, redo=true)
  end
  @test  orders == automorphism_group_order.(L)

  for i in L
    Hecke.__assert_has_automorphisms(i; use_everything=true, compress=false, redo=true)
  end
  @test  orders == automorphism_group_order.(L)

  for i in L
    Hecke.__assert_has_automorphisms(i; use_everything=true, compress=false, redo=true, search_fixed_vectors=true)
  end
  @test  orders == automorphism_group_order.(L)

  for i in L
    Hecke.__assert_has_automorphisms(i; use_everything=true, compress=false, redo=true, search_fixed_vectors=false)
  end
  @test  orders == automorphism_group_order.(L)

  for i in L
    Hecke.__assert_has_automorphisms(i; use_everything=true, compress=true, redo=true, search_fixed_vectors=false)
  end
  @test  orders == automorphism_group_order.(L)

  for i in L
    Hecke.__assert_has_automorphisms(i; use_everything=true, compress=true, redo=true, search_fixed_vectors=false, short_vectors_direct=true)
  end
  @test  orders == automorphism_group_order.(L)
  for i in L
    Hecke.__assert_has_automorphisms(i; use_everything=true, compress=true, redo=true, search_fixed_vectors=true, short_vectors_direct=true)
  end
  @test  orders == automorphism_group_order.(L)

  for i in L
    Hecke.__assert_has_automorphisms(i; use_everything=false, compress=true, redo=true)
  end
  @test  orders == automorphism_group_order.(L)

  for i in L
    Hecke.__assert_has_automorphisms(i; use_everything=false, use_weyl=true, compress=true, redo=true)
  end
  @test  orders == automorphism_group_order.(L)

  for i in L
    Hecke.__assert_has_automorphisms(i; use_everything=false, use_weyl=true, use_projections=true, compress=true, redo=true)
  end
  @test  orders == automorphism_group_order.(L)

  L = integer_lattice(; gram = ZZ[-2 0 0 0 1 1 -1 -1 -1 -1 -1 -1 1 1 1 -1 -1; 0 -2 1 1 0 0 -1 -1 -1 1 -1 1 1 1 1 1 1; 0 1 -2 0 0 0 0 1 0 -1 0 -1 0 -1 0 -1 -1; 0 1 0 -2 0 0 0 0 0 -1 0 -1 0 0 -1 0 0; 1 0 0 0 -2 0 1 0 1 1 1 1 -1 -1 0 0 1; 1 0 0 0 0 -2 0 0 1 1 1 1 0 -1 0 1 1; -1 -1 0 0 1 0 -4 -2 -2 -1 -2 -1 2 0 0 1 -1; -1 -1 1 0 0 0 -2 -4 0 1 0 1 2 0 1 0 0; -1 -1 0 0 1 1 -2 0 -4 -2 -3 -2 2 2 1 1 0; -1 1 -1 -1 1 1 -1 1 -2 -4 -1 -3 0 0 0 0 -2; -1 -1 0 0 1 1 -2 0 -3 -1 -4 -1 2 2 0 1 0; -1 1 -1 -1 1 1 -1 1 -2 -3 -1 -4 0 0 0 -1 -2; 1 1 0 0 -1 0 2 2 2 0 2 0 -4 -1 -1 -1 0; 1 1 -1 0 -1 -1 0 0 2 0 2 0 -1 -4 -1 0 -1; 1 1 0 -1 0 0 0 1 1 0 0 0 -1 -1 -4 1 -1; -1 1 -1 0 0 1 1 0 1 0 1 -1 -1 0 1 -4 -1; -1 1 -1 0 1 1 -1 0 0 -2 0 -2 0 -1 -1 -1 -4]);
  @test Hecke.reduced_automorphism_group_order(L)==2

  L = integer_lattice(gram=QQ[3 1 -1 1 1 0 -1 -1 0 -1 1 0 -1 1 0 0 -1 1 1 -1 0 0 0 0 0 0; 1 3 1 1 0 1 0 0 -1 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1; -1 1 3 -1 0 0 0 1 -1 0 1 0 0 0 0 0 0 -1 -1 1 0 0 1 -1 1 1; 1 1 -1 3 1 1 -1 0 0 1 0 1 0 0 1 0 0 0 1 -1 0 1 0 1 0 0; 1 0 0 1 3 1 -1 1 1 0 0 0 -1 1 0 0 -1 1 1 -1 0 0 1 0 1 0; 0 1 0 1 1 3 1 0 1 0 0 1 0 1 0 0 0 0 0 0 1 0 0 0 0 1; -1 0 0 -1 -1 1 3 -1 1 0 -1 0 1 0 0 0 0 0 0 1 0 0 -1 0 -1 0; -1 0 1 0 1 0 -1 3 0 0 0 0 0 0 0 0 1 0 0 0 0 0 1 0 1 0; 0 -1 -1 0 1 1 1 0 3 -1 -1 1 -1 1 0 -1 0 1 1 0 0 1 0 1 0 0; -1 0 0 1 0 0 0 0 -1 3 0 0 1 -1 0 0 0 0 0 0 0 0 0 0 0 0; 1 1 1 0 0 0 -1 0 -1 0 3 0 0 1 0 0 0 0 0 0 0 0 1 0 1 1; 0 0 0 1 0 1 0 0 1 0 0 3 -1 0 0 -1 0 0 0 0 0 1 0 0 0 1; -1 0 0 0 -1 0 1 0 -1 1 0 -1 3 -1 0 0 0 -1 0 0 0 0 0 0 -1 -1; 1 0 0 0 1 1 0 0 1 -1 1 0 -1 3 0 0 0 0 1 0 1 0 0 0 1 0; 0 0 0 1 0 0 0 0 0 0 0 0 0 0 3 1 1 0 0 0 -1 1 0 1 0 0; 0 0 0 0 0 0 0 0 -1 0 0 -1 0 0 1 3 0 0 0 0 0 -1 0 0 1 0; -1 0 0 0 -1 0 0 1 0 0 0 0 0 0 1 0 3 0 -1 1 0 0 0 1 0 0; 1 0 -1 0 1 0 0 0 1 0 0 0 -1 0 0 0 0 3 1 0 -1 0 0 1 0 0; 1 0 -1 1 1 0 0 0 1 0 0 0 0 1 0 0 -1 1 3 -1 0 1 0 1 0 -1; -1 0 1 -1 -1 0 1 0 0 0 0 0 0 0 0 0 1 0 -1 3 0 0 -1 0 0 1; 0 0 0 0 0 1 0 0 0 0 0 0 0 1 -1 0 0 -1 0 0 3 0 0 -1 0 0; 0 0 0 1 0 0 0 0 1 0 0 1 0 0 1 -1 0 0 1 0 0 3 0 1 0 0; 0 0 1 0 1 0 -1 1 0 0 1 0 0 0 0 0 0 0 0 -1 0 0 3 0 1 0; 0 0 -1 1 0 0 0 0 1 0 0 0 0 0 1 0 1 1 1 0 -1 1 0 3 0 0; 0 0 1 0 1 0 -1 1 0 0 1 0 -1 1 0 1 0 0 0 0 0 0 1 0 3 1; 0 1 1 0 0 1 0 0 0 0 1 1 -1 0 0 0 0 0 -1 1 0 0 0 0 1 3])
  Hecke.__assert_has_automorphisms(L; redo = true, short_vectors_direct = false, use_dual = true, use_everything = true, search_invariant_subspace = false, do_lll = false, depth = 0);
  @test L.reduced_automorphism_group_order == 18720000
  Hecke.__assert_has_automorphisms(L; redo = true, short_vectors_direct = true, use_dual = true, use_everything = true, search_invariant_subspace = false, do_lll = false, depth = 0);
  @test L.reduced_automorphism_group_order == 18720000
  Hecke.__assert_has_automorphisms(L; redo = true, short_vectors_direct = true, use_dual = true, use_everything = true, search_invariant_subspace = true, do_lll = false, depth = 0);
  @test L.reduced_automorphism_group_order == 18720000

  # automorphisms from a (possibly redundant) generating set instead of a basis
  G2 = ZZMatrix[matrix(ZZ, 2, 2, [2, -1, -1, 2])]
  B = matrix(ZZ, 3, 2, [1, 0, 0, 1, 1, 1]) # e1, e2, e1 + e2 generate ZZ^2 redundantly
  gens, order = Hecke.automorphisms_from_generating_set(G2, B)
  @test order == 12
  @test all(g * G2[1] * transpose(g) == G2[1] for g in gens)
  @test order == automorphism_group_order(integer_lattice(gram = G2[1]))

  G17 = matrix(ZZ, 17, 17, [2,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,-1, 0,2,1,-1,1,-1,1,1,-1,-1,0,0,0,0,0,0,1, 0,1,2,-1,1,-1,1,1,-1,0,0,0,0,0,0,0,0, 0,-1,-1,2,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,1,1,0,2,-1,1,1,-1,-1,0,0,0,0,0,0,1, 0,-1,-1,0,-1,2,-1,-1,1,0,0,0,0,0,0,0,0, 0,1,1,0,1,-1,2,1,-1,-1,0,0,0,0,0,0,1, 0,1,1,0,1,-1,1,2,-1,-1,0,0,0,0,0,0,1, 0,-1,-1,0,-1,1,-1,-1,2,0,0,0,0,0,0,0,0, 1,-1,0,0,-1,0,-1,-1,0,4,0,0,0,0,0,0,-3, 0,0,0,0,0,0,0,0,0,0,2,1,1,1,-1,-1,0, 0,0,0,0,0,0,0,0,0,0,1,2,1,0,-1,-1,0, 0,0,0,0,0,0,0,0,0,0,1,1,2,1,-1,-1,0, 0,0,0,0,0,0,0,0,0,0,1,0,1,2,-1,0,0, 0,0,0,0,0,0,0,0,0,0,-1,-1,-1,-1,2,1,0, 0,0,0,0,0,0,0,0,0,0,-1,-1,-1,0,1,2,0, -1,1,0,0,1,0,1,1,0,-3,0,0,0,0,0,0,6])
  # Build a redundant generating set out of vectors of norm <= 4: greedily add
  # short vectors (in enumeration order) whose inclusion improves the
  # elementary divisors of the currently spanned sublattice, until they
  # generate ZZ^17; this yields more than 17 vectors, with no basis among the
  # first 17 of them.
  sv = short_vectors(integer_lattice(gram = G17), 4)
  sort!(sv, by = x -> x[2]) # sort by length
  vecs17 = ZZMatrix[matrix(ZZ, 1, 17, v) for (v, l) in sv if l <= 4]
  H17 = zero_matrix(ZZ, 0, 17)
  divs17 = ZZRingElem[]
  chosen17 = ZZMatrix[]
  nextra = 2
  for v in vecs17
    Ht = vcat(H17, v)
    newdivs = elementary_divisors(Ht)
    if newdivs != divs17 || extra > 0
      push!(chosen17, v)
      H17 = Ht
      divs17 = newdivs
      extra -= 1
    end
    length(divs17) == 17 && all(isone, divs17) && break
  end
  B17 = reduce(vcat, chosen17)
  gens17, order17 = Hecke.automorphisms_from_generating_set(ZZMatrix[G17], B17)
  @test order17 == 2140353331200
  @test all(g * G17 * transpose(g) == G17 for g in gens17)
  @test order17 == automorphism_group_order(integer_lattice(gram = G17))

end
