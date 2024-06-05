@testset "Genus" begin
  Qx, x = QQ["x"]
  K, a = number_field(x^2 - 2, "a")
  OK = maximal_order(K)
  Kt, t  = K["t"]

  E1, b1 = number_field(t^2 - a, "b1") # ramified at 2
  E2, b2 = number_field(t^2 - 5, "b2") # unramified at 2

  p = prime_decomposition(OK, 2)[1][1]
  q = prime_decomposition(OK, 3)[1][1]

  #
  # ramified & dyadic
  #

  g = @inferred genus(HermLat, E1, p, [(0, 1, 1, 0), (2, 2, -1, 1)], type = :det)
  @test is_ramified(g)
  @test !is_split(g)
  @test !is_inert(g)
  @test is_dyadic(g)
  @test scales(g) == [0, 2]
  @test ranks(g) == [1, 2]
  @test dets(g) == [1, -1]
  @test norms(g) == [0, 1]
  @test det(g) == -1
  @test discriminant(g, 1) == 1
  @test discriminant(g, 2) == 1
  @test discriminant(g) == 1
  @test g == g
  @test g != genus(HermLat, E1, p, [(0, 1, 1, 0), (2, 2, -1, 1), (6, 1, -1, 3)])
  @test g != genus(HermLat, E1, p)
  @test g != genus(HermLat, E1, p, [(0, 1, 1, 0), (2, 3, -1, 1)], type = :det)
  @test g != genus(HermLat, E1, p, [(0, 1, 1, 0), (1, 2, -1, 1)], type = :det)
  @test genus(HermLat, E1, p) != genus(HermLat, E1, q)
  @test genus(HermLat, E1, p) != genus(HermLat, E2, p)

  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, "text/plain", g, context = :compact => true) isa String
  @test sprint(show, g) isa String
  @test sprint(show, g, context = :compact => true) isa String
  L = @inferred representative(g)
  @test L in g
  # p => g is cached on L
  @test hermitian_lattice(E1; gram = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test is_local_norm(E1, K(det(gram_matrix(g))) * inv(d), p)

  # empty genus
  g = @inferred genus(HermLat, E1, p)
  @test is_ramified(g)
  @test !is_split(g)
  @test !is_inert(g)
  @test is_dyadic(g)
  @test rank(g) == 0
  @test scales(g) == []
  @test ranks(g) == []
  @test dets(g) == []
  @test norms(g) == []
  @test det(g) == 1
  @test discriminant(g) == 1
  @test g == g

  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, "text/plain", g, context = :compact => true) isa String
  @test sprint(show, g) isa String
  @test sprint(show, g, context = :compact => true) isa String
  L = @inferred representative(g)
  @test L in g
  # p => g is cached on L
  @test hermitian_lattice(E1; gram = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test is_local_norm(E1, K(det(gram_matrix(g))) * inv(d), p)


  g = @inferred genus(HermLat, E1, p, [(0, 1, 1, 0), (2, 2, -1, 1)], type = :disc)
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, "text/plain", g, context = :compact => true) isa String
  @test sprint(show, g) isa String
  @test sprint(show, g, context = :compact => true) isa String
  @test g == g
  @test representative(g) in g
  L = @inferred representative(g)
  @test L in g
  # p => g is cached on L
  @test hermitian_lattice(E1; gram = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test is_local_norm(E1, K(det(gram_matrix(g))) * inv(d), p)

  # negative scale
  g = @inferred genus(HermLat, E1, p, [(-2, 1, 1, -1), (2, 2, -1, 1)], type = :disc)
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, "text/plain", g, context = :compact => true) isa String
  @test sprint(show, g) isa String
  @test sprint(show, g, context = :compact => true) isa String
  @test g == g
  L = @inferred representative(g)
  @test L in g
  # p => g is cached on L
  @test hermitian_lattice(E1; gram = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test is_local_norm(E1, K(det(gram_matrix(g))) * inv(d), p)

  @test_throws ArgumentError genus(HermLat, E1, p, [(0, 1, 1, 1), (2, 2, -1, 0)], type = :det)
  @test_throws ArgumentError genus(HermLat, E1, p, [(0, 1, 1, 1), (2, 2, -1, 0)], type = :disc)
  @test_throws ArgumentError genus(HermLat, E1, p, [(0, 1, 1, 0), (2, 2, -1, 1)], type = :bla)
  # scale not increasing
  @test_throws ArgumentError genus(HermLat, E1, p, [(3, 1, 1, 0), (2, 2, -1, 1)])
  # negative rank
  @test_throws ArgumentError genus(HermLat, E1, p, [(1, -1, 1, 0), (2, 2, -1, 1)])
  # bad determinant class
  @test_throws ArgumentError genus(HermLat, E1, p, [(0, 1, 2, 0), (2, 2, -1, 1)])
  # wrong norm valuation (must 1 * 2 since rank is odd)
  @test_throws ArgumentError genus(HermLat, E1, p, [(1, 1, 1, 3)], type = :det)
  # wrong prime
  @test_throws ArgumentError genus(HermLat, E1, p, [(1, 1, 1)], type = :det)
  # wrong prime
  @test_throws ArgumentError genus(HermLat, E1, p, [(1, 1)])

  #
  # unramified & inert & dyadic
  #

  g = genus(HermLat, E2, p, [(0, 1, 1), (3, 5, -1)], type = :det)

  @test g == genus(HermLat, E2, p, [(0, 1), (3, 5)])

  @test !is_ramified(g)
  @test is_inert(g)
  @test !is_split(g)
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, "text/plain", g, context = :compact => true) isa String
  @test sprint(show, g) isa String
  @test sprint(show, g, context = :compact => true) isa String
  @test g == g
  L = @inferred representative(g)
  @test L in g
  # p => g is cached on L
  @test hermitian_lattice(E2; gram = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test is_local_norm(E2, K(det(gram_matrix(g))) * inv(d), p)

  # rank zero genus
  g = @inferred genus(HermLat, E2, p)
  @test rank(g) == 0
  @test !is_ramified(g)
  @test is_inert(g)
  @test !is_split(g)
  @test scales(g) == []
  @test ranks(g) == []
  @test dets(g) == []
  @test det(g) == 1
  @test discriminant(g) == 1
  @test g == g

  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, "text/plain", g, context = :compact => true) isa String
  @test sprint(show, g) isa String
  @test sprint(show, g, context = :compact => true) isa String
  L = @inferred representative(g)
  @test L in g
  # p => g is cached on L
  @test hermitian_lattice(E2; gram = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test is_local_norm(E2, K(det(gram_matrix(g))) * inv(d), p)

  g = genus(HermLat, E2, p, [(0, 1, 1), (2, 2, +1)], type = :disc)

  @test g == genus(HermLat, E2, p, [(0, 1), (2, 2)])

  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, "text/plain", g, context = :compact => true) isa String
  @test sprint(show, g) isa String
  @test sprint(show, g, context = :compact => true) isa String
  @test g == g
  L = @inferred representative(g)
  @test L in g
  # p => g is cached on L
  @test hermitian_lattice(E2; gram = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test is_local_norm(E2, K(det(gram_matrix(g))) * inv(d), p)

  # wrong det class
  @test_throws ArgumentError genus(HermLat, E2, p, [(0, 1, -1), (2, 2, +1)], type = :det)
  # wrong det class
  @test_throws ArgumentError genus(HermLat, E2, p, [(0, 1, +1), (2, 2, -1)], type = :det)
  # wrong det class
  @test_throws ArgumentError genus(HermLat, E2, p, [(0, 1, +2), (2, 2, -1)], type = :det)
  # wrong type
  @test_throws ArgumentError genus(HermLat, E2, p, [(0, 1, 1), (2, 2, -1)], type = :bla)
  # negative rank
  @test_throws ArgumentError genus(HermLat, E2, p, [(0, -1, 1), (2, 2, +1)], type = :det)
  # non-increasing scale
  @test_throws ArgumentError genus(HermLat, E2, p, [(3, 1, 1), (2, 2, +1)], type = :det)
  # wrong prime
  @test_throws ArgumentError genus(HermLat, E2, p, [(0, 1, 1, 1)], type = :det)

  #
  # ramified & non-dyadic
  #

  p = prime_decomposition(OK, 5)[1][1]
  g = genus(HermLat, E2, p, [(0, 1, 1), (2, 2, -1)], type = :det)
  @test rank(g) == 3
  @test is_ramified(g)
  @test !is_split(g)
  @test !is_inert(g)
  @test g == g

  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, "text/plain", g, context = :compact => true) isa String
  @test sprint(show, g) isa String
  @test sprint(show, g, context = :compact => true) isa String
  L = @inferred representative(g)
  @test L in g
  # p => g is cached on L
  @test hermitian_lattice(E2; gram = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test is_local_norm(E2, K(det(gram_matrix(g))) * inv(d), p)

  # Test some problem with non_norm_rep
  # It is cached on the genus
  @test all(1:100) do i
    g = genus(HermLat, E2, p, [(0, 1, 1), (2, 2, -1)], type = :det)
    hermitian_lattice(E2; gram = gram_matrix(g)) in g
  end

  # rank zero genus
  g = @inferred genus(HermLat, E2, p)
  @test rank(g) == 0
  @test is_ramified(g)
  @test !is_split(g)
  @test !is_inert(g)
  @test scales(g) == []
  @test ranks(g) == []
  @test dets(g) == []
  @test det(g) == 1
  @test discriminant(g) == 1
  @test g == g

  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, "text/plain", g, context = :compact => true) isa String
  @test sprint(show, g) isa String
  @test sprint(show, g, context = :compact => true) isa String
  L = @inferred representative(g)
  @test L in g
  # p => g is cached on L
  @test hermitian_lattice(E2; gram = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test is_local_norm(E2, K(det(gram_matrix(g))) * inv(d), p)

  g = genus(HermLat, E2, p, [(0, 1, 1), (2, 2, -1)], type = :disc)
  @test g == g
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, "text/plain", g, context = :compact => true) isa String
  @test sprint(show, g) isa String
  @test sprint(show, g, context = :compact => true) isa String
  @test_throws ArgumentError genus(HermLat, E2, p, [(0, 1, 1), (2, 2, -1)], type = :bla)
  L = @inferred representative(g)
  @test L in g
  # p => g is cached on L
  @test hermitian_lattice(E2; gram = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test is_local_norm(E2, K(det(gram_matrix(g))) * inv(d), p)

  # -1 is a local square, so the determinant equals discriminant
  @test discriminant(g, 2) == -1
  @test discriminant(g) == -1
  @test det(g) == -1

  #
  # unramified & split & non-dyadic
  #

  p = prime_decomposition(OK, 3)[1][1]
  g = genus(HermLat, E2, p, [(0, 2, 1)], type = :disc)
  @test !is_ramified(g)
  @test !is_inert(g)
  @test is_split(g)
  @test !is_dyadic(g)
  @test isone(inv(norm(g))*scale(g))
  @test discriminant(g) == 1
  @test g == g
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, "text/plain", g, context = :compact => true) isa String
  @test sprint(show, g) isa String
  @test sprint(show, g, context = :compact => true) isa String
  L = @inferred representative(g)
  @test L in g
  # p => g is cached on L
  @test hermitian_lattice(E2; gram = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test is_local_norm(E2, K(det(gram_matrix(g))) * inv(d), p)

  g = genus(HermLat, E2, p, [(0, 2, 1), (1, 1, 1), (2, 3, 1)], type = :disc)
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, "text/plain", g, context = :compact => true) isa String
  @test sprint(show, g) isa String
  @test sprint(show, g, context = :compact => true) isa String
  L = @inferred representative(g)
  @test L in g
  # p => g is cached on L
  @test hermitian_lattice(E2; gram = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test is_local_norm(E2, K(det(gram_matrix(g))) * inv(d), p)

  # Wrong det class in last component (must be 1)
  @test_throws ArgumentError g = genus(HermLat, E2, p, [(0, 2, 1), (1, 1, 1), (2, 3, -1)], type = :disc)

  #
  # ramified & non-dyadic and -1 not a local norm
  #
  K, _ = Hecke.rationals_as_number_field()
  Kt, t = K["t"]
  E, = number_field(t^2 + 7)
  p = prime_decomposition(maximal_order(K), 7)[1][1]

  # is_local_norm(E, -1, 7) == false

  g = genus(HermLat, E, p, [(0, 2, 1)], type = :disc)
  @test g == genus(HermLat, E, p, [(0, 2, -1)])
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, "text/plain", g, context = :compact => true) isa String
  @test sprint(show, g) isa String
  @test sprint(show, g, context = :compact => true) isa String
  @test g == g
  L = @inferred representative(g)
  @test L in g
  # p => g is cached on L
  @test hermitian_lattice(E; gram = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test is_local_norm(E, K(det(gram_matrix(g))) * inv(d), p)


  g = genus(HermLat, E, p, [(0, 2, 1), (1, 4, 1), (2, 3, -1)], type = :disc)
  # swap because of the ranks
  @test g == genus(HermLat, E, p, [(0, 2, -1), (1, 4, 1), (2, 3, 1)])
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, "text/plain", g, context = :compact => true) isa String
  @test sprint(show, g) isa String
  @test sprint(show, g, context = :compact => true) isa String
  L = @inferred representative(g)
  @test L in g
  # p => g is cached on L
  @test hermitian_lattice(E; gram = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test is_local_norm(E, K(det(gram_matrix(g))) * inv(d), p)

  for t in [(0, 1, 1), (0, 1, -1), (0, 2, 1), (0, 2, -1), (1, 2, -1)]
    g = genus(HermLat, E, p, [t])
    @test sprint(show, "text/plain", g) isa String
    @test sprint(show, "text/plain", g, context = :compact => true) isa String
    @test sprint(show, g) isa String
    @test sprint(show, g, context = :compact => true) isa String
    @test g == g
    L = @inferred representative(g)
    @test L in g
    # p => g is cached on L
    @test hermitian_lattice(E; gram = gram_matrix(g)) in g
    d = @inferred det_representative(g)
    @test is_local_norm(E, K(det(gram_matrix(g))) * inv(d), p)
  end

  #  odd scale, so rank even, and rank/2 is odd/even => det must be -1,1
  @test_throws ArgumentError genus(HermLat, E, p, [(1, 1, 1)])
  @test_throws ArgumentError genus(HermLat, E, p, [(1, 2, 1)])
  @test_throws ArgumentError genus(HermLat, E, p, [(1, 6, 1)])
  @test_throws ArgumentError genus(HermLat, E, p, [(1, 4, -1)])

  ##############################################################################
  #
  #  Now global
  #
  ##############################################################################

  Qx, x = QQ["x"]
  K, a = number_field(x^2 - 2, "a")
  OK = maximal_order(K)
  Kt, t  = K["t"]

  E1, b1 = number_field(t^2 - a, "b1") # ramified at 2
  E2, b2 = number_field(t^2 - 5, "b2") # unramified at 2

  p = prime_decomposition(OK, 2)[1][1]
  q = prime_decomposition(OK, 3)[1][1]

  g = @inferred genus(HermLat, E1, p, [(0, 1, 1, 0), (2, 2, -1, 1)])
  L = representative(g)
  G = genus(L)
  @test sprint(show, "text/plain", G) isa String
  @test sprint(show, "text/plain", G, context = :compact => true) isa String
  @test sprint(show, G) isa String
  @test sprint(show, G, context = :compact => true) isa String
  @test scale(G) == scale(L)
  @test norm(G) == norm(L)

  g = @inferred genus(HermLat, E1, q, [(0, 2, 1)])
  M = representative(g)
  G2 = genus(M)
  @test genus(representative(direct_sum(G, G2))) == direct_sum(G, G2)
  @test genus(representative(direct_sum(G2, G))) == direct_sum(G2, G)
  @test scale(G2) == scale(M)
  @test norm(G2) == norm(M)

  rlp = real_places(K)
  sig = Dict(rlp[1] => 2, rlp[2] => 2)
  G = genus([g], sig)
  @test G == genus([g], [(rlp[1], 2), (rlp[2], 2)])

  # rank 1 representative
  Qx, x = polynomial_ring(FlintQQ, "x");
  f = x^2 + x - 1;
  K, a = number_field(f, "a", cached = false);
  Kt, t = polynomial_ring(K, "t");
  g = t^2 - a*t + 1;
  E, b = number_field(g, "b", cached = false);
  D = matrix(E, 1, 1, [-a + 2]);
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [1]), map(E, [a]), map(E, [b]), map(E, [a*b])];
  LM = hermitian_lattice(E, gens, gram = D);
  L2 = @inferred representative(genus(LM))
  @test is_isometric_with_isometry(LM, L2)[1]

  # Fix norm in non-dyadic ramified case

  # Rank 1 example
  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x^10 - 10*x^8 + 35*x^6 + x^5 - 50*x^4 - 5*x^3 + 25*x^2 + 5*x - 1
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2 - a*t + 1
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 1, 1, [1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [5]), map(E, [a + 3]), map(E, [a^2 + 1]), map(E, [a^3 + 2]), map(E, [a^4 + 4]), map(E, [a^5 + 3]), map(E, [a^6 + 1]), map(E, [a^7 + 2]), map(E, [a^8 + 4]), map(E, [a^9 + 3]), map(E, [b + 4]), map(E, [a*b + 4*a]), map(E, [a^2*b + 4*a^2]), map(E, [a^3*b + 4*a^3]), map(E, [a^4*b + 4*a^4]), map(E, [a^5*b + 4*a^5]), map(E, [a^6*b + 4*a^6]), map(E, [a^7*b + 4*a^7]), map(E, [a^8*b + 4*a^8]), map(E, [a^9*b + 4*a^9])]
  L = hermitian_lattice(E, gens, gram = D)

  @test norm(L) == norm(genus(L))

  # Hyperbolic plane of scale P^3, and norm p^2
  E,b = cyclotomic_field_as_cm_extension(3)
  M = matrix(E, 2, 2, [           0  (1-b)^3;
                       (1-inv(b))^3        0])
  L = lattice(hermitian_space(E, M))
  @test norm(L) == norm(genus(L))

  ##############################################################################
  #
  #  Local genera hermitian
  #
  #############################################################################

  K, a = cyclotomic_real_subfield(8, "a")
  Kt, t = polynomial_ring(K, "t")
  L, b = number_field(t^2 - a * t + 1)

  p = prime_decomposition(maximal_order(K), 2)[1][1]
  G = @inferred hermitian_local_genera(L, p, 4, 2, 0, 4)
  @test length(G) == 15
  for i in 1:length(G)
    @test rank(G[i]) == 4
    @test (@inferred representative(G[i])) in G[i]
  end

  for i in 1:10
    g1 = rand(G)
    g2 = rand(G)
    g3 = @inferred direct_sum(g1, g2)
    @test genus(representative(g3), p) == genus(direct_sum(representative(g1), representative(g2))[1], p)
  end

  GG = G[1]
  u = @inferred uniformizer(GG)
  @assert parent(u) == K

  p = prime_decomposition(maximal_order(K), 3)[1][1]
  G = hermitian_local_genera(L, p, 4, 2, 0, 4)
  for i in 1:10
    g1 = rand(G)
    g2 = rand(G)
    g3 = @inferred direct_sum(g1, g2)
    @test genus(representative(g3), p) == genus(direct_sum(representative(g1), representative(g2))[1], p)
  end

  p = prime_decomposition(maximal_order(K), 17)[1][1]
  G = @inferred hermitian_local_genera(L, p, 5, 5, 0, 5)
  @test length(G) == 7
  for i in 1:length(G)
    @test rank(G[i]) == 5
    @test (@inferred representative(G[i])) in G[i]
  end

  K, a = cyclotomic_real_subfield(8, "a")
  Kt, t = K["t"]
  L, b = number_field(t^2 - a * t + 1)
  p = prime_decomposition(maximal_order(K), 2)[1][1]
  l =  Vector{Tuple{Int, Int, Int, Int}}[[(0, 3, 1, 0), (4, 1, 1, 2)],
       [(0, 3, -1, 0), (4, 1, 1, 2)],
       [(0, 3, 1, 0), (4, 1, -1, 2)],
       [(0, 3, -1, 0), (4, 1, -1, 2)],
       [(0, 2, 1, 0), (2, 2, 1, 1)],
       [(0, 2, -1, 0), (2, 2, 1, 1)],
       [(0, 2, 1, 1), (2, 2, 1, 1)],
       [(0, 2, 1, 0), (2, 2, 1, 2)],
       [(0, 2, 1, 1), (2, 2, -1, 1)],
       [(0, 2, -1, 0), (2, 2, 1, 2)],
       [(0, 2, 1, 1), (2, 2, 1, 2)],
       [(0, 1, 1, 0), (1, 2, 1, 1), (2, 1, 1, 1)],
       [(0, 1, -1, 0), (1, 2, 1, 1), (2, 1, 1, 1)],
       [(1, 4, 1, 1)],
       [(1, 4, -1, 1)]]
  Gs = Hecke.HermLocalGenus{typeof(L), typeof(p)}[ genus(HermLat, L, p, x) for x in l ]
  myG = @inferred hermitian_local_genera(L, p, 4, 2, 0, 4)
  @test length(Gs) == length(myG)
  @test all(x -> x in Gs, myG)
  @test all(x -> x in myG, Gs)

  K, a = cyclotomic_real_subfield(8, "a")
  Kt, t = K["t"]
  L, b = number_field(t^2 - a * t + 1)
  rlp = real_places(K)
  G = @inferred hermitian_genera(L, 3, Dict(rlp[1] => 1, rlp[2] => 1), 100 * maximal_order(L))
  for i in 1:10
    g1 = rand(G)
    g2 = rand(G)
    M, = @inferred direct_sum(representative(g1), representative(g2))
    @test M in (g1 + g2)
  end

end

@testset "non-integral genera" begin
  
  # rescaling
  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x^2 - 3
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2 + 1
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [1, 1, 0]), map(E, [0, 0, -1]), map(E, [(1//2*a + 1//2)*b + 1//2*a - 1//2, 0, 0])]
  L = hermitian_lattice(E, gens, gram = D)
  G = genus(L)
  G2 = @inferred rescale(G, -1//(a^2+5))
  @test G2 == genus(rescale(L, -1//(a^2+5)))
  @test_throws ArgumentError rescale(G, b)
  @test rescale(G2, -(a^2+5)) == G

  # representatives
  reps = representatives(G2)
  @test length(reps) == 1
  @test is_isometric(reps[1], rescale(L, -1//(a^2+5)))
  L2 = representative(rescale(G, 1//100000001))
  @test is_isometric(L2, rescale(L, 1//100000001))
  
  # enumeration
  E, b = cyclotomic_field_as_cm_extension(8, cached=false)
  Eabs, EabstoE = absolute_simple_field(E)
  DEabs = different(maximal_order(Eabs))
  DE = EabstoE(DEabs)
  rp = real_places(base_field(E))
  sig = Dict(r => 1 for r in rp)
  gh = @inferred hermitian_genera(E, 4, sig, inv(DE), min_scale =inv(DE)^2)
  @test length(gh) == 22
  @test allunique(gh)
  @test all(G -> signatures(G) == sig, gh)
  @test all(G -> rank(G) == 4, gh)
  @test all(G -> !is_integral(G), gh)
  @test all(G -> is_integral(Hecke._scale(G)*fractional_ideal(maximal_order(E), DE)^2), gh)
  
  K = base_field(E)
  sig[rp[1]] = 7
  sig[rp[2]] = 3
  gh = @inferred hermitian_genera(E, 8, sig, E(1//135)*maximal_order(E), min_scale = E(1//45)*maximal_order(E), max_scale = E(45)*maximal_order(E))
  @test allunique(gh)
  @test all(G -> (signatures(G), rank(G)) == (sig, 8), gh)
  @test all(G -> !is_integral(G), gh)
  @test all(G -> is_integral(K(45)*Hecke._scale(G)), gh)
  @test all(G -> is_integral(K(45)*inv(Hecke._scale(G))), gh)
  for G in gh
    @test prod([fractional_ideal(prime(g))^(sum([rank(g,i)*scale(g,i) for i in 1:length(g)])) for g in G.LGS]) == inv(135*maximal_order(base_field(E)))
  end

  @test_throws ArgumentError hermitian_genera(E, -1, sig, DE)
  @test_throws ArgumentError hermitian_genera(E, 1, sig, DE, min_scale = 0*DE)
  @test_throws ArgumentError hermitian_genera(E, 1, sig, DE, max_scale = 0*DE)
  sig[rp[1]] = -12
  @test_throws ArgumentError hermitian_genera(E, 4, sig, DE)
end

@testset "Hermitian form with given invariants" begin
  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x^6 + x^5 - 5*x^4 - 4*x^3 + 6*x^2 + 3*x - 1
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2 - a*t + 1
  E, b = number_field(g, "b", cached = false);
  S = unique([restrict(r, K) for r in filter(!is_real, infinite_places(E)) if is_real(restrict(r, K))]);
  sort!(S, lt=(p,q) -> isless(real(embedding(p).r), real(embedding(q).r)));
  vals = Int[2, 2, 2, 2, 0, 2];
  sig = Dict(S[i] => vals[i] for i in 1:6);
  OK = maximal_order(K);
  ps = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[ideal(OK, v) for v in Vector{AbsSimpleNumFieldOrderElem}[map(OK, [2, 6*a^4 + 4*a^3 - 6*a^2 - 2*a + 2]), map(OK, [13, a + 11])]];
  datas = [[(0, 2, 1)], [(-11, 2, 1)]];
  lgs = Hecke.HermLocalGenus{typeof(E), AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}[genus(HermLat, E, ps[i], datas[i]) for i in 1:2];
  G = Hecke.HermGenus(E, 2, lgs, sig)
  h = Hecke._hermitian_form_with_invariants(E, 2, Hecke._non_norm_primes(local_symbols(G)), sig)
  L = lattice(hermitian_space(E, h))
  sig2 = signatures(genus(L))
  @test all(p -> sig[p] == sig2[p], S)
end

@testset "Hashes" begin
  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x - 1
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2 + 3
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [11//2*b + 41//2, b - 5, 0]), map(E, [-107//2*b + 189//2, 18*b, -b - 9]), map(E, [-29*b + 105, 15*b - 9, -2*b - 6])]
  L = hermitian_lattice(E, gens, gram = D)
  p1 = minimum(support(3*maximal_order(E))[1])
  p2 = minimum(support(2*maximal_order(E))[1])
  @test length(unique!([Hecke._genus(L), genus(L)])) == 1
  @test length(unique!([genus(L, p1), genus(L, p1)])) == 1
  @test length(unique!([genus(L, p2), genus(L, p2)])) == 1

  L = lattice(hermitian_space(E, 0))
  G = genus(L)
  @test length(unique([G ,G, G])) == 1
end
