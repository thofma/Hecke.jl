@testset "Genus" begin
  Qx, x = QQ["x"]
  K, a = NumberField(x^2 - 2, "a")
  OK = maximal_order(K)
  Kt, t  = K["t"]

  E1, b1 = NumberField(t^2 - a, "b1") # ramified at 2
  E2, b2 = NumberField(t^2 - 5, "b2") # unramified at 2

  p = prime_decomposition(OK, 2)[1][1]
  q = prime_decomposition(OK, 3)[1][1]

  #
  # ramified & dyadic
  #

  g = @inferred genus(HermLat, E1, p, [(0, 1, 1, 0), (2, 2, -1, 1)], type = :det)
  @test isramified(g)
  @test !issplit(g)
  @test !isinert(g)
  @test scales(g) == [0, 2]
  @test ranks(g) == [1, 2]
  @test dets(g) == [1, -1]
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
  @test hermitian_lattice(E1; gram_ambient_space = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test islocal_norm(E1, K(det(gram_matrix(g))) * inv(d), p)

  # empty genus
  g = @inferred genus(HermLat, E1, p)
  @test isramified(g)
  @test !issplit(g)
  @test !isinert(g)
  @test rank(g) == 0
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
  @test hermitian_lattice(E1; gram_ambient_space = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test islocal_norm(E1, K(det(gram_matrix(g))) * inv(d), p)


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
  @test hermitian_lattice(E1; gram_ambient_space = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test islocal_norm(E1, K(det(gram_matrix(g))) * inv(d), p)

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
  @test hermitian_lattice(E1; gram_ambient_space = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test islocal_norm(E1, K(det(gram_matrix(g))) * inv(d), p)

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

  @test !isramified(g)
  @test isinert(g)
  @test !issplit(g)
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, "text/plain", g, context = :compact => true) isa String
  @test sprint(show, g) isa String
  @test sprint(show, g, context = :compact => true) isa String
  @test g == g
  L = @inferred representative(g)
  @test L in g
  # p => g is cached on L
  @test hermitian_lattice(E2; gram_ambient_space = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test islocal_norm(E2, K(det(gram_matrix(g))) * inv(d), p)

  # rank zero genus
  g = @inferred genus(HermLat, E2, p)
  @test rank(g) == 0
  @test !isramified(g)
  @test isinert(g)
  @test !issplit(g)
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
  @test hermitian_lattice(E2; gram_ambient_space = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test islocal_norm(E2, K(det(gram_matrix(g))) * inv(d), p)

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
  @test hermitian_lattice(E2; gram_ambient_space = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test islocal_norm(E2, K(det(gram_matrix(g))) * inv(d), p)

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
  @test isramified(g)
  @test !issplit(g)
  @test !isinert(g)
  @test g == g

  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, "text/plain", g, context = :compact => true) isa String
  @test sprint(show, g) isa String
  @test sprint(show, g, context = :compact => true) isa String
  L = @inferred representative(g)
  @test L in g
  # p => g is cached on L
  @test hermitian_lattice(E2; gram_ambient_space = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test islocal_norm(E2, K(det(gram_matrix(g))) * inv(d), p)

  # Test some problem with non_norm_rep
  # It is cached on the genus
  @test all(1:100) do i
    g = genus(HermLat, E2, p, [(0, 1, 1), (2, 2, -1)], type = :det)
    hermitian_lattice(E2; gram_ambient_space = gram_matrix(g)) in g
  end

  # rank zero genus
  g = @inferred genus(HermLat, E2, p)
  @test rank(g) == 0
  @test isramified(g)
  @test !issplit(g)
  @test !isinert(g)
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
  @test hermitian_lattice(E2; gram_ambient_space = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test islocal_norm(E2, K(det(gram_matrix(g))) * inv(d), p)

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
  @test hermitian_lattice(E2; gram_ambient_space = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test islocal_norm(E2, K(det(gram_matrix(g))) * inv(d), p)

  # -1 is a local square, so the determinant equals discriminant
  @test discriminant(g, 2) == -1
  @test discriminant(g) == -1
  @test det(g) == -1

  #
  # unramified & split & non-dyadic
  #

  p = prime_decomposition(OK, 3)[1][1]
  g = genus(HermLat, E2, p, [(0, 2, 1)], type = :disc)
  @test !isramified(g)
  @test !isinert(g)
  @test issplit(g)
  @test discriminant(g) == 1
  @test g == g
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, "text/plain", g, context = :compact => true) isa String
  @test sprint(show, g) isa String
  @test sprint(show, g, context = :compact => true) isa String
  L = @inferred representative(g)
  @test L in g
  # p => g is cached on L
  @test hermitian_lattice(E2; gram_ambient_space = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test islocal_norm(E2, K(det(gram_matrix(g))) * inv(d), p)

  g = genus(HermLat, E2, p, [(0, 2, 1), (1, 1, 1), (2, 3, 1)], type = :disc)
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, "text/plain", g, context = :compact => true) isa String
  @test sprint(show, g) isa String
  @test sprint(show, g, context = :compact => true) isa String
  L = @inferred representative(g)
  @test L in g
  # p => g is cached on L
  @test hermitian_lattice(E2; gram_ambient_space = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test islocal_norm(E2, K(det(gram_matrix(g))) * inv(d), p)

  # Wrong det class in last component (must be 1)
  @test_throws ArgumentError g = genus(HermLat, E2, p, [(0, 2, 1), (1, 1, 1), (2, 3, -1)], type = :disc)

  #
  # ramified & non-dyadic and -1 not a local norm
  #
  K, _ = Hecke.rationals_as_number_field()
  Kt, t = K["t"]
  E, = number_field(t^2 + 7)
  p = prime_decomposition(maximal_order(K), 7)[1][1]

  # islocal_norm(E, -1, 7) == false

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
  @test hermitian_lattice(E; gram_ambient_space = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test islocal_norm(E, K(det(gram_matrix(g))) * inv(d), p)


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
  @test hermitian_lattice(E; gram_ambient_space = gram_matrix(g)) in g
  d = @inferred det_representative(g)
  @test islocal_norm(E, K(det(gram_matrix(g))) * inv(d), p)

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
    @test hermitian_lattice(E; gram_ambient_space = gram_matrix(g)) in g
    d = @inferred det_representative(g)
    @test islocal_norm(E, K(det(gram_matrix(g))) * inv(d), p)
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
  K, a = NumberField(x^2 - 2, "a")
  OK = maximal_order(K)
  Kt, t  = K["t"]

  E1, b1 = NumberField(t^2 - a, "b1") # ramified at 2
  E2, b2 = NumberField(t^2 - 5, "b2") # unramified at 2

  p = prime_decomposition(OK, 2)[1][1]
  q = prime_decomposition(OK, 3)[1][1]

  g = @inferred genus(HermLat, E1, p, [(0, 1, 1, 0), (2, 2, -1, 1)])
  L = representative(g)
  G = genus(L)
  @test sprint(show, "text/plain", G) isa String
  @test sprint(show, "text/plain", G, context = :compact => true) isa String
  @test sprint(show, G) isa String
  @test sprint(show, G, context = :compact => true) isa String
  g = @inferred genus(HermLat, E1, q, [(0, 2, 1)])
  M = representative(g)
  G2 = genus(M)
  @test genus(representative(orthogonal_sum(G, G2))) == orthogonal_sum(G, G2)
  @test genus(representative(orthogonal_sum(G2, G))) == orthogonal_sum(G2, G)

  rlp = real_places(K)
  sig = Dict(rlp[1] => 2, rlp[2] => 2)
  G = genus([g], sig)
  @test G == genus([g], [(rlp[1], 2), (rlp[2], 2)])

  #
  # genus_generators
  #
  
  Qx, x = PolynomialRing(FlintQQ, "x")
  f = x^2 - 2
  K, a = NumberField(f, "a", cached = false)
  Kt, t = PolynomialRing(K, "t")
  g = t^2 + 1
  E, b = NumberField(g, "b", cached = false)
  D = matrix(E, 2, 2, [1, 2, 2, 1])
  gene = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [1, 0]), map(E, [a, 0]), map(E, [b + 1, 0]), map(E, [1//2*a*b + 1//2*a, 0]), map(E, [0, 1]), map(E, [0, a]), map(E, [0, b + 1]), map(E, [0, 1//2*a*b + 1//2*a])]

  L = hermitian_lattice(E, generators = gene, gram_ambient_space = D)
  gens, def, P0 = @inferred Hecke.genus_generators(L)
  @test length(gens) == 0
  @test !def
  @test P0 == Hecke.smallest_neighbour_prime(L)[2]

  Qx, x = PolynomialRing(FlintQQ, "x")
  f = x^6 + x^5 + x^4 + x^3 + x^2 + x + 1
  K, z_7 = NumberField(f, "a", cached = false)
  Kt, t = PolynomialRing(K, "t")
  g = t^2 - 3
  E, b = NumberField(g, "b", cached = false)
  D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
  gene = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [4, 0, 0, 0]), map(E, [4*z_7, 0, 0, 0]), map(E, [4*z_7^2, 0, 0, 0]), map(E, [4*z_7^3, 0, 0, 0]), map(E, [4*z_7^4, 0, 0, 0]), map(E, [4*z_7^5, 0, 0, 0]), map(E, [2*b + 2, 0, 0, 0]), map(E, [2*z_7*b + 2*z_7, 0, 0, 0]), map(E, [2*z_7^2*b + 2*z_7^2, 0, 0, 0]), map(E, [2*z_7^3*b + 2*z_7^3, 0, 0, 0]), map(E, [2*z_7^4*b + 2*z_7^4, 0, 0, 0]), map(E, [2*z_7^5*b + 2*z_7^5, 0, 0, 0]), map(E, [2, 2, 0, 0]), map(E, [2*z_7, 2*z_7, 0, 0]), map(E, [2*z_7^2, 2*z_7^2, 0, 0]), map(E, [2*z_7^3, 2*z_7^3, 0, 0]), map(E, [2*z_7^4, 2*z_7^4, 0, 0]), map(E, [2*z_7^5, 2*z_7^5, 0, 0]), map(E, [2*b, 2*b, 0, 0]), map(E, [2*z_7*b, 2*z_7*b, 0, 0]), map(E, [2*z_7^2*b, 2*z_7^2*b, 0, 0]), map(E, [2*z_7^3*b, 2*z_7^3*b, 0, 0]), map(E, [2*z_7^4*b, 2*z_7^4*b, 0, 0]), map(E, [2*z_7^5*b, 2*z_7^5*b, 0, 0]), map(E, [(-246*z_7^5 + 882*z_7^4 - 180*z_7^3 + 720*z_7^2 - 151*z_7 - 168)*b + 1133*z_7^5 + 47*z_7^4 + 2267*z_7^3 + 190*z_7^2 + 731*z_7 + 165, (2436*z_7^5 + 5*z_7^4 + 3744*z_7^3 + 40*z_7^2 + 1028*z_7 + 378)*b - 1973*z_7^5 + 4326*z_7^4 - 1943*z_7^3 + 2428*z_7^2 - 1792*z_7 - 1646, 1, 0]), map(E, [(1128*z_7^5 + 66*z_7^4 + 966*z_7^3 + 95*z_7^2 + 78*z_7 + 246)*b - 1086*z_7^5 + 1134*z_7^4 - 943*z_7^3 - 402*z_7^2 - 968*z_7 - 1133, (-2431*z_7^5 + 1308*z_7^4 - 2396*z_7^3 - 1408*z_7^2 - 2058*z_7 - 2436)*b + 6299*z_7^5 + 30*z_7^4 + 4401*z_7^3 + 181*z_7^2 + 327*z_7 + 1973, z_7, 0]), map(E, [(-1062*z_7^5 - 162*z_7^4 - 1033*z_7^3 - 1050*z_7^2 - 882*z_7 - 1128)*b + 2220*z_7^5 + 143*z_7^4 + 684*z_7^3 + 118*z_7^2 - 47*z_7 + 1086, (3739*z_7^5 + 35*z_7^4 + 1023*z_7^3 + 373*z_7^2 - 5*z_7 + 2431)*b - 6269*z_7^5 - 1898*z_7^4 - 6118*z_7^3 - 5972*z_7^2 - 4326*z_7 - 6299, z_7^2, 0]), map(E, [(900*z_7^5 + 29*z_7^4 + 12*z_7^3 + 180*z_7^2 - 66*z_7 + 1062)*b - 2077*z_7^5 - 1536*z_7^4 - 2102*z_7^3 - 2267*z_7^2 - 1134*z_7 - 2220, (-3704*z_7^5 - 2716*z_7^4 - 3366*z_7^3 - 3744*z_7^2 - 1308*z_7 - 3739)*b + 4371*z_7^5 + 151*z_7^4 + 297*z_7^3 + 1943*z_7^2 - 30*z_7 + 6269, z_7^3, 0]), map(E, [(-871*z_7^5 - 888*z_7^4 - 720*z_7^3 - 966*z_7^2 + 162*z_7 - 900)*b + 541*z_7^5 - 25*z_7^4 - 190*z_7^3 + 943*z_7^2 - 143*z_7 + 2077, (988*z_7^5 + 338*z_7^4 - 40*z_7^3 + 2396*z_7^2 - 35*z_7 + 3704)*b - 4220*z_7^5 - 4074*z_7^4 - 2428*z_7^3 - 4401*z_7^2 + 1898*z_7 - 4371, z_7^4, 0]), map(E, [(-17*z_7^5 + 151*z_7^4 - 95*z_7^3 + 1033*z_7^2 - 29*z_7 + 871)*b - 566*z_7^5 - 731*z_7^4 + 402*z_7^3 - 684*z_7^2 + 1536*z_7 - 541, (-650*z_7^5 - 1028*z_7^4 + 1408*z_7^3 - 1023*z_7^2 + 2716*z_7 - 988)*b + 146*z_7^5 + 1792*z_7^4 - 181*z_7^3 + 6118*z_7^2 - 151*z_7 + 4220, z_7^5, 0]), map(E, [(1133*z_7^5 + 47*z_7^4 + 2267*z_7^3 + 190*z_7^2 + 731*z_7 + 165)*b - 738*z_7^5 + 2646*z_7^4 - 540*z_7^3 + 2160*z_7^2 - 453*z_7 - 504, (-1973*z_7^5 + 4326*z_7^4 - 1943*z_7^3 + 2428*z_7^2 - 1792*z_7 - 1646)*b + 7308*z_7^5 + 15*z_7^4 + 11232*z_7^3 + 120*z_7^2 + 3084*z_7 + 1134, b, 0]), map(E, [(-1086*z_7^5 + 1134*z_7^4 - 943*z_7^3 - 402*z_7^2 - 968*z_7 - 1133)*b + 3384*z_7^5 + 198*z_7^4 + 2898*z_7^3 + 285*z_7^2 + 234*z_7 + 738, (6299*z_7^5 + 30*z_7^4 + 4401*z_7^3 + 181*z_7^2 + 327*z_7 + 1973)*b - 7293*z_7^5 + 3924*z_7^4 - 7188*z_7^3 - 4224*z_7^2 - 6174*z_7 - 7308, z_7*b, 0]), map(E, [(2220*z_7^5 + 143*z_7^4 + 684*z_7^3 + 118*z_7^2 - 47*z_7 + 1086)*b - 3186*z_7^5 - 486*z_7^4 - 3099*z_7^3 - 3150*z_7^2 - 2646*z_7 - 3384, (-6269*z_7^5 - 1898*z_7^4 - 6118*z_7^3 - 5972*z_7^2 - 4326*z_7 - 6299)*b + 11217*z_7^5 + 105*z_7^4 + 3069*z_7^3 + 1119*z_7^2 - 15*z_7 + 7293, z_7^2*b, 0]), map(E, [(-2077*z_7^5 - 1536*z_7^4 - 2102*z_7^3 - 2267*z_7^2 - 1134*z_7 - 2220)*b + 2700*z_7^5 + 87*z_7^4 + 36*z_7^3 + 540*z_7^2 - 198*z_7 + 3186, (4371*z_7^5 + 151*z_7^4 + 297*z_7^3 + 1943*z_7^2 - 30*z_7 + 6269)*b - 11112*z_7^5 - 8148*z_7^4 - 10098*z_7^3 - 11232*z_7^2 - 3924*z_7 - 11217, z_7^3*b, 0]), map(E, [(541*z_7^5 - 25*z_7^4 - 190*z_7^3 + 943*z_7^2 - 143*z_7 + 2077)*b - 2613*z_7^5 - 2664*z_7^4 - 2160*z_7^3 - 2898*z_7^2 + 486*z_7 - 2700, (-4220*z_7^5 - 4074*z_7^4 - 2428*z_7^3 - 4401*z_7^2 + 1898*z_7 - 4371)*b + 2964*z_7^5 + 1014*z_7^4 - 120*z_7^3 + 7188*z_7^2 - 105*z_7 + 11112, z_7^4*b, 0]), map(E, [(-566*z_7^5 - 731*z_7^4 + 402*z_7^3 - 684*z_7^2 + 1536*z_7 - 541)*b - 51*z_7^5 + 453*z_7^4 - 285*z_7^3 + 3099*z_7^2 - 87*z_7 + 2613, (146*z_7^5 + 1792*z_7^4 - 181*z_7^3 + 6118*z_7^2 - 151*z_7 + 4220)*b - 1950*z_7^5 - 3084*z_7^4 + 4224*z_7^3 - 3069*z_7^2 + 8148*z_7 - 2964, z_7^5*b, 0]), map(E, [(2724*z_7^5 + 1597*z_7^4 + 5432*z_7^3 + 1552*z_7^2 + 1639*z_7 + 202)*b - 422*z_7^5 + 6539*z_7^4 + 1902*z_7^3 + 5346*z_7^2 - 591*z_7 - 1425, (2190*z_7^5 + 887*z_7^4 + 3556*z_7^3 + 760*z_7^2 + 849*z_7 + 206)*b - 840*z_7^5 + 4371*z_7^4 + 324*z_7^3 + 2580*z_7^2 - 1065*z_7 - 1507, 1, 1]), map(E, [(-1127*z_7^5 + 2708*z_7^4 - 1172*z_7^3 - 1085*z_7^2 - 2522*z_7 - 2724)*b + 6961*z_7^5 + 2324*z_7^4 + 5768*z_7^3 - 169*z_7^2 - 1003*z_7 + 422, (-1303*z_7^5 + 1366*z_7^4 - 1430*z_7^3 - 1341*z_7^2 - 1984*z_7 - 2190)*b + 5211*z_7^5 + 1164*z_7^4 + 3420*z_7^3 - 225*z_7^2 - 667*z_7 + 840, z_7, z_7]), map(E, [(3835*z_7^5 - 45*z_7^4 + 42*z_7^3 - 1395*z_7^2 - 1597*z_7 + 1127)*b - 4637*z_7^5 - 1193*z_7^4 - 7130*z_7^3 - 7964*z_7^2 - 6539*z_7 - 6961, (2669*z_7^5 - 127*z_7^4 - 38*z_7^3 - 681*z_7^2 - 887*z_7 + 1303)*b - 4047*z_7^5 - 1791*z_7^4 - 5436*z_7^3 - 5878*z_7^2 - 4371*z_7 - 5211, z_7^2, z_7^2]), map(E, [(-3880*z_7^5 - 3793*z_7^4 - 5230*z_7^3 - 5432*z_7^2 - 2708*z_7 - 3835)*b + 3444*z_7^5 - 2493*z_7^4 - 3327*z_7^3 - 1902*z_7^2 - 2324*z_7 + 4637, (-2796*z_7^5 - 2707*z_7^4 - 3350*z_7^3 - 3556*z_7^2 - 1366*z_7 - 2669)*b + 2256*z_7^5 - 1389*z_7^4 - 1831*z_7^3 - 324*z_7^2 - 1164*z_7 + 4047, z_7^3, z_7^3]), map(E, [(87*z_7^5 - 1350*z_7^4 - 1552*z_7^3 + 1172*z_7^2 + 45*z_7 + 3880)*b - 5937*z_7^5 - 6771*z_7^4 - 5346*z_7^3 - 5768*z_7^2 + 1193*z_7 - 3444, (89*z_7^5 - 554*z_7^4 - 760*z_7^3 + 1430*z_7^2 + 127*z_7 + 2796)*b - 3645*z_7^5 - 4087*z_7^4 - 2580*z_7^3 - 3420*z_7^2 + 1791*z_7 - 2256, z_7^4, z_7^4]), map(E, [(-1437*z_7^5 - 1639*z_7^4 + 1085*z_7^3 - 42*z_7^2 + 3793*z_7 - 87)*b - 834*z_7^5 + 591*z_7^4 + 169*z_7^3 + 7130*z_7^2 + 2493*z_7 + 5937, (-643*z_7^5 - 849*z_7^4 + 1341*z_7^3 + 38*z_7^2 + 2707*z_7 - 89)*b - 442*z_7^5 + 1065*z_7^4 + 225*z_7^3 + 5436*z_7^2 + 1389*z_7 + 3645, z_7^5, z_7^5]), map(E, [(1151*z_7^5 + 4068*z_7^4 + 3667*z_7^3 + 3449*z_7^2 + 524*z_7 - 1223//2)*b + 3875*z_7^5 + 5665*z_7^4 + 9099*z_7^3 + 5001*z_7^2 + 2163*z_7 - 819//2, (675*z_7^5 + 2629*z_7^4 + 1940*z_7^3 + 1670*z_7^2 - 108*z_7 - 1301//2)*b + 2865*z_7^5 + 3516*z_7^4 + 5496*z_7^3 + 2430*z_7^2 + 741*z_7 - 889//2, 1//2*b + 1//2, 1//2*b + 1//2]), map(E, [(2917*z_7^5 + 2516*z_7^4 + 2298*z_7^3 - 627*z_7^2 - 3525//2*z_7 - 1151)*b + 1790*z_7^5 + 5224*z_7^4 + 1126*z_7^3 - 1712*z_7^2 - 8569//2*z_7 - 3875, (1954*z_7^5 + 1265*z_7^4 + 995*z_7^3 - 783*z_7^2 - 2651//2*z_7 - 675)*b + 651*z_7^5 + 2631*z_7^4 - 435*z_7^3 - 2124*z_7^2 - 6619//2*z_7 - 2865, 1//2*z_7*b + 1//2*z_7, 1//2*z_7*b + 1//2*z_7]), map(E, [(-401*z_7^5 - 619*z_7^4 - 3544*z_7^3 - 9359//2*z_7^2 - 4068*z_7 - 2917)*b + 3434*z_7^5 - 664*z_7^4 - 3502*z_7^3 - 12149//2*z_7^2 - 5665*z_7 - 1790, (-689*z_7^5 - 959*z_7^4 - 2737*z_7^3 - 6559//2*z_7^2 - 2629*z_7 - 1954)*b + 1980*z_7^5 - 1086*z_7^4 - 2775*z_7^3 - 7921//2*z_7^2 - 3516*z_7 - 651, 1//2*z_7^2*b + 1//2*z_7^2, 1//2*z_7^2*b + 1//2*z_7^2]), map(E, [(-218*z_7^5 - 3143*z_7^4 - 8557//2*z_7^3 - 3667*z_7^2 - 2516*z_7 + 401)*b - 4098*z_7^5 - 6936*z_7^4 - 19017//2*z_7^3 - 9099*z_7^2 - 5224*z_7 - 3434, (-270*z_7^5 - 2048*z_7^4 - 5181//2*z_7^3 - 1940*z_7^2 - 1265*z_7 + 689)*b - 3066*z_7^5 - 4755*z_7^4 - 11881//2*z_7^3 - 5496*z_7^2 - 2631*z_7 - 1980, 1//2*z_7^3*b + 1//2*z_7^3, 1//2*z_7^3*b + 1//2*z_7^3]), map(E, [(-2925*z_7^5 - 8121//2*z_7^4 - 3449*z_7^3 - 2298*z_7^2 + 619*z_7 + 218)*b - 2838*z_7^5 - 10821//2*z_7^4 - 5001*z_7^3 - 1126*z_7^2 + 664*z_7 + 4098, (-1778*z_7^5 - 4641//2*z_7^4 - 1670*z_7^3 - 995*z_7^2 + 959*z_7 + 270)*b - 1689*z_7^5 - 5749//2*z_7^4 - 2430*z_7^3 + 435*z_7^2 + 1086*z_7 + 3066, 1//2*z_7^4*b + 1//2*z_7^4, 1//2*z_7^4*b + 1//2*z_7^4]), map(E, [(-2271//2*z_7^5 - 524*z_7^4 + 627*z_7^3 + 3544*z_7^2 + 3143*z_7 + 2925)*b - 5145//2*z_7^5 - 2163*z_7^4 + 1712*z_7^3 + 3502*z_7^2 + 6936*z_7 + 2838, (-1085//2*z_7^5 + 108*z_7^4 + 783*z_7^3 + 2737*z_7^2 + 2048*z_7 + 1778)*b - 2371//2*z_7^5 - 741*z_7^4 + 2124*z_7^3 + 2775*z_7^2 + 4755*z_7 + 1689, 1//2*z_7^5*b + 1//2*z_7^5, 1//2*z_7^5*b + 1//2*z_7^5])]
  
  L = hermitian_lattice(E, generators = gene, gram_ambient_space = D)
  gens, def, P0 = @inferred Hecke.genus_generators(L)
  @test length(gens) == 0
  @test !def
  @test P0 == 1*base_ring(L)
end
