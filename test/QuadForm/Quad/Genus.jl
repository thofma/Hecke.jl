@testset "Genus" begin
  Qx, x = FlintQQ["x"]
  K, a = NumberField(x - 1, "a", cached = false)
  OK = maximal_order(K)
  rlp = real_places(K)
  sig = Dict(rlp[1] => 2)

  p2 = prime_decomposition(OK, 2)[1][1]
  p3 = prime_decomposition(OK, 3)[1][1]
  p5 = prime_decomposition(OK, 5)[1][1]

  @test length(Hecke.local_genera_quadratic(K, p2, rank = 2, det_val = 0)) == 8
  @test length(Hecke.local_genera_quadratic(K, p2, rank = 2, det_val = 1)) == 8
  @test length(Hecke.local_genera_quadratic(K, p2, rank = 2, det_val = 2)) == 16
  @test length(Hecke.local_genera_quadratic(K, p2, rank = 2, det_val = 3)) == 24
  @test length(Hecke.local_genera_quadratic(K, p2, rank = 2, det_val = 4)) == 32

  @test length(Hecke.local_genera_quadratic(K, p3, rank = 5, det_val = 0)) == 2
  @test length(Hecke.local_genera_quadratic(K, p3, rank = 5, det_val = 1)) == 4
  @test length(Hecke.local_genera_quadratic(K, p3, rank = 5, det_val = 2)) == 8
  @test length(Hecke.local_genera_quadratic(K, p3, rank = 5, det_val = 3)) == 16
  @test length(Hecke.local_genera_quadratic(K, p3, rank = 5, det_val = 4)) == 28
  @test length(Hecke.local_genera_quadratic(K, p3, rank = 5, det_val = 5)) == 46
  @test length(Hecke.local_genera_quadratic(K, p3, rank = 5, det_val = 6)) == 72

  @test length(Hecke.local_genera_quadratic(K, p5, rank = 4, det_val = 2)) == 8
  @test length(Hecke.local_genera_quadratic(K, p5, rank = 4, det_val = 1)) == 4
  @test length(Hecke.local_genera_quadratic(K, p5, rank = 2, det_val = 0)) == 2
  @test length(Hecke.local_genera_quadratic(K, p5, rank = 2, det_val = 1)) == 4

  @test length(Hecke.genera_quadratic(K, rank = 2, signatures = sig, det = 5^2 * 8 * 9 * OK)) == 27
  @test length(Hecke.genera_quadratic(K, rank = 2, signatures = sig, det = 5 * 7 * 8 * 9 * OK)) == 36
  @test length(Hecke.genera_quadratic(K, rank = 2, signatures = sig, det = 2^5 * OK)) == 5
  @test length(Hecke.genera_quadratic(K, rank = 2, signatures = sig, det = 11 * 13^2 * OK)) == 6

  G1 = Hecke.local_genera_quadratic(K, p3, rank = 3, det_val = 1)[4]
  G1a = Hecke.local_genera_quadratic(K, p3, rank = 3, det_val = 1)[4]
  G1a.uniformizer = 4*G1.uniformizer
  @test G1 == G1a
  @test G1+G1a == G1+G1
  G2 = Hecke.local_genera_quadratic(K, p3, rank = 3, det_val = 1)[4]
  G2.uniformizer = -G2.uniformizer
  @test G2 != G1
  @test G2 != G1a

  # test representative and orthogonal_sum

  G = Hecke.local_genera_quadratic(K, p2, rank = 3, det_val = 4)
  for i in 1:10
    G1 = rand(G)
    G2 = rand(G)
    L1 = representative(G1)
    @test L1 in G1
    L2 = representative(G2)
    G3 = @inferred orthogonal_sum(G1, G2)
    L3, = orthogonal_sum(L1, L2)
    @test G3 == genus(L3, p2)
    @test genus(L1,p2) + genus(QuadLat,p2) == G1
  end
  @test sprint(show, G[1]) isa String
  @test sprint(show, "text/plain", G[1]) isa String

  G = Hecke.local_genera_quadratic(K, p2, rank = 3, det_val = 1)
  for i in 1:10
    G1 = rand(G)
    G2 = rand(G)
    L1 = representative(G1)
    L2 = representative(G2)
    G3 = @inferred orthogonal_sum(G1, G2)
    L3, = orthogonal_sum(L1, L2)
    @test G3 == genus(L3, p2)
  end

  G = Hecke.local_genera_quadratic(K, p2, rank = 5, det_val = 1)
  for i in 1:10
    G1 = rand(G)
    G2 = rand(G)
    L1 = representative(G1)
    @test L1 in G1
    L2 = representative(G2)
    G3 = @inferred orthogonal_sum(G1, G2)
    L3, = orthogonal_sum(L1, L2)
    @test G3 == genus(L3, p2)
  end

  G = Hecke.local_genera_quadratic(K, p3, rank = 5, det_val = 5)
  for i in 1:10
    G1 = rand(G)
    G2 = rand(G)
    L1 = representative(G1)
    L2 = representative(G2)
    G3 = @inferred orthogonal_sum(G1, G2)
    L3, = orthogonal_sum(L1, L2)
    @test G3 == genus(L3, p3)
    @test genus(L1,p3) + genus(QuadLat,p3) == G1
  end
  q = genus(QuadLat,p2)
  @test det(q) == 1
  @test rank(q) == 0
  @test hasse_invariant(q) == 1

  @test sprint(show, G[1]) isa String
  @test sprint(show, "text/plain", G[1]) isa String

  G = Hecke.local_genera_quadratic(K, p5, rank = 2, det_val = 1)
  for i in 1:10
    G1 = rand(G)
    G2 = rand(G)
    L1 = representative(G1)
    L2 = representative(G2)
    G3 = @inferred orthogonal_sum(G1, G2)
    L3, = orthogonal_sum(L1, L2)
    @test G3 == genus(L3, p5)
  end

  G = Hecke.genera_quadratic(K, rank = 3, signatures = sig, det = 2 * 9 * OK)
  for i in 1:10
    G1 = rand(G)
    G2 = rand(G)
    L1 = representative(G1)
    L2 = representative(G2)
    G3 = @inferred orthogonal_sum(G1, G2)
    L3, = orthogonal_sum(L1, L2)
    @test L3 in G3
  end

  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  f = x - 1;
  K, a = number_field(f)
  D = matrix(K, 3, 3, [30, -15, 0, -15, 30, -15, 0, -15, 30]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 1, 0], [0, 1, 0], [5//6, 2//3, 1//6], [5//6, 2//3, 1//6]]
  L = quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  p = prime_decomposition(maximal_order(K), 5)[1][1]
  fl, LL = Hecke.ismaximal_integral(L, p)
  @test !fl

  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  f = x^2 - 2;
  K, a = number_field(f)
  p = prime_ideals_over(maximal_order(K),2)[1]
  D = matrix(K, 3, 3, [1//64, 0, 0, 0, 1//64, 0, 0, 0, 1//64]);
  gens = [[64, 0, 0], [248*a + 88, 0, 0], [32, 32, 0], [100*a + 136, 100*a + 136, 0], [32, 0, 32], [20*a + 136, 0, 20*a + 136]]
  L = quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  @test sprint(show, Hecke.JorDec(L, p)) isa String
  @test sprint(show,"text/plain" , Hecke.JorDec(L, p)) isa String
  @test sprint(show, genus(L, p)) isa String
  @test sprint(show, "text/plain", genus(L, p)) isa String

  R, x = PolynomialRing(QQ,:x)
  F,a = number_field(x^2-2,:a)
  OF = maximal_order(F)
  pl = real_places(F)
  p = prime_ideals_over(OF, 2)[1]
  p3 = prime_ideals_over(OF, 3)[1]

  # Test the computation of jordan decomposition
  G = Hecke.local_genera_quadratic(F, p, rank = 3, det_val = 2)
  for g in G
    g1 = genus(QuadLat, p, g.ranks, g.scales, g.weights, g.dets, g.normgens, g.witt)
    representative(g1) in G  # computes jordan decompositions
  end
  G = Hecke.local_genera_quadratic(F, p3, rank = 3, det_val = 2)
  for g in G
    g1 = genus(QuadLat, p3, g.uniformizer, g.ranks, g.scales, g.detclasses)
    representative(g1) in G  # computes jordan decompositions
  end

  sig = Dict([(pl[1],0),(pl[2],0)])
  for d in 1:(long_test ? 10 : 3)
    for G in Hecke.genera_quadratic(F,rank=2,det=d*OF,signatures=sig)
      @test representative(G) in G
    end
  end
  sig = Dict([(pl[1],3),(pl[2],2)])
  for d in 1:(long_test ? 10 : 3)
    for G in Hecke.genera_quadratic(F,rank=4,det=d*OF,signatures=sig)
      @test representative(G) in G
    end
  end

  R, x = PolynomialRing(QQ,:x)
  F,a = number_field(x^3+x+1,:a)
  OF = maximal_order(F)
  pl = real_places(F)
  sig = Dict([(pl[1],0)])
  for d in 1:(long_test ? 10 : 3)
    for G in Hecke.genera_quadratic(F,rank=2,det=d*OF,signatures=sig)
      @test representative(G) in G
    end
  end
  sig = Dict([(pl[1],3)])
  for d in 1:(long_test ? 10 : 3)
    for G in Hecke.genera_quadratic(F,rank=3,det=d*OF,signatures=sig)
      @test representative(G) in G
    end
  end
end
