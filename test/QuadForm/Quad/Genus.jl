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


  G = Hecke.local_genera_quadratic(K, p2, rank = 2, det_val = 4)
  for i in 1:10
    G1 = rand(G)
    G2 = rand(G)
    L1 = representative(G1)
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
  end

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
  @test sprint(show, jordan_decomposition(L, p)) isa String
  @test sprint(show, genus(L, p)) isa String
end


