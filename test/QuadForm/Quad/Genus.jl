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
end

@testset "Genus representatives" begin
  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  f = x-1;
  K, a = number_field(f)
  D = matrix(K, 3, 3, [-717210130, 0, 0, 0, -55, 0, 0, 0, -1173298395869600]);
  gens = [[1, 0, 0], [1, 0, 0], [4//5, 2//5, 0], [4//5, 2//5, 0], [1493459//5517001, 0, 1//15778622860], [1493459//5517001, 0, 1//15778622860]]
  L = quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  @test length(genus_representatives(L)) == 6

  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  f = x-1;
  K, a = number_field(f)
  D = matrix(K, 3, 3, [-34, 0, 0, 0, -17, 0, 0, 0, -17192032]);
  gens = [[26, 0, 0], [234, 0, 0], [177//17, 2//17, 0], [177//17, 2//17, 0], [27//2, 0, 1//1768], [27//2, 0, 1//1768]]
  L = quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  @test length(genus_representatives(L)) == 93

  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  f = x-1;
  K, a = number_field(f)
  D = matrix(K, 3, 3, [-98, 0, 0, 0, -2, 0, 0, 0, -5829824]);
  gens = [[8//7, 0, 0], [8//7, 0, 0], [5//14, 13//2, 0], [45//14, 117//2, 0], [29//28, 3//4, 1//1456], [29//28, 3//4, 1//1456]]
  L = quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  @test length(genus_representatives(L)) == 114

  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  f = x^2-2;
  K, a = number_field(f)
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -7436]);
  gens = [[13, 0, 0], [156*a+143, 0, 0], [3//2*a+5, 1, 0], [3//2*a+5, 1, 0], [21//2*a, 0, 1//26], [21//2*a, 0, 1//26]]
  L = quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  @test length(genus_representatives(L)) == 1


end
