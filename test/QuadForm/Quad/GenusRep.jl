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

  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  f = x - 1
  K, a = number_field(f)
  M = matrix(QQ, 2, 2, [47, 80, 80, 560])
  w = Int[]
  for i in 1:10
    M[2, 2] = 560 + i
    V = quadratic_space(K, M)
    L = lattice(V, identity_matrix(K, 2))
    g = length(Hecke._genus_representatives_binary_quadratic_definite(L))
    push!(w, g)
  end
  @test w == Int[37, 16, 19, 11, 6, 3, 52, 7, 13, 21]

  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  f = x^2 - 2;
  K, a = number_field(f)
  D = matrix(K, 2, 2, [15, 2, 2, 32]);
  gens = [[1, 0], [1, 0], [0, 1], [0, 1]]
  L = quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  @test length(genus_representatives(L)) == 6
end
