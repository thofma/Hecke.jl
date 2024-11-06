@testset "Genera" begin

  # TODO: move the remaining examples in the corresponding files in ~/test/QuadForm/Quad
  # Representatives

  Qx, x = QQ["x"]
  K, a = number_field(x^2 - 15)
  gens = [[a-1, 2*a-12, 0], [-471//70*a+881//14, 12*a-471, 1//70*a+39//14], [-7367*a+33891, 38904*a-212340, -194*a+1164], [2858191//5*a-1701731, -3700688*a+8438412, 103014//5*a-40352]]
  D = matrix(K, 3, 3, [38*a+150, 0, 0, 0, 2*a+8, 0, 0, 0, 302*a+1170])
  L = @inferred quadratic_lattice(K, gens, gram = D)
  @test length(@inferred genus_representatives(L)) == 1

  K, a = number_field(x - 1)
  gens = [[-768, -1024, 0], [-768, -928, 160], [256, 320, -64]]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2])
  L = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L)) == 2

  K, a = number_field(x - 1)
  gens = [[-128, -1024, 0], [0, -2016, -32], [0, -512, 0]]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2])
  L = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L)) == 2

  K, a = number_field(x^2 - 2)
  gens = [[32*a-48, 32*a-64, 0], [0, 208*a+272, -24], [0, 512*a+768, -40*a-8]]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2])
  L = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L)) == 2

  K, a = number_field(x^3-x^2-2*x+1)
  gens = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 1//2, 0, 1//2]]
  D = matrix(K, 4, 4, [1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2])
  L = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L)) == 2

  # Addition of genera

  Qx, x = polynomial_ring(QQ, "x", cached = false)
  f = x - 1;
  K, a = number_field(f)
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -36]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 1, 0], [0, 1, 0], [1//2, 1//2, 1//4], [1//2, 1//2, 1//4]]
  L = quadratic_lattice(K, gens, gram = D)
  p = prime_decomposition(maximal_order(K), 3)[1][1]
  fl, LL = @inferred Hecke.is_maximal_integral(L, p)
  @test !fl
  fl, _ = Hecke.is_maximal_integral(LL, p)
  @test fl

  Qx, x = polynomial_ring(QQ, "x", cached = false)
  f = x - 1;
  K, a = number_field(f)
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -36]);
  V = quadratic_space(K, D)

  W = quadratic_space(K, diagonal_matrix([K(2), K(-36)]))

  @test @inferred Hecke.is_represented_by(W, V)

  W = quadratic_space(K, diagonal_matrix([K(2), K(36)]))

  @test @inferred !Hecke.is_represented_by(W, V)

end

