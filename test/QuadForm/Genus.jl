@testset "Genera" begin
  K, a = CyclotomicRealSubfield(8, "a")
  Kt, t = PolynomialRing(K, "t")
  L, b = number_field(t^2 - gen(K) * t + 1)
  p = prime_decomposition(maximal_order(K), 2)[1][1]
  G = @inferred local_genera_hermitian(L, p, 4, 2, 4, true)
  @test length(G) == 15
  for i in 1:length(G)
    @test rank(G[i]) == 4
    @test (@inferred representative(G[i])) in G[i]
  end

  GG = G[1]
  u = @inferred uniformizer(GG)
  @assert parent(u) == K

  p = prime_decomposition(maximal_order(K), 17)[1][1]
  G = @inferred local_genera_hermitian(L, p, 5, 5, 5)
  @test length(G) == 7
  for i in 1:length(G)
    @test rank(G[i]) == 5
    @test (@inferred representative(G[i])) in G[i]
  end

  K, a = CyclotomicRealSubfield(8, "a")
  Kt, t = K["t"]
  L, b = number_field(t^2 - gen(K) * t + 1)
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
  # The compiler does not like the following:
  # Gs = map(x -> genus(HermLat, L, p, x), l)
  Gs = Hecke.LocalGenusHerm{typeof(L), typeof(p)}[ genus(HermLat, L, p, x) for x in l ]
  myG = @inferred local_genera_hermitian(L, p, 4, 2, 4)
  @test length(Gs) == length(myG)
  @test all(x -> x in Gs, myG)
  @test all(x -> x in myG, Gs)

  K, a = CyclotomicRealSubfield(8, "a")
  Kt, t = K["t"]
  L, b = number_field(t^2 - gen(K) * t + 1)
  rlp = real_places(K)
  G = @inferred genera_hermitian(L, 3, Dict(rlp[1] => 1, rlp[2] => 1), 100 * maximal_order(L))
  for i in 1:10
    g1 = rand(G)
    g2 = rand(G)
    M, = @inferred orthogonal_sum(representative(g1), representative(g2))
    @test M in (g1 + g2)
  end

  # Representatives

  Qx, x = FlintQQ["x"]
  K, a = NumberField(x - 1, "a")
  Kt, t = K["t"]
  E, b = NumberField(t^2 + 1, "b")
  p = prime_decomposition(maximal_order(K), 2)[1][1]
  G = genus(HermLat, E, p, [(0, 3, -1, 0)])
  L = @inferred representative(G)
  @test length(@inferred Hecke.genus_representatives(L)) == 1

  K, a = NumberField(x^2 - 15)
  gens = [[a-1, 2*a-12, 0], [-471//70*a+881//14, 12*a-471, 1//70*a+39//14], [-7367*a+33891, 38904*a-212340, -194*a+1164], [2858191//5*a-1701731, -3700688*a+8438412, 103014//5*a-40352]]
  D = matrix(K, 3, 3, [38*a+150, 0, 0, 0, 2*a+8, 0, 0, 0, 302*a+1170])
  L = @inferred quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  @test length(@inferred genus_representatives(L)) == 1

  K, a = NumberField(x - 1)
  gens = [[-768, -1024, 0], [-768, -928, 160], [256, 320, -64]]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2])
  L = quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  @test length(genus_representatives(L)) == 2

  K, a = NumberField(x - 1)
  gens = [[-128, -1024, 0], [0, -2016, -32], [0, -512, 0]]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2])
  L = quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  @test length(genus_representatives(L)) == 2

  K, a = NumberField(x^2 - 2)
  gens = [[32*a-48, 32*a-64, 0], [0, 208*a+272, -24], [0, 512*a+768, -40*a-8]]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 2, 0, 0, 0, 2])
  L = quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  @test length(genus_representatives(L)) == 2

  K, a = NumberField(x^3-x^2-2*x+1)
  gens = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 1//2, 0, 1//2]]
  D = matrix(K, 4, 4, [1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2])
  L = quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  @test length(genus_representatives(L)) == 2

  K, a = NumberField(x - 1)
  OK = maximal_order(K)
  p = prime_decomposition(OK, 2)[1][1]
  @test length(Hecke.local_genera_quadratic(K, p, rank = 2, det_val = 1)) == 8

  # Addition of genera

  K, a = CyclotomicRealSubfield(8, "a")
  Kt, t = PolynomialRing(K, "t")
  L, b = number_field(t^2 - gen(K) * t + 1)

  p = prime_decomposition(maximal_order(K), 2)[1][1]
  G = local_genera_hermitian(L, p, 4, 2, 4, true)
  for i in 1:10
    g1 = rand(G)
    g2 = rand(G)
    g3 = @inferred orthogonal_sum(g1, g2)
    @test genus(representative(g3), p) == genus(orthogonal_sum(representative(g1), representative(g2))[1], p)
  end

  p = prime_decomposition(maximal_order(K), 3)[1][1]
  G = local_genera_hermitian(L, p, 4, 2, 4, true)
  for i in 1:10
    g1 = rand(G)
    g2 = rand(G)
    g3 = @inferred orthogonal_sum(g1, g2)
    @test genus(representative(g3), p) == genus(orthogonal_sum(representative(g1), representative(g2))[1], p)
  end

  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  f = x - 1;
  K, a = number_field(f)
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -36]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 1, 0], [0, 1, 0], [1//2, 1//2, 1//4], [1//2, 1//2, 1//4]]
  L = quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  p = prime_decomposition(maximal_order(K), 3)[1][1]
  fl, LL = @inferred Hecke.ismaximal_integral(L, p)
  @test !fl
  fl, _ = Hecke.ismaximal_integral(LL, p)
  @test fl

  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  f = x - 1;
  K, a = number_field(f)
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -36]);
  V = quadratic_space(K, D)

  W = quadratic_space(K, diagonal_matrix([K(2), K(-36)]))

  @test @inferred Hecke.isrepresented_by(W, V)

  W = quadratic_space(K, diagonal_matrix([K(2), K(36)]))

  @test @inferred !Hecke.isrepresented_by(W, V)

  Qx, x = PolynomialRing(FlintQQ, "x")
  f = x^2-3
  K, a = NumberField(f, "a", cached = false)
  Kt, t = PolynomialRing(K, "t")
  g = t^2+(1)
  E, b = NumberField(g, "b", cached = false)
  D = matrix(E, 3, 3, [(a), 0, 0, 0, (2 * a), 0, 0, 0, (a + 5)])
  V = hermitian_space(E, D)
  DD = matrix(E, 2, 2, [a + 3, 0, 0, (a + 2)])
  W = hermitian_space(E, DD)
  @test @inferred Hecke.isrepresented_by(W, V)
  @test @inferred Hecke.isrepresented_by(V, V)
  DD = E(a) * identity_matrix(E, 5)
  W = hermitian_space(E, DD)
  @test @inferred Hecke.isrepresented_by(V, W)

  # they are not isometric at some dyadic prime ideal:
  DD = identity_matrix(E, 4)
  W = hermitian_space(E, DD)
  @test !(@inferred Hecke.isrepresented_by(W, V))
end
