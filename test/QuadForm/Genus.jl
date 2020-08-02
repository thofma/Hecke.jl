@testset "Genera" begin
  K, a = MaximalRealSubfield(8, "a")
  Kt, t = PolynomialRing(K, "t")
  L, b = number_field(t^2 - gen(K) * t + 1)
  p = prime_decomposition(maximal_order(K), 2)[1][1]
  G = local_genera_hermitian(L, p, 4, 2, 4, true)
  @test length(G) == 15
  for i in 1:length(G)
    @test rank(G[i]) == 4
    @test representative(G[i]) in G[i]
  end

  GG = G[1]
  u = @inferred uniformizer(GG)
  @assert parent(u) == K
  
  p = prime_decomposition(maximal_order(K), 17)[1][1]
  G = local_genera_hermitian(L, p, 5, 5, 5)
  @test length(G) == 7
  for i in 1:length(G)
    @test rank(G[i]) == 5
    @test representative(G[i]) in G[i]
  end
  
  K, a = MaximalRealSubfield(8, "a")
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
  myG = local_genera_hermitian(L, p, 4, 2, 4)
  @test length(Gs) == length(myG)
  @test all(x -> x in Gs, myG)
  @test all(x -> x in myG, Gs)

  # Representatives
  
  Qx, x = FlintQQ["x"]
  K, a = NumberField(x - 1, "a")
  Kt, t = K["t"]
  E, b = NumberField(t^2 + 1, "b")
  p = prime_decomposition(maximal_order(K), 2)[1][1]
  G = genus(HermLat, E, p, [(0, 3, -1, 0)])
  L = representative(G)
 @test length(Hecke.genus_representatives(L)) == 1

  K, a = NumberField(x^2 - 15)
  gens = [[a-1, 2*a-12, 0], [-471//70*a+881//14, 12*a-471, 1//70*a+39//14], [-7367*a+33891, 38904*a-212340, -194*a+1164], [2858191//5*a-1701731, -3700688*a+8438412, 103014//5*a-40352]]
  D = matrix(K, 3, 3, [38*a+150, 0, 0, 0, 2*a+8, 0, 0, 0, 302*a+1170])
  L = quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  @test length(genus_representatives(L)) == 1

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
end
