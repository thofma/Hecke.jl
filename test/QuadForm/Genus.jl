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
  l =  [[(0, 3, 1, 0), (4, 1, 1, 2)],
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
  Gs = map(x -> genus(HermLat, L, p, x), l)
  myG = local_genera_hermitian(L, p, 4, 2, 4)
  @test length(Gs) == length(myG)
  @test all(x -> x in Gs, myG)
  @test all(x -> x in myG, Gs)

end
