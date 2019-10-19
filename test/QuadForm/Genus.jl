@testset "Genera" begin
  K, a = MaximalRealSubfield(8, "a")
  Kt, t = PolynomialRing(K, "t")
  L, b = number_field(t^2 - gen(K) * t + 1)
  p = prime_decomposition(maximal_order(K), 2)[1][1]
  G = Hecke._local_genera(L, p, 4, 2, 4, true)
  for i in 1:length(G)
    @test representative(G[i]) in G[i]
  end
  
  p = prime_decomposition(maximal_order(K), 17)[1][1]
  G = Hecke._local_genera(L, p, 4, 2, 4, false)
  for i in 1:length(G)
    @test representative(G[i]) in G[i]
  end
end
