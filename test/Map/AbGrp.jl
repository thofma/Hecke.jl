@testset "Test composition order" begin
  G = abelian_group([2, 2, 2])
  f = hom(G, G, [G[2], G[1], G[3]])
  g = hom(G, G, [G[1], G[3], G[2]])
  h = (f * g)
  @test all(h(x) == g(f(x)) for x in gens(G))
end
