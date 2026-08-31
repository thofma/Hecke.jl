@testset "Chain complexes" begin
  G = abelian_group([4])
  f = hom(G, G, [2*G[1]])
  z = zero_map(G, G)
  C = chain_complex(f, z)

  H = Hecke.homology(C)
  H1 = Hecke.homology(C, 1)
  @test length(H) == 1
  @test is_isomorphic(H1, H[1])
  @test order(H1) == 2

  M = Hecke.ComplexOfMorphismsMap(C, C, Dict{Int, Hecke.Map}(1 => f))
  @test M[1] === f
  @test_throws KeyError M[2]

  M.fill = (M, i) -> z
  @test M[2] === z
end
