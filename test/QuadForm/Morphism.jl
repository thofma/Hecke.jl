@testset "Morphism" begin
  L = Zlattice(gram = zero_matrix(ZZ, 0, 0))
  @test_throws ArgumentError shortest_vectors(L)
  @test_throws ArgumentError shortest_vectors(L, Vector{Int})
  @test_throws ArgumentError minimum(L)
  @test_throws ArgumentError kissing_number(L)
  @test (@inferred short_vectors(L, 1)) == []
  @test (@inferred short_vectors(L, 1, 2)) == []

  G = ZZ[2 1 -1 -1 -1 1 1 -1 0 0 0 0 0 0 0 0; 1 2 -1 -1 -1 1 1 -1 0 0 0 0 0 0 0 0; -1 -1 2 0 1 0 -1 1 0 0 0 0 0 0 0 0; -1 -1 0 2 1 -1 0 0 0 0 0 0 0 0 0 0; -1 -1 1 1 2 0 -1 0 0 0 0 0 0 0 0 0; 1 1 0 -1 0 2 0 -1 0 0 0 0 0 0 0 0; 1 1 -1 0 -1 0 2 -1 0 0 0 0 0 0 0 0; -1 -1 1 0 0 -1 -1 2 0 0 0 0 0 0 0 0; 0 0 0 0 0 0 0 0 2 1 1 0 1 1 1 0; 0 0 0 0 0 0 0 0 1 2 1 0 1 1 0 0; 0 0 0 0 0 0 0 0 1 1 2 0 0 0 1 0; 0 0 0 0 0 0 0 0 0 0 0 2 1 0 -1 0; 0 0 0 0 0 0 0 0 1 1 0 1 4 1 0 1; 0 0 0 0 0 0 0 0 1 1 0 0 1 4 0 0; 0 0 0 0 0 0 0 0 1 0 1 -1 0 0 8 1; 0 0 0 0 0 0 0 0 0 0 0 0 1 0 1 18]
  L = Zlattice(gram=G)
  @test length(shortest_vectors(L)) == 127
end
