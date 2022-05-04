@testset "Morphism" begin
  L = Zlattice(gram = zero_matrix(ZZ, 0, 0))
  @test_throws ArgumentError shortest_vectors(L)
  @test_throws ArgumentError shortest_vectors(L, Vector{Int})
  @test_throws ArgumentError minimum(L)
  @test_throws ArgumentError kissing_number(L)
  @test (@inferred short_vectors(L, 1)) == []
  @test (@inferred short_vectors(L, 1, 2)) == []
end
