@testset "Lattices" begin
  # Smoke test for genus symbol
  Qx, x = PolynomialRing(FlintQQ, "x")
  K, a = NumberField(x^2 - 2, "a")
  L = quadratic_lattice(K, identity_matrix(K, 10), gram_ambient_space = 35*identity_matrix(K, 10)) 
  P = prime_decomposition(maximal_order(K), 5)[1][1]
  @test Hecke.genus_symbol(L, P).data == [(10, 1, 1)]

  P = prime_decomposition(maximal_order(K), 2)[1][1]
  GS = Hecke.genus_symbol(L, P)
  @test GS.data[1] == [10]
  @test GS.data[2] == [0]
  @test GS.data[3] == [2]
  @test GS.data[4] == [35]
  @test GS.data[5] == []
end
