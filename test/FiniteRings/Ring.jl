@testset "Finite rings" begin
  R = finite_ring([1], [zero_matrix(ZZ, 1, 1)])

  @test order(R) == 1
end
