@testset "FiniteRings/Ideal" begin
  R, = finite_ring(GF(2)[small_group(8, 5)])
  @test_throws UndefKeywordError ideal(R, one(R))
  @test_throws ArgumentError ideal(R, one(R); side = :blub)
  I1 = ideal(R, one(R); side = :twosided)
  I2 = ideal(R, one(R); side = :left)
  I3 = ideal(R, one(R); side = :right)
  @test I1 == I2 == I3
end
