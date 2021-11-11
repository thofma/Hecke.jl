@testset "Test inverse of MapFromFunc" begin
  f = MapFromFunc(x -> x+1, x -> x-1, ZZ, ZZ)
  x = ZZ(1)
  y = f(x)
  @test preimage(f, y) == x

  finv = inv(f)
  y = finv(x)
  @test preimage(finv, y) == x
end
