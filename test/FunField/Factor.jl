@testset "Factor" begin
  kt, t = rational_function_field(GF(3), "t")
  ktx, x = kt[:x]
  F, a = function_field(x^2 + 1)
  Fy, y = F[:y]
  f = t*y^2 * (y^3 + t^3*a^3)^2
  fac = factor(f)
  @test unit(fac) * prod(p^e for (p, e) in fac) == f
  @test all(isone(degree(p)) for (p, _) in fac)
  f = t*y^2 * (y + t*a)^2
  fac = factor(f)
  @test unit(fac) * prod(p^e for (p, e) in fac) == f
  @test all(isone(degree(p)) for (p, _) in fac)
end
