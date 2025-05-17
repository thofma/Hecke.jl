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

  # inseparable extension
  let
    k, o = finite_field(9)
    kt, t = rational_function_field(k, "t")
    ktx, x = kt[:x]
    F, a = function_field(x^3 - t, "a")
    Fy, y = polynomial_ring(F, :x)
    f = o*(y^3 - t)
    @test !is_squarefree(f)
    fac = factor_squarefree(f)
    @test evaluate(fac) == f
    @test all(isone(degree(p)) for (p, _) in fac)
    fac = factor(f)
    @test evaluate(fac) == f
    @test length(fac) == 1
  end
end
