@testset "Simplify" begin
  Qx, x = PolynomialRing(FlintQQ, "x")
  K, a = NumberField(x^2 - 10, cached = false)
  L, mL = simplify(K)
  @test isisomorphic(K, L)[1]

  K, a = NumberField(x^2 - 100000000000000000000000, cached = false)
  L, mL = simplify(K)
  @test isisomorphic(K, L)[1]

  K, a = NumberField(x - 10, cached = false)
  L, mL = simplify(K)
  @test isisomorphic(K, L)[1]

  K,a = NumberField(x^4-100020001*x^2+100040006000400010, cached = false)
  L, mL = simplify(K)
  @test isisomorphic(K, L)[1]

  K, a = number_field(8*x^3 + 4*x^2 - 4*x - 1, cached = false)
  L, mL = simplify(K)
  @test Hecke.isdefining_polynomial_nice(L)
  L1, mL1 = simplify(K, canonical = true)
  @test Hecke.isdefining_polynomial_nice(L1)
  @test isisomorphic(L1, L)[1]

  f = -1//3*x^2 - x + 1
  K, a = number_field(f, cached = false)
  L, mL = simplify(K)
  @test isisomorphic(K, L)[1]

  f = x - 1
  K, a = number_field(f, cached = false)
  _, g = Hecke.polredabs(K)
  @test g == f
end
