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
  @tet isisomorphic(K, L)[1]
end
