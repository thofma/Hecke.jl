@testset "GenOrd" begin
  # Test first the ring interface
  Qx, x = QQ["x"]
  K, _ = number_field(x^3 - 18, "a")
  O = @inferred Order(ZZ, K)
  @test O isa Hecke.GenOrd
  ConformanceTests.test_Ring_interface(O)

  k = GF(5)
  kx, x = rational_function_field(k, "x")
  kt = parent(numerator(x))
  ky, y = polynomial_ring(kx, "y")
  F, a = function_field(y^3+(4*x^3 + 4*x^2 + 2*x +2)*y^2 + (3*x+3)*y +2)
  Ofin = integral_closure(kt, F)

  # Promotion
  @test Ofin(one(k)) == one(Ofin)
  @test Ofin(one(kt)) == one(Ofin)
  @test Ofin(one(ZZ)) == one(Ofin)
  @test one(Ofin) + 1 == Ofin(2)
  @test one(Ofin) + one(k) == Ofin(2)
  @test one(Ofin) + one(kt) == Ofin(2)

  u = canonical_unit(one(Ofin))
  @test parent(u) === Ofin
  @test is_unit(u)
end
