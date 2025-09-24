@testset "Simplify" begin
  Qx, x = polynomial_ring(QQ, "x")
  K, a = number_field(x^2 - 10, cached = false)
  L, mL = simplify(K)
  @test is_isomorphic(K, L)

  K, a = number_field(x^2 - 100000000000000000000000, cached = false)
  L, mL = simplify(K)
  @test is_isomorphic(K, L)

  K, a = number_field(x - 10, cached = false)
  L, mL = simplify(K)
  @test is_isomorphic(K, L)

  K,a = number_field(x^4-100020001*x^2+100040006000400010, cached = false)
  L, mL = simplify(K)
  @test is_isomorphic(K, L)

  K, a = number_field(8*x^3 + 4*x^2 - 4*x - 1, cached = false)
  L, mL = simplify(K)
  @test Hecke.is_defining_polynomial_nice(L)
  L1, mL1 = simplify(K, canonical = true)
  @test Hecke.is_defining_polynomial_nice(L1)
  @test is_isomorphic(L1, L)

  f = -1//3*x^2 - x + 1
  K, a = number_field(f, cached = false)
  L, mL = simplify(K)
  @test is_isomorphic(K, L)

  f = x - 1
  K, a = number_field(f, cached = false)
  _, g = Hecke.polredabs(K)
  @test g == f

  f = -x^3 - 14*x^2 - 13*x + 6
  K, a = number_field(f, cached = false)
  L, _ = simplify(K)
  g = defining_polynomial(L)
  @test is_monic(g) && is_one(denominator(g))

  let
    # issue #1897
    R, x = polynomial_ring(QQ, :x)
    f = x^3 - 65637*x - 5630196
    K, = simplify(number_field(f)[1]; canonical = true)
    @test defining_polynomial(K) == f
  end
end
