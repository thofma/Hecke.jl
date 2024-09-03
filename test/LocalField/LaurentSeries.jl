@testset "Local field interface" begin
  K, x = laurent_series_field(GF(3), 10, "x")
  @test characteristic(K) == 3

  p = uniformizer(K)
  @test p == x

  p = uniformizer(K, 3, prec = 5)
  @test p == x^3
  @test precision(p) == 5
  q = setprecision(p, 10)
  @test precision(p) == 5
  @test precision(q) == 10
  setprecision!(p, 10)
  @test precision(p) == 10

  @test absolute_ramification_index(K) == 1

  @test Hecke._valuation_integral(x^2) == 2

  k, Ktok = residue_field(K)
  @test k === base_ring(K)

  @test_throws ErrorException Ktok(x^-1)
  @test is_zero(Ktok(x))
  @test is_one(Ktok(x + 1))
  @test is_one(Ktok\one(k))
end
