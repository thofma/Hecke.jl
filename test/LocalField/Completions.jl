@testset "Completions" begin
  K, a = cyclotomic_field(7)
  lp = prime_decomposition(maximal_order(K), 7)
  P = lp[1][1]
  C, KtoC = completion(K, P)

  @test is_one(KtoC(one(K)))
  @test is_zero(KtoC(zero(K)))

  a = rand(K, -10:10)
  b = rand(K, -10:10)
  @test KtoC(a * b) == KtoC(a) * KtoC(b)
  @test KtoC(a + b) == KtoC(a) + KtoC(b)

  @test valuation(C(7)) == 1
  @test valuation(KtoC(K(uniformizer(P)))) == 1//6
end
