@testset "Morphisms of finite fields" begin
  F = GF(5, 2)
  K = GF(5, 4)
  a = roots(map_coefficients(K, defining_polynomial(F)))[1]
  h = hom(F, K, a)
  x = gen(F)
  @test h(x) == a
  @test preimage(h, h(x + 1)) == x + 1
  @test_throws ErrorException preimage(h, gen(K))
end
