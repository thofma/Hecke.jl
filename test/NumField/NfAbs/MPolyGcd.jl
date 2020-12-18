@testset "MPolyGcd" begin
  QA, A = PolynomialRing(Hecke.QQ, "A")
  K, a = number_field(A^3 - 2, "a")
  Kx, (x,) = PolynomialRing(K, ["x"])
  g = gcd(-715//2*a^2*x^3 - 715//2*a^2*x^2 - 365525875//2*a^2*x - 365525875//2*a^2, (-715//2*a^2 + 511225)*x^2 - 365525875//2*a^2 + 261351000625)
  @test g == x^2 + 511225
end
