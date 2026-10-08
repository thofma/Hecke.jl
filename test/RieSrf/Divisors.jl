@testset "Divisors" begin
  using Hecke.RiemannSurfaces
  Kxy, (x, y) = polynomial_ring(QQ, ["x", "y"])
  RS = riemann_surface(x^6 + x^2 + 1 - y^2, 100, integration_method = "heuristic")
  CC = complex_field(RS)
  P1 = RS([CC(0), CC(1)])
  P2 = RS([CC(0), CC(-1)])
  I1, I2 = infinite_points(RS)

  # points whose multiplicities cancel leave the support
  D = P1 + I1 - P1
  @test support(D) == ([I1], [1])
  @test D == 1 * I1
  @test P1 + P2 + I1 - I2 - P2 - I1 == P1 - I2

  D = P1 - P1
  @test isempty(support(D)[1])
  @test degree(D) == 0
  @test D + I2 == 1 * I2
end
