@testset "PeriodMatrix" begin
  using Hecke.RiemannSurfaces
  Kxy, (x, y) = polynomial_ring(QQ, ["x", "y"])
  f = x^5 + x^4 + x^3 - x + 4 - y^2

  tau = small_period_matrix(riemann_surface(f, 100, integration_method = "rigorous"))
  tau_heuristic = small_period_matrix(riemann_surface(f, 100, integration_method = "heuristic"))
  @test overlaps(tau, tau_heuristic)
  @test all(z -> Hecke.radiuslttwopower(z, -80), tau)
end
