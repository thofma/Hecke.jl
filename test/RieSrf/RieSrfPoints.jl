@testset "RieSrfPoints" begin
  using Hecke.RiemannSurfaces
  Kxy, (x, y) = polynomial_ring(QQ, ["x", "y"])

  @testset "Equality" begin
    RS = riemann_surface(x^6 + x^2 + 1 - y^2, 100, integration_method = "heuristic")
    CC = complex_field(RS)
    P1 = RS([CC(0), CC(1)])
    P2 = RS([CC(0), CC(-1)])
    I1, I2 = infinite_points(RS)

    @test I1 == I1
    @test I2 == I2
    @test I1 != I2
    @test P1 != I1
    @test I1 != P1

    D = P1 + P2 - I1 - I2
    @test degree(D) == 0
    @test D == P2 - I2 + P1 - I1
    @test D != P1 + P2 - 2 * I1
    @test I1 + I2 == I2 + I1

    # the same coordinates on another surface
    RS2 = riemann_surface(x^6 + 1 - y^2, 100, integration_method = "heuristic")
    @test P1 != RS2([CC(0), CC(1)])
    @test I1 != infinite_points(RS2)[1]

    # the two points lying over the singular point (0, 0)
    RS = riemann_surface(y^3 - x^7 + 2*x^3*y, 100, integration_method = "heuristic")
    S1, S2 = filter(P -> P.is_singular, critical_points(RS))
    @test S1 == S1
    @test S1 != S2
  end
end
