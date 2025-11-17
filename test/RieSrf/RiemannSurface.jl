@testset "RiemannSurface" begin
  using Hecke.RiemannSurfaces
  K = rationals_as_number_field()[1]

  Kxy, (x,y) = polynomial_ring(K, ["x","y"])
  f = x^5 + x^4 + x^3 - x + 4 - y^2

  v = real_places(K)[1]
  RS = RiemannSurface(f, v)
  tau = small_period_matrix(RS)

  # an Elliptic curve
  f = x^3 + 1 - y^2
  RS = RiemannSurface(f, v)
  tau = small_period_matrix(RS)
  R = base_ring(tau)
  t = R("0.5 +/- 1e-10") + R("0.86602540378443864676372317 +/- 1.91e-10")*im
  @test contains(t, tau[1,1])

  # the same but different
  f = x^3-1 - y^2
  RS = RiemannSurface(f, v)
  small_period_matrix(RS)

   Kxy, (x,y) = polynomial_ring(QQ, ["x","y"])
   f = x^8 + 2 * x^7 + 2 * x^6 + x^5 - 10 * x + 1 + x^3 * y^2 - y^3 + 2 * y^8

end
