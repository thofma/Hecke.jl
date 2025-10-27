@testset "RiemannSurface" begin
  using Hecke.RiemannSurfaces
  K = rationals_as_number_field()[1]

  Kxy, (x,y) = polynomial_ring(K, ["x","y"])
  f = x^5 + x^4 + x^3 -x + 4 - y^2

  v = real_places(K)[1]
  RS = RiemannSurface(f, v)
  tau = small_period_matrix(RS)

  # an elliptic curve
  f = x^3+1 - y^2
  RS = RiemannSurface(f, v)
  tau = small_period_matrix(RS)
  R = base_ring(tau)
  x = R("0.5 +/- 1e-10") + R("0.86602540378443864676372317 +/- 1.91e-10")*im
  @test contains(x, tau[1,1])

  # another elliptic curve
  @test_broken f = x^3 + 2*x^2*y + 3*x - 4 + 5*y^2 # Redefining Kxy helps somehow
  Kxy, (x,y) = polynomial_ring(K, ["x","y"])
  f = x^3 + 2*x^2*y + 3*x - 4 + 5*y^2
  RS = RiemannSurface(f, v)
  tau = small_period_matrix(RS)
  x = R("0.4968045031 +/- 1e-10") + R("0.2904966226 +/- 1e-10")*im
  @test contains(x, tau[1,1])

  # ERROR: A larger example -- this throws an ArgumentError although it works perfectly fine in Magma
  Kxy, (x,y) = polynomial_ring(K, ["x","y"])
  f = x^8 + 2 * x^7 + 2 * x^6 + x^5 - 10 * x + 1 + x^3 * y^2 - y^3 + 2 * y^8
  RS = RiemannSurface(f, v)
  @test_broken small_period_matrix(RS)

end
