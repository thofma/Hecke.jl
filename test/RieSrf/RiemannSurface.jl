@testset "RiemannSurface" begin
  using Hecke.RiemannSurfaces
  K = QQ

  Kxy, (x,y) = polynomial_ring(K, ["x","y"])

  f = x^5 + x^4 + x^3 - x + 4 - y^2
  RS = RiemannSurface(f)
  tau = small_period_matrix(RS)
  R = AcbField(70)
  R2 = AcbField(55)

  test_tau = matrix( [[R("0.5113438425838405028") + R("0.3793845307485294315")*im,
    R("0.37968242378136137665") + R("0.01931936639996602903")*im],
[R("0.379682423781361376") + R("0.01931936639996602903")*im,
    R("0.5515666804208422259") + R("0.7989131245853492630")*im]])

  @test contains(matrix(R2,tau), test_tau)

  # an Elliptic curve
  f = x^3 + 1 - y^2
  RS = RiemannSurface(f)
  tau = small_period_matrix(RS)
  
  R = base_ring(tau)
  t = R("0.5 +/- 1e-10") + R("0.86602540378443864676372317 +/- 1.91e-10")*im
  @test contains(t, tau[1,1])

  # the same but different
  f = x^3-1 - y^2
  RS = RiemannSurface(f)
  small_period_matrix(RS)

  f = x^8 + 2 * x^7 + 2 * x^6 + x^5 - 10 * x + 1 + x^3 * y^2 - y^3 + 2 * y^8
  RS = RiemannSurface(f)
  small_period_matrix(RS)
end
