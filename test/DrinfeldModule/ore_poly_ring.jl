@testset "OrePolyRing" begin
  # Set up: F_4[T] as function ring, F_16 as base field
  Fq, _ = finite_field(2, 2, "a")
  K, b = finite_field(2, 4, "b")
  A, T = polynomial_ring(Fq, "T")
  q = ZZRingElem(order(Fq))

  R, tau = ore_polynomial_ring(K, q, :tau)

  @test base_ring(R) === K
  @test var(R) == :tau

  # Zero and one
  z = zero(R)
  o = one(R)
  @test iszero(z)
  @test isone(o)
  @test degree(z) == -1
  @test degree(o) == 0

  # Generator
  @test degree(tau) == 1
  @test constant_coefficient(tau) == zero(K)
  @test leading_coefficient(tau) == one(K)

  # Arithmetic
  c1 = K(1)
  c2 = b  # a generator of F_16 over F_2
  f = R(c1) + tau  # 1 + tau
  g = tau + R(c2)  # tau + c2

  @test degree(f) == 1
  @test coeff(f, 0) == c1
  @test coeff(f, 1) == one(K)

  # Multiplication: tau * c = c^q * tau
  tc = tau * R(c2)
  @test degree(tc) == 1
  @test coeff(tc, 0) == zero(K)
  @test coeff(tc, 1) == c2^q  # c2^4

  # Left mult: c * tau = c * tau (no twist on left constant mult)
  ct = R(c2) * tau
  @test coeff(ct, 1) == c2

  # Right division: f = q*g + r, deg(r) < deg(g)
  # Take f = tau^2 + tau + 1, g = tau + 1
  f2 = tau^2 + tau + one(R)
  g2 = tau + one(R)
  q2, r2 = right_quo_rem(f2, g2)
  @test f2 == q2 * g2 + r2
  @test degree(r2) < degree(g2)

  # Valuation
  @test ore_poly_valuation(z) == 0  # zero: returns degree + 1 = -1 + 1 = 0
  @test ore_poly_valuation(o) == 0
  @test ore_poly_valuation(tau) == 1

  f3 = tau^2  # no constant or linear term
  @test ore_poly_valuation(f3) == 2
end
