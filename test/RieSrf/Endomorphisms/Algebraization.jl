@testset "Algebraization" begin
  RSM = Hecke.RiemannSurfaces
  Qt, t = polynomial_ring(QQ, :t)
  CC = AcbField(200)

  # an element of Q(sqrt 2), for both embeddings
  F, a = number_field(t^2 - 2, :a)
  z = 1 + 3*sqrt(CC(2))
  for v in infinite_places(F)
    b = RSM.algebraize_element(z, F, v)
    @test b == 1 + 3*a || b == 1 - 3*a
  end

  # the minimal polynomial of 1 + sqrt 2 over QQ
  K, _ = rationals_as_number_field()
  f = RSM.approximate_minimal_polynomial(1 + sqrt(CC(2)), K, infinite_places(K)[1])
  @test degree(f) == 2
  @test all(overlaps(evaluate(map_coefficients(c -> CC(coeff(c, 0)), f), r), zero(CC))
            for r in (1 + sqrt(CC(2)), 1 - sqrt(CC(2))))
end
