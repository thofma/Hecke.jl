@testset "HeuristicEndomorphisms" begin
  using Hecke.RiemannSurfaces
  R, t = polynomial_ring(QQ)

  F, r = number_field(t^2 - 5)
  L, a = number_field(t^4 + 3*t^2 + 1)

  S, (x,y) = polynomial_ring(F, [:x,:y])
  f = x^5 + r*x^3 + x - y^2
  v = infinite_places(F)[2]
  RS = RiemannSurface(f,v, 500, integration_method = "heuristic")
  P = big_period_matrix(RS)

  A, h = geometric_homomorphism_representation_nf(P,P,F,v)

  #We might need more and better tests. But these are some basic
  #sanity checks.
  @test is_isomorphic(codomain(h), L)
  @test length(A) == 8

  F, r = number_field(t^2 - t + 1)
  S, (x,y) = polynomial_ring(F, [:x,:y])
  f = (-22*r + 62)*x^6 + (156*r - 312)*x^5 + (-90*r + 126)*x^4 + (-1456*r + 1040)*x^3 + (-66*r + 186)*x^2 + (-156*r + 312)*x - 30*r + 42 - y^2

  v = infinite_places(F)[1]
  RS = RiemannSurface(f,v, 500, integration_method = "heuristic")
  P = big_period_matrix(RS)
  A, h = geometric_homomorphism_representation_nf(P,P,F,v)

  @test is_isomorphic(codomain(h), F)
  @test length(A) == 4

  F, r = rationals_as_number_field()
  S, (x,y) = polynomial_ring(F, [:x,:y])
  f = 10*x^10 + 24*x^9 + 23*x^8 + 48*x^7 + 35*x^6 + 35*x^4 - 48*x^3 + 23*x^2 - 24*x + 10 - y^2
  v = infinite_places(F)[1]
  RS = RiemannSurface(f,500, integration_method = "heuristic")
  P = big_period_matrix(RS)
  A, h = geometric_homomorphism_representation_nf(P,P,F,v)

  @test is_isomorphic(codomain(h), F)
  @test length(A) == 4

  F, r = rationals_as_number_field()
  L, a = number_field(t^6 - t^5 + 2*t^4 + 8*t^3 - t^2 - 5*t + 7)
  S, (x,y) = polynomial_ring(F, [:x,:y])
  f = x^4 - x^3*y + 2*x^3 + 2*x^2*y + 2*x^2 - 2*x*y^2 + 4*x*y - y^3 + 3*y^2 + 2*y + 1
  v = infinite_places(F)[1]
  RS = RiemannSurface(f,500, integration_method = "heuristic")
  P = big_period_matrix(RS)
  A, h = geometric_homomorphism_representation_nf(P,P,F,v)

  @test is_isomorphic(codomain(h), L)
  @test length(A) == 6
end
