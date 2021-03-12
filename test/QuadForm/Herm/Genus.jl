@testset "Genus" begin
  Qx, x = QQ["x"]
  K, a = NumberField(x^2 - 2, "a")
  OK = maximal_order(K)
  Kt, t  = K["t"]

  E1, b1 = NumberField(t^2 - a, "b1") # ramified at 2
  E2, b2 = NumberField(t^2 - 5, "b2") # unramified at 2

  p = prime_decomposition(OK, 2)[1][1]
  # ramified & dyadic
  g = genus(HermLat, E1, p, [(0, 1, 1, 0), (2, 2, -1, 1)], type = :det)
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, g) isa String
  g = genus(HermLat, E1, p, [(0, 1, 1, 0), (2, 2, -1, 1)], type = :disc)
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, g) isa String
  @test_throws ErrorException genus(HermLat, E1, p, [(0, 1, 1, 1), (2, 2, -1, 0)], type = :det)
  @test_throws ErrorException genus(HermLat, E1, p, [(0, 1, 1, 1), (2, 2, -1, 0)], type = :disc)
  @test_throws ErrorException genus(HermLat, E1, p, [(0, 1, 1, 0), (2, 2, -1, 1)], type = :bla)

  # unramified & dyadic
  g = genus(HermLat, E2, p, [(0, 1, 1), (2, 2, -1)], type = :det)
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, g) isa String
  g = genus(HermLat, E2, p, [(0, 1, 1), (2, 2, -1)], type = :disc)
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, g) isa String
  @test_throws ErrorException genus(HermLat, E2, p, [(0, 1, 1), (2, 2, -1)], type = :bla)

  # ramified & non-dyadic
  p = prime_decomposition(OK, 5)[1][1]
  g = genus(HermLat, E2, p, [(0, 1, 1), (2, 2, -1)], type = :det)
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, g) isa String
  g = genus(HermLat, E2, p, [(0, 1, 1), (2, 2, -1)], type = :disc)
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, g) isa String
  @test_throws ErrorException genus(HermLat, E2, p, [(0, 1, 1), (2, 2, -1)], type = :bla)
end
