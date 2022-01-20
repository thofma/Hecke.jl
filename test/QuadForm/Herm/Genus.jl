@testset "Genus" begin
  Qx, x = QQ["x"]
  K, a = NumberField(x^2 - 2, "a")
  OK = maximal_order(K)
  Kt, t  = K["t"]

  E1, b1 = NumberField(t^2 - a, "b1") # ramified at 2
  E2, b2 = NumberField(t^2 - 5, "b2") # unramified at 2

  p = prime_decomposition(OK, 2)[1][1]

  # ramified & dyadic

  g = @inferred genus(HermLat, E1, p, [(0, 1, 1, 0), (2, 2, -1, 1)], type = :det)
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, g) isa String
  @test representative(g) in g

  g = @inferred genus(HermLat, E1, p, [(0, 1, 1, 0), (2, 2, -1, 1)], type = :disc)
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, g) isa String
  @test representative(g) in g

  # negative scale
  g = @inferred genus(HermLat, E1, p, [(-2, 1, 1, -1), (2, 2, -1, 1)], type = :disc)
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, g) isa String

  @test_throws ArgumentError genus(HermLat, E1, p, [(0, 1, 1, 1), (2, 2, -1, 0)], type = :det)
  @test_throws ArgumentError genus(HermLat, E1, p, [(0, 1, 1, 1), (2, 2, -1, 0)], type = :disc)
  @test_throws ArgumentError genus(HermLat, E1, p, [(0, 1, 1, 0), (2, 2, -1, 1)], type = :bla)
  # scale not increasing
  @test_throws ArgumentError genus(HermLat, E1, p, [(3, 1, 1, 0), (2, 2, -1, 1)])
  # negative rank
  @test_throws ArgumentError genus(HermLat, E1, p, [(1, -1, 1, 0), (2, 2, -1, 1)])
  # bad determinant class 
  @test_throws ArgumentError genus(HermLat, E1, p, [(0, 1, 2, 0), (2, 2, -1, 1)])
  # wrong norm valuation (must 1 * 2 since rank is odd)
  @test_throws ArgumentError genus(HermLat, E1, p, [(1, 1, 1, 3)], type = :det)
  # wrong prime
  @test_throws ArgumentError genus(HermLat, E1, p, [(1, 1, 1)], type = :det)
  # wrong prime
  @test_throws ArgumentError genus(HermLat, E1, p, [(1, 1)])

  # unramified & dyadic
  
  g = genus(HermLat, E2, p, [(0, 1, 1), (2, 2, +1)], type = :det)

  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, g) isa String
  g = genus(HermLat, E2, p, [(0, 1, 1), (2, 2, +1)], type = :disc)
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, g) isa String

  # wrong det class
  @test_throws ArgumentError genus(HermLat, E2, p, [(0, 1, -1), (2, 2, +1)], type = :det)
  # wrong det class
  @test_throws ArgumentError genus(HermLat, E2, p, [(0, 1, +1), (2, 2, -1)], type = :det)
  # wrong det class
  @test_throws ArgumentError genus(HermLat, E2, p, [(0, 1, +2), (2, 2, -1)], type = :det)
  # wrong type
  @test_throws ArgumentError genus(HermLat, E2, p, [(0, 1, 1), (2, 2, -1)], type = :bla)
  # negative rank
  @test_throws ArgumentError genus(HermLat, E2, p, [(0, -1, 1), (2, 2, +1)], type = :det)
  # non-increasing scale
  @test_throws ArgumentError genus(HermLat, E2, p, [(3, 1, 1), (2, 2, +1)], type = :det)
  # wrong prime
  @test_throws ArgumentError genus(HermLat, E2, p, [(0, 1, 1, 1)], type = :det)

  # ramified & non-dyadic
  p = prime_decomposition(OK, 5)[1][1]
  g = genus(HermLat, E2, p, [(0, 1, 1), (2, 2, -1)], type = :det)
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, g) isa String
  g = genus(HermLat, E2, p, [(0, 1, 1), (2, 2, -1)], type = :disc)
  @test sprint(show, "text/plain", g) isa String
  @test sprint(show, g) isa String
  @test_throws ArgumentError genus(HermLat, E2, p, [(0, 1, 1), (2, 2, -1)], type = :bla)

  # ramified & non-dyadic and -1 not a local norm
  E, = quadratic_field(7)
  # islocal_norm(E, -1, 7) == false
  g = genus(HermLat, E, fmpz(7), [(0, 2, 1)], type = :disc)
  @test g == genus(HermLat, E, fmpz(7), [(0, 2, -1)])
  g = genus(HermLat, E, fmpz(7), [(0, 2, 1), (1, 1, -1), (2, 3, -1)], type = :disc)
  @test g == genus(HermLat, E, fmpz(7), [(0, 2, -1), (1, 1, -1), (2, 3, 1)])
end
