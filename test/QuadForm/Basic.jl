@testset "Basic" begin
  Qx, x = PolynomialRing(FlintQQ, "x")
  K, a = NumberField(x^2 - 5, "a")
  OK = maximal_order(K)
  G = matrix(K, 5, 5, [ 1, 0, 0, 0, 0,
                        0, 1, 0, 0, 0,
                        0, 0, 7, 0, 0,
                        0, 0, 0, 1//2*(a + 1), 0,
                        0, 0, 0, 0, 1//2*(7*a + 35) ])

  V = quadratic_space(K, G)
  @test hasse_invariant(V, 2 * OK) == -1
  @test hasse_invariant(V, 7 * OK) == -1
  @test hasse_invariant(V, real_places(K)[1]) == 1
  @test hasse_invariant(V, real_places(K)[2]) == 1

  @test witt_invariant(V, 2 * OK) == -1
  @test witt_invariant(V, 7 * OK) == -1
  @test witt_invariant(V, real_places(K)[1]) == -1
  @test witt_invariant(V, real_places(K)[2]) == -1

  plc = real_places(K)
  d, H, I = @inferred invariants(V)
  @test d == 147//2*a+245//2
  @test H == Dict(2 * OK => -1, 7 * OK => -1)
  @test length(I) == 2 && (I[1][2], I[2][2]) in [(1, 0), (0, 1)]
  @test isequivalent(V, V)
  @test !isequivalent(V, quadratic_space(K, 5))
end
