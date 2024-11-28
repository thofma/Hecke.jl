@testset "Basic" begin
  Qx, x = polynomial_ring(QQ, "x")
  K, a = number_field(x^2 - 5, "a")
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
  _, _, d, H, I = @inferred invariants(V)
  @test d == 147//2*a+245//2
  @test H == Dict(2 * OK => -1, 7 * OK => -1)
  @test length(I) == 2 && (I[1][2], I[2][2]) in [(1, 0), (0, 1)]
  @test is_isometric(V, V)
  @test !is_isometric(V, quadratic_space(K, 5))

  W = quadratic_space(K, G[1:2,1:2])
  f = hom(W, V, K[1 0 0 0 0; 0 1 0 0 0], check=true)
  v = [K(1), K(0)]
  @test f(v) == image(f, v)
  g = hom(W, W, K[0 1; 1 0], check=true)
  h = compose(g, f)
  @test h(v) == f(g(v))
  @test Hecke.is_isotropic(V, real_places(K)[1])
end
