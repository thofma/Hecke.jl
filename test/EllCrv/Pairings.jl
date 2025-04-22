@testset "Pairings" begin

  K, a = cyclotomic_field(5)
  E = elliptic_curve(K, [0, -1, 1, -10, -20])
  T = torsion_structure(E)[2]
  E_O = infinity(E)
  P = T[1]
  Q = T[2]

  @test @inferred weil_pairing(P, Q, 5) == a^3
  @test @inferred weil_pairing(Q, P, 5) == a^2
  @test @inferred weil_pairing(P, P, 5) == 1
  @test @inferred weil_pairing(P, 3*P, 5) == 1
  @test @inferred weil_pairing(P, E_O, 5) == 1

  K = GF(197)
  E = elliptic_curve(K, [47, 75])
  P = E([133, 26])
  @test weil_pairing(P, 2*P, 24) == 1
  @test weil_pairing(P, P, 24) == 1
  @test weil_pairing(P, -2*P, 24) == 1
  @test weil_pairing(P, -P, 24) == 1

  tp = tate_pairing(P, 2*P, 24)
  # Should be in the same class as 33
  Kt, t = K["t"]
  @test length(roots(t^24 - tp//K(33))) > 0

  tp = tate_pairing(P, 2*P, -24)
  # Should be in the same class as 33
  @test length(roots(t^24 - tp//K(33))) > 0

  tp = tate_pairing(0*P, P, 24)
  # Should be in the same class as 1
  @test length(roots(t^24 - tp)) > 0
  tp = tate_pairing(0*P, P, -24)
  # Should be in the same class as 1
  @test length(roots(t^24 - tp)) > 0
  tp = tate_pairing(P, 0*P, -24)
  # Should be in the same class as 1
  @test length(roots(t^24 - tp)) > 0

  @test_throws ArgumentError weil_pairing(P, 0*P, 3)
  @test_throws ArgumentError weil_pairing(0*P, P, 3)
  @test_throws ArgumentError weil_pairing(P, infinity(elliptic_curve(K, [1, 1])), 24)

  @test_throws ArgumentError tate_pairing(P, 0*P, 3)
  @test_throws ArgumentError tate_pairing(P, infinity(elliptic_curve(K, [1, 1])), 24)

  @test_throws ArgumentError reduced_tate_pairing(P, 0*P, 3)
  @test_throws ArgumentError reduced_tate_pairing(P, infinity(elliptic_curve(K, [1, 1])), 24)
  @test_throws ArgumentError reduced_tate_pairing(0*P, 0*P, 3)

  K = GF(19, 4)
  a = gen(K)
  E = elliptic_curve(K, [-1,0])

  P = E([10*a^3 + 13*a^2 + 14*a + 2, 2*a^3 + 12*a^2 + 18*a + 4])
  Q = E([18*a^3 + 17*a^2 + 12*a + 18, 6*a^3 + 9*a^2 + 3*a + 1])

  @test @inferred weil_pairing(P, Q, 360) == a^22806

  K = GF(3, 4)
  a = gen(K)
  E = elliptic_curve(K, [1,1,0,0,1])
  P = E([a^67, a^64])
  Q = E([a^55, a^72])
  @test @inferred tate_pairing(P, Q, 5) == a^69

  @test @inferred reduced_tate_pairing(P, Q, 5) == a^64

end

