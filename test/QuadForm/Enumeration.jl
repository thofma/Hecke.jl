@testset "Internal short vector enumeration" begin
  G = matrix(ZZ, 5, 5, [10, -8, -3, -6, -8, -8, 12, 8, 5, 6, -3, 8, 16, 4, 0, -6, 5, 4, 12, 6, -8, 6, 0, 6, 14])
  ub = 10
  sv = @inferred Hecke.__enumerate_gram(Vector, G, nothing, ub)
  @test length(sv) == 4
  sv = @inferred Hecke.__enumerate_gram(Vector, G, 0, ub)
  @test length(sv) == 4

  G = matrix(ZZ, 5, 5, [192, 114, 6, -22, -5, 114, 200, -76, 63, -13, 6, -76, 144, 24, 1, -22, 63, 24, 192, 9, -5, -13, 1, 9, 60])
  ub = 1000
  sv = @inferred Hecke.__enumerate_gram(Vector, G, nothing, ub)
  @test length(sv) == 732
  sv = @inferred Hecke.__enumerate_gram(Vector, G, 0, ub)
  @test length(sv) == 732

  G = matrix(ZZ, 5, 5, [994, -215, 0, 364, -264, -215, 1926, 1039, -59, 1087, 0, 1039, 1574, -90, 757, 364, -59, -90, 1822, -76, -264, 1087, 757, -76, 966])
  ub = 10000
  sv = @inferred Hecke.__enumerate_gram(Vector, G, nothing, ub)
  @test length(sv) == 844
  sv = @inferred Hecke.__enumerate_gram(Vector, G, 0, ub)
  @test length(sv) == 844

  # Test the _short_vectors_gram_integral interface
  # The following has non-trivial LLL
  G = matrix(ZZ, 5, 5, [10, -8, -3, -6, -8, -8, 12, 8, 5, 6, -3, 8, 16, 4, 0, -6, 5, 4, 12, 6, -8, 6, 0, 6, 14])
  ub = 10
  @test length(@inferred Hecke._short_vectors_gram_integral(Vector, G, ub, Int)) == 4
  @test length(@inferred Hecke._short_vectors_gram_integral(Vector, G, ub, ZZRingElem)) == 4
  @test length(@inferred Hecke._short_vectors_gram_integral(Vector, G, ub)) == 4
  @test length(collect(@inferred Hecke._short_vectors_gram_integral(Hecke.LatEnumCtx, G, ub, Int))) == 4
  @test length(collect(@inferred Hecke._short_vectors_gram_integral(Hecke.LatEnumCtx, G, ub, ZZRingElem))) == 4
  @test length(collect(@inferred Hecke._short_vectors_gram_integral(Hecke.LatEnumCtx, G, ub))) == 4

  @test length(@inferred Hecke._short_vectors_gram_integral(Vector, G, ub, Int; hard = true)) == 4
  @test length(@inferred Hecke._short_vectors_gram_integral(Vector, G, ub, ZZRingElem; hard = true)) == 4
  @test length(@inferred Hecke._short_vectors_gram_integral(Vector, G, ub; hard = true)) == 4
  @test length(collect(@inferred Hecke._short_vectors_gram_integral(Hecke.LatEnumCtx, G, ub, Int; hard = true))) == 4
  @test length(collect(@inferred Hecke._short_vectors_gram_integral(Hecke.LatEnumCtx, G, ub, ZZRingElem; hard = true))) == 4
  @test length(collect(@inferred Hecke._short_vectors_gram_integral(Hecke.LatEnumCtx, G, ub; hard = true))) == 4

  # Now one with trivial LLL
  G = identity_matrix(ZZ, 2)
  ub = 4
  @test length(@inferred Hecke._short_vectors_gram_integral(Vector, G, ub, Int)) == 6
  @test length(@inferred Hecke._short_vectors_gram_integral(Vector, G, ub, ZZRingElem)) == 6
  @test length(@inferred Hecke._short_vectors_gram_integral(Vector, G, ub)) == 6
  @test length(collect(@inferred Hecke._short_vectors_gram_integral(Hecke.LatEnumCtx, G, ub, Int))) == 6
  @test length(collect(@inferred Hecke._short_vectors_gram_integral(Hecke.LatEnumCtx, G, ub, ZZRingElem))) == 6
  @test length(collect(@inferred Hecke._short_vectors_gram_integral(Hecke.LatEnumCtx, G, ub))) == 6

  @test length(@inferred Hecke._short_vectors_gram_integral(Vector, G, ub, Int; hard = true)) == 6
  @test length(@inferred Hecke._short_vectors_gram_integral(Vector, G, ub, ZZRingElem; hard = true)) == 6
  @test length(@inferred Hecke._short_vectors_gram_integral(Vector, G, ub; hard = true)) == 6
  @test length(collect(@inferred Hecke._short_vectors_gram_integral(Hecke.LatEnumCtx, G, ub, Int; hard = true))) == 6
  @test length(collect(@inferred Hecke._short_vectors_gram_integral(Hecke.LatEnumCtx, G, ub, ZZRingElem; hard = true))) == 6
  @test length(collect(@inferred Hecke._short_vectors_gram_integral(Hecke.LatEnumCtx, G, ub; hard = true))) == 6
end

@testset "Integer Fincke-Pohst" begin
  # 2x2
  G = ZZ[2 1; 1 2]
  r = Hecke._finckepohstint(G, 4)
  @test length(r) == 3
  @test all(1 <= n <= 4 for (_, n) in r)

  # E8 roots
  E8 = root_lattice(:E, 8)
  G8 = ZZ.(gram_matrix(E8))
  r8 = Hecke._finckepohstint(G8, 2)
  @test length(r8) == 120

  # 1x1
  G1 = ZZ[3;]
  @test length(Hecke._finckepohstint(G1, 6)) == 1
  @test length(Hecke._finckepohstint(G1, 2)) == 0

  # 3x3 identity
  I3 = identity_matrix(ZZ, 3)
  @test length(Hecke._finckepohstint(I3, 3)) == 13

  # D16: compare with existing implementation
  D16 = root_lattice(:D, 16)
  G16 = ZZ.(gram_matrix(D16))
  r16 = Hecke._finckepohstint(G16, 4)
  sv16 = short_vectors(D16, 4)
  @test length(r16) == length(sv16)

  # Overflow detection
  G_big = ZZ[2 1; 1 2]
  @test_throws ErrorException Hecke._finckepohstint(G_big, typemax(Int))
end
