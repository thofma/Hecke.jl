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
  ok, r = Hecke._finckepohstint(G, 4)
  @test ok
  @test length(r) == 3
  @test all(1 <= n <= 4 for (_, n) in r)

  # E8 roots
  E8 = root_lattice(:E, 8)
  G8 = ZZ.(gram_matrix(E8))
  ok, r8 = Hecke._finckepohstint(G8, 2)
  @test ok
  @test length(r8) == 120

  # 1x1
  G1 = ZZ[3;]
  ok, r1 = Hecke._finckepohstint(G1, 6)
  @test ok
  @test length(r1) == 1
  ok, r2 = Hecke._finckepohstint(G1, 2)
  @test ok
  @test length(r2) == 0

  # 3x3 identity
  I3 = identity_matrix(ZZ, 3)
  ok, r3 = Hecke._finckepohstint(I3, 3)
  @test ok
  @test length(r3) == 13

  # D16: compare with existing implementation
  D16 = root_lattice(:D, 16)
  G16 = ZZ.(gram_matrix(D16))
  ok, r16 = Hecke._finckepohstint(G16, 4)
  @test ok
  sv16 = short_vectors(D16, 4)
  @test length(r16) == length(sv16)

  # Overflow detection
  G_big = ZZ[2 1; 1 2]
  ok, rbig = Hecke._finckepohstint(G_big, typemax(Int))
  @test !ok
  @test isempty(rbig)
end

@testset "Integer Fincke-Pohst iterator" begin
  # Helper: collect iterator and sort for comparison
  function iter_sorted(G, M)
    iter = Hecke.__enumerate_gram(Hecke.FinckePohstIntIterCtx, G, nothing, M,
                                  ZZRingElem, identity, identity, ZZRingElem)
    r = collect(iter)
    sort!(r, by = x -> (x[2], x[1]))
    return r
  end
  function batch_sorted(G, M)
    r = Hecke.__enumerate_gram(Hecke.FinckePohstInt, G, nothing, M,
                                ZZRingElem, identity, identity, ZZRingElem)
    sort!(r, by = x -> (x[2], x[1]))
    return r
  end

  # 2x2: basic correctness
  G = ZZ[2 1; 1 2]
  @test iter_sorted(G, ZZ(8)) == batch_sorted(G, ZZ(8))

  # 1x1
  G1 = ZZ[3;]
  @test iter_sorted(G1, ZZ(6)) == batch_sorted(G1, ZZ(6))
  @test iter_sorted(G1, ZZ(2)) == batch_sorted(G1, ZZ(2))  # no vectors

  # 3x3 identity
  I3 = identity_matrix(ZZ, 3)
  @test iter_sorted(I3, ZZ(3)) == batch_sorted(I3, ZZ(3))

  # 5x5 (same three matrices as "Internal short vector enumeration")
  G5a = matrix(ZZ, 5, 5, [10, -8, -3, -6, -8, -8, 12, 8, 5, 6, -3, 8, 16, 4, 0, -6, 5, 4, 12, 6, -8, 6, 0, 6, 14])
  @test iter_sorted(G5a, ZZ(10)) == batch_sorted(G5a, ZZ(10))

  G5b = matrix(ZZ, 5, 5, [192, 114, 6, -22, -5, 114, 200, -76, 63, -13, 6, -76, 144, 24, 1, -22, 63, 24, 192, 9, -5, -13, 1, 9, 60])
  @test length(iter_sorted(G5b, ZZ(1000))) == 732
  @test iter_sorted(G5b, ZZ(1000)) == batch_sorted(G5b, ZZ(1000))

  G5c = matrix(ZZ, 5, 5, [994, -215, 0, 364, -264, -215, 1926, 1039, -59, 1087, 0, 1039, 1574, -90, 757, 364, -59, -90, 1822, -76, -264, 1087, 757, -76, 966])
  @test length(iter_sorted(G5c, ZZ(10000))) == 844
  @test length(collect(Hecke.__enumerate_gram(Hecke.FinckePohstIntIterCtx, G5c, ZZ(0), ZZ(10000),
                                              ZZRingElem, identity, identity, ZZRingElem))) == 844
  @test iter_sorted(G5c, ZZ(10000)) == batch_sorted(G5c, ZZ(10000))

  # E8 roots
  E8 = root_lattice(:E, 8)
  G8 = ZZ.(gram_matrix(E8))
  @test length(iter_sorted(G8, ZZ(2))) == 120
  @test iter_sorted(G8, ZZ(2)) == batch_sorted(G8, ZZ(2))

  # Lower bound: only vectors with norm >= lb
  G = ZZ[2 1; 1 2]
  iter_lb = Hecke.__enumerate_gram(Hecke.FinckePohstIntIterCtx, G, ZZ(4), ZZ(8),
                                   ZZRingElem, identity, identity, ZZRingElem)
  batch_lb = Hecke.__enumerate_gram(Hecke.FinckePohstInt, G, ZZ(4), ZZ(8),
                                    ZZRingElem, identity, identity, ZZRingElem)
  @test sort(collect(iter_lb), by = x -> (x[2], x[1])) ==
        sort(batch_lb, by = x -> (x[2], x[1]))

  # Laziness: first element without collecting all
  G = ZZ[2 1; 1 2]
  iter = Hecke.__enumerate_gram(Hecke.FinckePohstIntIterCtx, G, nothing, ZZ(8),
                                ZZRingElem, identity, identity, ZZRingElem)
  first_elem = iterate(iter)
  @test first_elem !== nothing

  # Iterator traits
  @test Base.IteratorSize(typeof(iter)) == Base.SizeUnknown()
  @test Base.eltype(typeof(iter)) == Tuple{Vector{ZZRingElem}, ZZRingElem}

  # n=0: immediately exhausted
  G0 = zero_matrix(ZZ, 0, 0)
  iter0 = Hecke.__enumerate_gram(Hecke.FinckePohstIntIterCtx, G0, nothing, ZZ(1),
                                 ZZRingElem, identity, identity, ZZRingElem)
  @test collect(iter0) == Tuple{Vector{ZZRingElem}, ZZRingElem}[]

  # Via _short_vectors_gram_integral: non-trivial LLL, hard=false and hard=true
  G = matrix(ZZ, 5, 5, [10, -8, -3, -6, -8, -8, 12, 8, 5, 6, -3, 8, 16, 4, 0, -6, 5, 4, 12, 6, -8, 6, 0, 6, 14])
  ub = 10
  @test length(collect(Hecke._short_vectors_gram_integral(Hecke.FinckePohstIntIterCtx, G, ub, Int))) == 4
  @test length(collect(Hecke._short_vectors_gram_integral(Hecke.FinckePohstIntIterCtx, G, ub, ZZRingElem))) == 4
  @test length(collect(Hecke._short_vectors_gram_integral(Hecke.FinckePohstIntIterCtx, G, ub))) == 4
  @test length(collect(Hecke._short_vectors_gram_integral(Hecke.FinckePohstIntIterCtx, G, ub, Int; hard = true))) == 4
  @test length(collect(Hecke._short_vectors_gram_integral(Hecke.FinckePohstIntIterCtx, G, ub, ZZRingElem; hard = true))) == 4
  @test length(collect(Hecke._short_vectors_gram_integral(Hecke.FinckePohstIntIterCtx, G, ub; hard = true))) == 4

  # Via _short_vectors_gram_integral: trivial LLL (identity matrix), hard=false and hard=true
  G = identity_matrix(ZZ, 2)
  ub = 4
  @test length(collect(Hecke._short_vectors_gram_integral(Hecke.FinckePohstIntIterCtx, G, ub, Int))) == 6
  @test length(collect(Hecke._short_vectors_gram_integral(Hecke.FinckePohstIntIterCtx, G, ub, ZZRingElem))) == 6
  @test length(collect(Hecke._short_vectors_gram_integral(Hecke.FinckePohstIntIterCtx, G, ub))) == 6
  @test length(collect(Hecke._short_vectors_gram_integral(Hecke.FinckePohstIntIterCtx, G, ub, Int; hard = true))) == 6
  @test length(collect(Hecke._short_vectors_gram_integral(Hecke.FinckePohstIntIterCtx, G, ub, ZZRingElem; hard = true))) == 6
  @test length(collect(Hecke._short_vectors_gram_integral(Hecke.FinckePohstIntIterCtx, G, ub; hard = true))) == 6
end
