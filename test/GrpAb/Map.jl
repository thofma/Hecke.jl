@testset "Map" begin
  @testset "Existence of (pre)image" begin
    G = abelian_group([3, 5, 0])
    H, mH = sub(G, [G[1]])
    a = G[1]
    b = G[3]
    bb, c = @inferred haspreimage(mH, a)
    @test bb
    @test mH(c) == a
    bb, c = @inferred haspreimage(mH, b)
    @test !bb
    # TODO: Test for has_image missing
  end

  @testset "Homomorphisms" begin
    G = abelian_group([4, 4, 4])
    H = abelian_group([4, 4, 4])
    h = @inferred hom(gens(G), gens(H))
    @test h(G[1]) == H[1]
    @test h(G[2]) == H[2]
    @test h(G[3]) == H[3]

    h = @inferred hom(G, [2*h for h in gens(H)])
    @test h(G[1]) == 2*H[1]
    @test h(G[2]) == 2*H[2]
    @test h(G[3]) == 2*H[3]
  end

  @testset "Kernel" begin
    G = abelian_group([4, 4, 4])
    H = abelian_group([4, 4, 4])
    h = @inferred hom(G, [2*h for h in gens(H)])
    @test h(G[1]) == 2*H[1]
    @test h(G[2]) == 2*H[2]
    @test h(G[3]) == 2*H[3]

    K, mK = @inferred kernel(h)
    @test all(iszero(h(mK(k))) for k in K)
    @test order(K) == 8
  end

  @testset "Image" begin
    G = abelian_group([4, 4, 4])
    H = abelian_group([4, 4, 4])
    h = @inferred hom(G, [2*h for h in gens(H)])
    @test h(G[1]) == 2*H[1]
    @test h(G[2]) == 2*H[2]
    @test h(G[3]) == 2*H[3]

    I, mI = @inferred image(h)
    @test all(haspreimage(h, mI(i))[1] for i in I)
    @test order(I) == 8
  end

  @testset "Injectivity" begin
    G = abelian_group([4, 4, 4])
    H = abelian_group([4, 4, 4])

    h = @inferred hom(G, [2*h for h in gens(H)])
    b = @inferred is_injective(h)
    @test !b

    h = @inferred hom(G, [3*h for h in gens(H)])
    b = @inferred is_injective(h)
    @test b
  end

  @testset "Surjectivity" begin
    G = abelian_group([4, 4, 4])
    H = abelian_group([4, 4, 4])

    h = @inferred hom(G, [2*h for h in gens(H)])
    b = @inferred is_surjective(h)
    @test !b

    h = @inferred hom(G, [3*h for h in gens(H)])
    b = @inferred is_surjective(h)
    @test b
  end

  @testset "Bijectivity" begin
    G = abelian_group([4, 4, 4])
    H = abelian_group([4, 4, 4])

    h = @inferred hom(G, [2*h for h in gens(H)])
    b = @inferred is_bijective(h)
    @test !b

    h = @inferred hom(G, [3*h for h in gens(H)])
    b = @inferred is_bijective(h)
    @test b

    # corner case
    G = abelian_group(fmpz[])
    H = abelian_group(fmpz[])
    i = hom(G, H, gens(H))
    j = inv(i)
    @test id(G)==j(id(H))
  end
end
