@testset "Map" begin
  @testset "Existence of (pre)image" begin
    G = abelian_group([3, 5, 0])
    H, mH = sub(G, [G[1]])
    a = G[1]
    b = G[3]
    bb, c = @inferred has_preimage_with_preimage(mH, a)
    @test bb
    @test mH(c) == a
    bb, c = @inferred has_preimage_with_preimage(mH, b)
    @test !bb
    # TODO: Test for has_image missing

    fl, c = @inferred has_preimage_with_preimage(mH, elem_type(H)[])
    @test fl
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

    G = abelian_group(Int[])
    H = abelian_group([2])
    h = hom(G, H, eltype(G)[])
    K, mK = @inferred kernel(h)
    @test isone(order(K))
  end

  @testset "Image" begin
    G = abelian_group([4, 4, 4])
    H = abelian_group([4, 4, 4])
    h = @inferred hom(G, [2*h for h in gens(H)])
    @test h(G[1]) == 2*H[1]
    @test h(G[2]) == 2*H[2]
    @test h(G[3]) == 2*H[3]

    I, mI = @inferred image(h)
    @test all(has_preimage_with_preimage(h, mI(i))[1] for i in I)
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

    G = abelian_group([0, 2, 0, 2])
    H = abelian_group([0, 2])
    g = hom(G, H, [gen(H, 1), gen(H, 2), gen(H, 1), gen(H, 2)])
    @test (@inferred is_surjective(g))
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
    G = abelian_group(ZZRingElem[])
    H = abelian_group(ZZRingElem[])
    i = hom(G, H, gens(H))
    j = inv(i)
    @test id(G)==j(id(H))
  end

  @testset "Post- and preinverse" begin
    G = abelian_group([0, 2, 0, 2])
    H = abelian_group([0, 2])
    f = hom(H, G, [gen(G, 3), gen(G, 4)])
    g = hom(G, H, [gen(H, 1), gen(H, 2), gen(H, 1), gen(H, 2)])
    ff = postinverse(f)
    @test f * ff == id_hom(H)
    gg = preinverse(g)
    @test gg * g == id_hom(H)
    @test_throws ArgumentError preinverse(f)
    @test_throws ArgumentError postinverse(g)
  end
end
