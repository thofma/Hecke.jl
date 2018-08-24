@testset "Map" begin
  @testset "Existence of (pre)image" begin
    G = DiagonalGroup([3, 5, 0])
    H, mH = sub(G, [G[1]])
    a = G[1]
    b = G[3]
    bb, c = @inferred haspreimage(mH, a)
    @test bb
    @test mH(c) == a
    bb, c = @inferred haspreimage(mH, b)
    @test !bb
    # TODO: Test for hasimage missing
  end

  @testset "Homomorphisms" begin
    G = DiagonalGroup([4, 4, 4])
    H = DiagonalGroup([4, 4, 4])
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
    G = DiagonalGroup([4, 4, 4])
    H = DiagonalGroup([4, 4, 4])
    h = @inferred hom(G, [2*h for h in gens(H)])
    @test h(G[1]) == 2*H[1]
    @test h(G[2]) == 2*H[2]
    @test h(G[3]) == 2*H[3]

    K, mK = @inferred kernel(h)
    @test all(iszero(h(mK(k))) for k in K)
    @test order(K) == 8
  end

  @testset "Image" begin
    G = DiagonalGroup([4, 4, 4])
    H = DiagonalGroup([4, 4, 4])
    h = @inferred hom(G, [2*h for h in gens(H)])
    @test h(G[1]) == 2*H[1]
    @test h(G[2]) == 2*H[2]
    @test h(G[3]) == 2*H[3]

    I, mI = @inferred image(h)
    @test all(haspreimage(h, mI(i))[1] for i in I)
    @test order(I) == 8
  end

  @testset "Injectivity" begin
    G = DiagonalGroup([4, 4, 4])
    H = DiagonalGroup([4, 4, 4])

    h = @inferred hom(G, [2*h for h in gens(H)])
    b = @inferred isinjective(h)
    @test !b

    h = @inferred hom(G, [3*h for h in gens(H)])
    b = @inferred isinjective(h)
    @test b
  end

  @testset "Surjectivity" begin
    G = DiagonalGroup([4, 4, 4])
    H = DiagonalGroup([4, 4, 4])

    h = @inferred hom(G, [2*h for h in gens(H)])
    b = @inferred issurjective(h)
    @test !b

    h = @inferred hom(G, [3*h for h in gens(H)])
    b = @inferred issurjective(h)
    @test b
  end
  
  @testset "Bijectivity" begin
    G = DiagonalGroup([4, 4, 4])
    H = DiagonalGroup([4, 4, 4])

    h = @inferred hom(G, [2*h for h in gens(H)])
    b = @inferred isbijective(h)
    @test !b

    h = @inferred hom(G, [3*h for h in gens(H)])
    b = @inferred isbijective(h)
    @test b
  end
end
