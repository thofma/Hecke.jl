@testset "GrpAbFinGen" begin
  @testset "Type stuff" begin
    @test elem_type(GrpAbFinGen) == GrpAbFinGenElem
    @test parent_type(GrpAbFinGenElem) == GrpAbFinGen
  end

  @testset "Constructor" begin
    M1 = matrix(FlintZZ, 2, 3, [1, 2, 3, 4, 5, 6])
    G = @inferred AbelianGroup(M1)
    @test isa(G, GrpAbFinGen)
    @test G.rels == M1

    M = FlintZZ[1 2 3; 4 5 6] # fmpz_mat
    G = @inferred AbelianGroup(M)
    @test isa(G, GrpAbFinGen)
    @test G.rels == M1

    M = fmpz[1 2 3; 4 5 6]
    G = @inferred AbelianGroup(M)
    @test isa(G, GrpAbFinGen)
    @test G.rels == M1

    M = [1 2 3; 4 5 6]
    G = @inferred AbelianGroup(M)
    @test isa(G, GrpAbFinGen)
    @test G.rels == M1

    M = fmpz[1, 2, 3, 4, 5, 6]
    G = @inferred AbelianGroup(M)
    @test isa(G, GrpAbFinGen)
    @test G.rels == matrix(FlintZZ, 1, 6, M)

    M = [1, 2, 3, 4, 5, 6]
    G = @inferred AbelianGroup(M)
    @test isa(G, GrpAbFinGen)
    @test G.rels == matrix(FlintZZ, 1, 6, M)

    M = [3, 0]
    G = @inferred DiagonalGroup(M)
    @test isa(G, GrpAbFinGen)

    M = fmpz[3, 0]
    G = @inferred DiagonalGroup(M)
    @test isa(G, GrpAbFinGen)

    M = matrix(FlintZZ, 1, 2, [3, 0])
    G = @inferred DiagonalGroup(M)
    @test isa(G, GrpAbFinGen)

    N = [3, 5]
    G = @inferred DiagonalGroup(N)
    @test isa(G, GrpAbFinGen)
    @test G.rels == matrix(FlintZZ, 2, 2, [3, 0, 0, 5])

    N = fmpz[3, 5]
    G = @inferred DiagonalGroup(N)
    @test isa(G, GrpAbFinGen)
    @test G.rels == matrix(FlintZZ, 2, 2, [3, 0, 0, 5])

    N = matrix(FlintZZ, 1, 2, [3, 5])
    G = @inferred DiagonalGroup(N)
    @test isa(G, GrpAbFinGen)
    @test G.rels == matrix(FlintZZ, 2, 2, [3, 0, 0, 5])

    @test_throws ErrorException DiagonalGroup(FlintZZ[1 2; 3 4])

    @testset "String I/O" begin
      @test issnf(M)
      @test isa(string(M), String)
      @test isa(string(N), String)
    end

    @testset "Field access" begin
      S = DiagonalGroup([3, 0])
      @test @inferred issnf(S)
      @test @inferred ngens(S) == 2
      @test @inferred nrels(S) == 2
      @test @inferred rels(S) == matrix(FlintZZ, 2, 2, [3, 0, 0, 0])

      G = DiagonalGroup([3, 5])
      @test @inferred !issnf(G)
      @test @inferred ngens(G) == 2
      @test @inferred nrels(G) == 2
      @test @inferred rels(G) == matrix(FlintZZ, 2, 2, [3, 0, 0, 5])
    end

    @testset "Hermite normal form" begin
      M   = FlintZZ[1 2 3; 4 5 6]
      HNF = FlintZZ[1 2 3; 0 3 6]
      G = AbelianGroup(M)
      Hecke.assure_has_hnf(G)
      @test G.hnf == HNF
    end

    @testset "Smith normal form" begin
      M = FlintZZ[16 17 2 ; 19 23 8 ; 16 17 2]
      G = AbelianGroup(M)
      S, mS = @inferred snf(G)
      @test issnf(S)
      @test S.snf == fmpz[45, 0]
      @test codomain(mS) == G
      @test domain(mS) == S
    end

    @testset "Finiteness" begin
      G = DiagonalGroup([3, 15])
      @test issnf(G)
      @test @inferred isfinite(G)
      @test @inferred !isinfinite(G)

      G = DiagonalGroup([3, 5])
      @test @inferred isfinite(G)
      @test @inferred !isinfinite(G)

      G = DiagonalGroup([3, 15, 0])
      @test issnf(G)
      @test @inferred !isfinite(G)
      @test @inferred isinfinite(G)

      G = DiagonalGroup([3, 5, 0])
      @test @inferred !isfinite(G)
      @test @inferred isinfinite(G)
    end

    @testset "Rank" begin
      G = DiagonalGroup([3, 15])
      @test @inferred rank(G) == 0

      G = DiagonalGroup([3, 5])
      @test @inferred rank(G) == 0

      G = DiagonalGroup([3, 15, 0])
      @test @inferred rank(G) == 1

      G = DiagonalGroup([3, 5, 0])
      @test @inferred rank(G) == 1
    end

    @testset "Order" begin
      G = DiagonalGroup([3, 5])
      @test @inferred order(G) == 15
      G = DiagonalGroup([3, 15])
      @test @inferred order(G) == 45
      G = DiagonalGroup([3, 5, 0])
      @test_throws ErrorException order(G)
    end

    @testset "Exponent" begin
      G = DiagonalGroup([3, 5])
      @test @inferred exponent(G) == 15
      G = DiagonalGroup([3, 15])
      @test @inferred exponent(G) == 15
    end

    @testset "Trivial" begin
      G = DiagonalGroup([1])
      @test @inferred istrivial(G)
      G = DiagonalGroup([1, 1, 1])
      @test @inferred istrivial(G)
      G = DiagonalGroup([3, 3])
      @test @inferred !istrivial(G)
      G = DiagonalGroup([3, 5])
      @test @inferred !istrivial(G)
    end

    @testset "Isomorphism" begin
      b = @inferred isisomorphic(DiagonalGroup(Int[]), DiagonalGroup(Int[]))
      @test b

      G = DiagonalGroup([2, 3, 5])
      H = DiagonalGroup([30])
      @test @inferred isisomorphic(G, H)
    end

    @testset "Direct product" begin
      G = DiagonalGroup([5, 3])
      H = DiagonalGroup([4])
      K = @inferred direct_product(G, H)
      @test isisomorphic(K, DiagonalGroup([60]))
    end

    @testset "Torsion" begin
      G = DiagonalGroup([5, 4])
      @test @inferred istorsion(G)
      H, mH = torsion_subgroup(G)
      @test order(H) == 20

      G = DiagonalGroup([5, 0, 4, 0])
      @test @inferred !istorsion(G)
      H, mH = torsion_subgroup(G)
      @test isisomorphic(H, DiagonalGroup([5, 4]))
    end 

    @testset "Subgroup" begin
      @test_throws ErrorException sub(GrpAbFinGenElem[])

      G = AbelianGroup(FlintZZ[3 0 0 ; 0 15 0])
      g1 = G[1]
      g2 = G[2]
      g3 = G[3]
      S, S_map = @inferred sub([g1, g2, g3])
      @test isisomorphic(G, S)

      G = AbelianGroup(FlintZZ[3 0 0 ; 0 15 0])
      S, mS = snf(G)
      s1 = S[1]
      s2 = S[2]
      s3 = S[3]
      H, mH = @inferred sub(S, [s1, s2, s3])
      @test isisomorphic(H, G)

      G = AbelianGroup(FlintZZ[3 0 0 ; 0 15 0])
      g1 = G[1]
      H, mH = @inferred sub(G, [g1])
      @test isisomorphic(H, DiagonalGroup([3]))

      G = AbelianGroup(FlintZZ[3 0 0 ; 0 15 0])
      S, mS = snf(G)
      s1 = S[1]
      H, mH = @inferred sub(S, [s1])
      @test isisomorphic(H, DiagonalGroup([3]))

      # G contains empty relation
      G = AbelianGroup(FlintZZ[3 0 0 ; 0 15 0 ; 0 0 30 ; 0 0 0])
      g1 = G[3]
      S, mS = @inferred sub(G, [g1])
      @test isisomorphic(S, DiagonalGroup([30]))

      # n*G

      G = DiagonalGroup([6, 6, 12, 5])
      H, mH = @inferred sub(G, 2)
      @test isisomorphic(H, DiagonalGroup([3, 3, 6, 5]))

      H, mH = @inferred sub(G, fmpz(2))
      @test isisomorphic(H, DiagonalGroup([3, 3, 6, 5]))
    end

    @testset "Quotient" begin
      G = AbelianGroup(FlintZZ[3 0 0 ; 0 15 0])

      Q, mQ = @inferred quo(G, GrpAbFinGenElem[])
      @test isisomorphic(Q, G)

      g2 = G[2]
      Q, mQ = @inferred quo(G, [g2])
      @test isisomorphic(Q, DiagonalGroup([3, 0]))

      S = DiagonalGroup([3, 15, 0])
      @test issnf(S)
      g2 = S[2]
      Q, mQ = @inferred quo(S, [g2])
      @test isisomorphic(Q, DiagonalGroup([3, 0]))

      G = DiagonalGroup([6, 6, 12, 5, 0])
      H, mH = @inferred quo(G, 2)
      @test isisomorphic(H, DiagonalGroup([2, 2, 2, 2]))

      H, mH = @inferred quo(G, fmpz(2))
      @test isisomorphic(H, DiagonalGroup([2, 2, 2, 2]))
    end

    @testset "Cyclic" begin
      G = DiagonalGroup([3, 5])
      @test @inferred iscyclic(G)

      G = DiagonalGroup([3, 15])
      @test @inferred !iscyclic(G)
    end

    @testset "p-Sylow subgroup" begin
      G = DiagonalGroup([1, 3, 9, 5, 15, 20, 7])
      P, mP = psylow_subgroup(G, 3)
      @test order(P) == 3^valuation(order(G), 3)
      P, mP = psylow_subgroup(G, 5)
      @test order(P) == 5^valuation(order(G), 5)
      P, mP = psylow_subgroup(G, 11)
      @test order(P) == 11^valuation(order(G), 11)
    end
  end
end
