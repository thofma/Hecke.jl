@testset "AbelianGrp" begin

  @testset "constructor FinGenGrpAbGen" begin
    @testset "not in hnf" begin
      M = ZZ[1 2 3; 4 5 6]        :: fmpz_mat
      G = Hecke.FinGenGrpAbGen(M) :: FinGenGrpAb
      @test G.rels == M
      @test_throws UndefRefError G.hnf
      @test_throws UndefRefError G.snf_map
    end

    @testset "in hnf" begin
      M = ZZ[1 2 3; 0 3 6]                     :: fmpz_mat
      G = Hecke.FinGenGrpAbGen(M, is_hnf=true) :: FinGenGrpAb
      @test G.rels == M
      @test G.hnf == M
      @test_throws UndefRefError G.snf_map
    end
  end

  @testset "constructor FinGenGrpAbSnf" begin
    A = Array{fmpz,1}([3 ; 15 ; 0])
    SNF = Hecke.FinGenGrpAbSnf(A)
    @test SNF.snf == A
  end

  @testset "constructor FinGenGrpAbElem" begin
    M = ZZ[1 2 3; 4 5 6]        :: fmpz_mat
    G = Hecke.FinGenGrpAbGen(M) :: FinGenGrpAb
    N = ZZ[1 2 3]               :: fmpz_mat
    a = Hecke.FinGenGrpAbElemCreate(G, N)
    @test a.parent == G
    @test a.coeff == N
  end

  @testset "parent" begin
    G = AbelianGroup(ZZ[1 2 3; 4 5 6])
    a = Hecke.FinGenGrpAbElemCreate(G, ZZ[0 1 0])
    @test parent(a) == G
  end

  @testset "ngens" begin
    @testset "Gen" begin
      G = AbelianGroup(ZZ[1 2 3; 4 5 6])
      @test ngens(G) == 3
    end

    @testset "Snf" begin
      A = Array{fmpz,1}([3 ; 0])
      SNF = Hecke.FinGenGrpAbSnf(A)
      @test ngens(SNF) == 2
    end
  end

  @testset "nrels" begin
    @testset "Gen" begin
      M = ZZ[1 2 3; 4 5 6]
      G = AbelianGroup(M)
      @test nrels(G) == 2
    end

    @testset "Snf" begin
      A = Array{fmpz,1}([3 ; 0])
      SNF = Hecke.FinGenGrpAbSnf(A)
      @test nrels(SNF) == 2
    end
  end

  @testset "getindex" begin
    G = AbelianGroup(ZZ[0 3 0])
    a = Hecke.FinGenGrpAbElemCreate(G, ZZ[0 4 0])
    @test getindex(a,1) == 0
    @test getindex(a,2) == 1
    @test getindex(a,3) == 0
  end

  @testset "assert_hnf" begin
    M   = ZZ[1 2 3; 4 5 6]
    HNF = ZZ[1 2 3; 0 3 6]
    G = AbelianGroup(M)
    Hecke.assert_hnf(G)
    @test G.hnf == HNF
  end

  @testset "reduce_mod_hnf" begin
    @testset "TODO" begin
      a = ZZ[21 32 43]
      H = ZZ[2 0 0 ; 0 3 0 ; 0 0 5]
      Hecke.reduce_mod_hnf!(a, H)
      @test a == ZZ[1 2 3]
    end

    @testset "TODO" begin
      a = ZZ[1 3 42]
      H = ZZ[1 1 14 ; 0 2 11 ; 0 0 17]
      Hecke.reduce_mod_hnf!(a, H)
      @test a == ZZ[0 0 0]
    end

    @testset "TODO" begin
      a = ZZ[0 0 1]
      H = ZZ[1 32 62 ; 0 45 90 ; 0 0 0]
      Hecke.reduce_mod_hnf!(a, H)
      @test a == ZZ[0 0 1]
    end
  end

  @testset "FinGenGrpAbElemCreate" begin
    @testset "Gen" begin
      G = AbelianGroup(ZZ[0 0 3])
      a = Hecke.FinGenGrpAbElemCreate(G, ZZ[0 2 4])
      @test parent(a) == G
      @test getindex(a,1) == 0
      @test getindex(a,2) == 2
      @test getindex(a,3) == 1
    end

    @testset "Snf" begin
      A = Array{fmpz,1}([3 ; 15 ; 0])
      SNF = Hecke.FinGenGrpAbSnf(A)
      a = Hecke.FinGenGrpAbElemCreate(SNF, ZZ[7 50 100])
      @test parent(a) == SNF
      @test getindex(a,1) == 1
      @test getindex(a,2) == 5
      @test getindex(a,3) == 100
    end
  end

  @testset "snf_with_transform" begin
    @testset "trivial" begin
      M = MatrixSpace(ZZ,1,1)([0])
      S = MatrixSpace(ZZ,1,1)([0])
      T,L,R = snf_with_transform(M,l=true,r=true)
      @test S == T
      @test L*M*R == T
    end

    @testset "trivial" begin
      M = MatrixSpace(ZZ,1,1)([1])
      S = MatrixSpace(ZZ,1,1)([1])
      T,L,R = snf_with_transform(M,l=true,r=true)
      @test S == T
      @test L*M*R == T
    end

    @testset "random" begin
      M = ZZ[834 599 214 915 ; 784 551 13 628 ; 986 5 649 100 ; 504 119 64 310 ]
      S = ZZ[1 0 0 0 ; 0 1 0 0 ; 0 0 1 0 ; 0 0 0 36533330310]
      T,L,R = snf_with_transform(M,l=true,r=true)
      @test S == T
      @test L*M*R == T
    end
  end

  @testset "snf" begin
    M = ZZ[16 17 2 ; 19 23 8 ; 16 17 2]
    G = AbelianGroup(M)
    SNF, SNF_map = snf(G)
    @test SNF.snf == Array{fmpz,1}([45 ; 0])
    @test SNF_map.header.domain == G
    @test SNF_map.header.codomain == SNF
    image = SNF_map.header.image
    preimage = SNF_map.header.preimage

    @testset "0 = 0" begin
      a = Hecke.FinGenGrpAbElemCreate(G, ZZ[0 0 0])
      b = Hecke.FinGenGrpAbElemCreate(SNF, ZZ[0 0])
      @test image(a) == b
      @test preimage(b) == a
    end

    @testset "0 != 100" begin
      a = Hecke.FinGenGrpAbElemCreate(G, ZZ[0 0 0])
      b = Hecke.FinGenGrpAbElemCreate(SNF, ZZ[100 100])
      @test image(a) != b
      @test preimage(b) != a
    end

    @testset "linearity" begin
      x = Hecke.FinGenGrpAbElemCreate(G, ZZ[234 4355 3455])
      y = Hecke.FinGenGrpAbElemCreate(G, ZZ[32 3090 34590])
      @test image(x+y) == image(x)+image(y)
      @test image(x-y) == image(x)-image(y)
      @test image(435*x) == 435*image(x)
    end
  end

  @testset "sub" begin
    @testset "S = G, Gen" begin
      G = AbelianGroup(ZZ[3 0 0 ; 0 15 0])
      g1 = Hecke.FinGenGrpAbElemCreate(G, ZZ[1 0 0])
      g2 = Hecke.FinGenGrpAbElemCreate(G, ZZ[0 1 0])
      g3 = Hecke.FinGenGrpAbElemCreate(G, ZZ[0 0 1])
      S , S_map = sub(G, [g1, g2, g3])
      image = S_map.header.image
      s1 = Hecke.FinGenGrpAbElemCreate(S, ZZ[1 0 0])
      s2 = Hecke.FinGenGrpAbElemCreate(S, ZZ[0 1 0])
      s3 = Hecke.FinGenGrpAbElemCreate(S, ZZ[0 0 1])
      @test S.hnf == G.hnf
      @test image(s1) == g1
      @test image(s2) == g2
      @test image(s3) == g3
      @test image(100*s1+456*s2-789*s3) == 100*g1+456*g2-789*g3
    end

    @testset "S = G, Snf" begin
      G = AbelianGroup(ZZ[3 0 0 ; 0 15 0])
      SNF, SNF_map = snf(G)
      snf1 = Hecke.FinGenGrpAbElemCreate(SNF, ZZ[1 0 0])
      snf2 = Hecke.FinGenGrpAbElemCreate(SNF, ZZ[0 1 0])
      snf3 = Hecke.FinGenGrpAbElemCreate(SNF, ZZ[0 0 1])
      S , S_map = sub(SNF, [snf1, snf2, snf3])
      image = S_map.header.image
      s1 = Hecke.FinGenGrpAbElemCreate(S, ZZ[1 0 0])
      s2 = Hecke.FinGenGrpAbElemCreate(S, ZZ[0 1 0])
      s3 = Hecke.FinGenGrpAbElemCreate(S, ZZ[0 0 1])
      @test image(s1) == snf1
      @test image(s2) == snf2
      @test image(s3) == snf3
      @test image(100*s1+456*s2-789*s3) == 100*snf1+456*snf2-789*snf3
    end

    @testset "S = <g1>, Gen" begin
      G = AbelianGroup(ZZ[3 0 0 ; 0 15 0])
      g1 = Hecke.FinGenGrpAbElemCreate(G, ZZ[1 0 0])
      S , S_map = sub(G, [g1])
      image = S_map.header.image
      s1 = Hecke.FinGenGrpAbElemCreate(S, MatrixSpace(ZZ,1,1)([4]))
      @test S.rels == MatrixSpace(ZZ,1,1)([3])
      @test image(s1) == g1
    end

    @testset "S = <g1>, Snf" begin
      G = AbelianGroup(ZZ[3 0 0 ; 0 15 0])
      SNF, SNF_map = snf(G)
      snf1 = Hecke.FinGenGrpAbElemCreate(SNF, ZZ[1 0 0])
      S , S_map = sub(SNF, [snf1])
      image = S_map.header.image
      s1 = Hecke.FinGenGrpAbElemCreate(S, MatrixSpace(ZZ,1,1)([4]))
      @test image(s1) == snf1
    end

    @testset "G contains empty relation" begin
      G = AbelianGroup(ZZ[3 0 0 ; 0 15 0 ; 0 0 30 ; 0 0 0])
      g1 = Hecke.FinGenGrpAbElemCreate(G, ZZ[0 0 1])
      S , S_map = sub(G, [g1])
      image = S_map.header.image
      s1 = Hecke.FinGenGrpAbElemCreate(S, MatrixSpace(ZZ,1,1)([1]))
      @test image(s1) == g1
    end
  end

  @testset "quo" begin
    G = AbelianGroup(ZZ[3 0 0 ; 0 15 0])
    g1 = Hecke.FinGenGrpAbElemCreate(G, ZZ[0 1 0])
    Q , Q_map = quo(G, [g1])
    SNF, SNF_map = snf(Q)
    @test SNF.snf == Array{fmpz,1}([3 ; 0])
  end
end
