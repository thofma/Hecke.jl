@testset "GrpAbFinGen" begin
  @testset "Type stuff" begin
    @test elem_type(GrpAbFinGen) == GrpAbFinGenElem
    @test parent_type(GrpAbFinGenElem) == GrpAbFinGen
  end

  @testset "Constructor" begin
    M1 = matrix(FlintZZ, 2, 3, [1, 2, 3, 4, 5, 6])
    G = @inferred abelian_group(M1)
    @test isa(G, GrpAbFinGen)
    @test G.rels == M1

    M = FlintZZ[1 2 3; 4 5 6] # fmpz_mat
    G = @inferred abelian_group(M)
    @test isa(G, GrpAbFinGen)
    @test G.rels == M1

    M = fmpz[1 2 3; 4 5 6]
    G = @inferred abelian_group(M)
    @test isa(G, GrpAbFinGen)
    @test G.rels == M1

    M = [1 2 3; 4 5 6]
    G = @inferred abelian_group(M)
    @test isa(G, GrpAbFinGen)
    @test G.rels == M1

    M = [3, 0]
    G = @inferred abelian_group(M)
    @test isa(G, GrpAbFinGen)

    M = fmpz[3, 0]
    G = @inferred abelian_group(M)
    @test isa(G, GrpAbFinGen)

    N = [3, 5]
    G = @inferred abelian_group(N)
    @test isa(G, GrpAbFinGen)
    @test G.rels == matrix(FlintZZ, 2, 2, [3, 0, 0, 5])

    N = fmpz[3, 5]
    G = @inferred abelian_group(N)
    @test isa(G, GrpAbFinGen)
    @test G.rels == matrix(FlintZZ, 2, 2, [3, 0, 0, 5])

    @test isabelian(G)
  end

  @testset "String I/O" begin
    G = abelian_group([ 3, 5 ])
    @test isa(string(G), String)
  end

  @testset "Field access" begin
    S = abelian_group([3, 0])
    @test @inferred issnf(S)
    @test @inferred ngens(S) == 2
    @test @inferred nrels(S) == 2
    @test @inferred rels(S) == matrix(FlintZZ, 2, 2, [3, 0, 0, 0])

    G = abelian_group([3, 5])
    @test @inferred !issnf(G)
    @test @inferred ngens(G) == 2
    @test @inferred nrels(G) == 2
    @test @inferred rels(G) == matrix(FlintZZ, 2, 2, [3, 0, 0, 5])
  end

  @testset "Hermite normal form" begin
    M   = FlintZZ[1 2 3; 4 5 6]
    HNF = FlintZZ[1 2 3; 0 3 6]
    G = abelian_group(M)
    Hecke.assure_has_hnf(G)
    @test G.hnf == HNF
  end

  @testset "Smith normal form" begin
    M = FlintZZ[16 17 2 ; 19 23 8 ; 16 17 2]
    G = abelian_group(M)
    S, mS = @inferred snf(G)
    @test issnf(S)
    @test S.snf == fmpz[45, 0]
    @test codomain(mS) == G
    @test domain(mS) == S

    M = FlintZZ[-4 0; 0 4]
    G = abelian_group(M)
    S, mS = @inferred snf(G)
    @test S.snf == fmpz[4, 4]
  end

  @testset "Finiteness" begin
    G = abelian_group([3, 15])
    @test issnf(G)
    @test @inferred isfinite(G)
    @test @inferred !isinfinite(G)

    G = abelian_group([3, 5])
    @test @inferred isfinite(G)
    @test @inferred !isinfinite(G)

    G = abelian_group([3, 15, 0])
    @test issnf(G)
    @test @inferred !isfinite(G)
    @test @inferred isinfinite(G)

    G = abelian_group([3, 5, 0])
    @test @inferred !isfinite(G)
    @test @inferred isinfinite(G)
  end

  @testset "Rank" begin
    G = abelian_group([3, 15])
    @test @inferred rank(G) == 0

    G = abelian_group([3, 5])
    @test @inferred rank(G) == 0

    G = abelian_group([3, 15, 0])
    @test @inferred rank(G) == 1

    G = abelian_group([3, 5, 0])
    @test @inferred rank(G) == 1
  end

  @testset "Order" begin
    G = abelian_group([3, 5])
    @test @inferred order(G) == 15
    G = abelian_group([3, 15])
    @test @inferred order(G) == 45
    G = abelian_group([3, 5, 0])
    @test_throws ErrorException order(G)
  end

  @testset "Exponent" begin
    G = abelian_group([3, 5])
    @test @inferred exponent(G) == 15
    G = abelian_group([3, 15])
    @test @inferred exponent(G) == 15
  end

  @testset "Trivial" begin
    G = abelian_group([1])
    @test @inferred istrivial(G)
    G = abelian_group([1, 1, 1])
    @test @inferred istrivial(G)
    G = abelian_group([3, 3])
    @test @inferred !istrivial(G)
    G = abelian_group([3, 5])
    @test @inferred !istrivial(G)
  end

  @testset "Isomorphism" begin
    b = @inferred isisomorphic(abelian_group(Int[]), abelian_group(Int[]))
    @test b

    G = abelian_group([2, 3, 5])
    H = abelian_group([30])
    @test @inferred isisomorphic(G, H)
  end

  @testset "Direct product" begin
    G = abelian_group([5, 3])
    H = abelian_group([4])
    K = direct_product(G, H)[1]
    @test isisomorphic(K, abelian_group([60]))
  end

  @testset "Torsion" begin
    G = abelian_group([5, 4])
    @test @inferred istorsion(G)
    H, mH = torsion_subgroup(G)
    @test order(H) == 20

    G = abelian_group([5, 0, 4, 0])
    @test @inferred !istorsion(G)
    H, mH = torsion_subgroup(G)
    @test isisomorphic(H, abelian_group([5, 4]))
  end

  @testset "Subgroup" begin
    @test_throws ErrorException sub(GrpAbFinGenElem[])

    G = abelian_group(FlintZZ[3 0 0 ; 0 15 0])
    g1 = G[1]
    g2 = G[2]
    g3 = G[3]
    S, S_map = @inferred sub([g1, g2, g3])
    @test isisomorphic(G, S)

    G = abelian_group(FlintZZ[3 0 0 ; 0 15 0])
    S, mS = snf(G)
    s1 = S[1]
    s2 = S[2]
    s3 = S[3]
    H, mH = @inferred sub(S, [s1, s2, s3])
    @test isisomorphic(H, G)

    G = abelian_group(FlintZZ[3 0 0 ; 0 15 0])
    g1 = G[1]
    H, mH = @inferred sub(G, [g1])
    @test isisomorphic(H, abelian_group([3]))

    G = abelian_group(FlintZZ[3 0 0 ; 0 15 0])
    S, mS = snf(G)
    s1 = S[1]
    H, mH = @inferred sub(S, [s1])
    @test isisomorphic(H, abelian_group([3]))

    # G contains empty relation
    G = abelian_group(FlintZZ[3 0 0 ; 0 15 0 ; 0 0 30 ; 0 0 0])
    g1 = G[3]
    S, mS = @inferred sub(G, [g1])
    @test isisomorphic(S, abelian_group([30]))

    # n*G

    G = abelian_group([6, 6, 12, 5])
    H, mH = @inferred sub(G, 2)
    @test isisomorphic(H, abelian_group([3, 3, 6, 5]))

    H, mH = @inferred sub(G, fmpz(2))
    @test isisomorphic(H, abelian_group([3, 3, 6, 5]))
    
    G = abelian_group([2, 2, 6, 6])
    H, mH = @inferred sub(G, 2)
    @test isisomorphic(H, abelian_group([3, 3]))
    H, mH = @inferred sub(G, 1)
    @test isisomorphic(H, G)
    H, mH = @inferred sub(G, 3)
    @test isisomorphic(H, abelian_group([2, 2, 2, 2]))
  end

  @testset "Quotient" begin
    G = abelian_group(FlintZZ[3 0 0 ; 0 15 0])

    Q, mQ = @inferred quo(G, GrpAbFinGenElem[])
    @test isisomorphic(Q, G)

    g2 = G[2]
    Q, mQ = @inferred quo(G, [g2])
    @test isisomorphic(Q, abelian_group([3, 0]))

    S = abelian_group([3, 15, 0])
    @test issnf(S)
    g2 = S[2]
    Q, mQ = @inferred quo(S, [g2])
    @test isisomorphic(Q, abelian_group([3, 0]))

    G = abelian_group([6, 6, 12, 5, 0])
    H, mH = @inferred quo(G, 2)
    @test isisomorphic(H, abelian_group([2, 2, 2, 2]))

    H, mH = @inferred quo(G, fmpz(2))
    @test isisomorphic(H, abelian_group([2, 2, 2, 2]))
  end

  @testset "Cyclic" begin
    G = abelian_group([3, 5])
    @test @inferred iscyclic(G)

    G = abelian_group([3, 15])
    @test @inferred !iscyclic(G)
  end

  @testset "p-Sylow subgroup" begin
    G = abelian_group([1, 3, 9, 5, 15, 20, 7])
    P, mP = psylow_subgroup(G, 3)
    @test order(P) == 3^valuation(order(G), 3)
    P, mP = psylow_subgroup(G, 5)
    @test order(P) == 5^valuation(order(G), 5)
    P, mP = psylow_subgroup(G, 11)
    @test order(P) == 11^valuation(order(G), 11)
  end

  @testset "pimary part" begin
    G = abelian_group([1, 2, 4, 6, 5])
    P, mP = primary_part(G, 2)
    @test order(P) == 2 * 4 * 2
    P, mP = primary_part(G, 6)
    @test order(P) == 2 * 4 * 6
    P, mP = primary_part(G, 9)
    @test order(P) == 3
  end

  @testset "All abelian groups" begin
    l = collect(abelian_groups(1))
    @test length(l) == 1
    l = collect(abelian_groups(2))
    @test length(l) == 1
    l = collect(abelian_groups(2^6 * 3^3 * 5^2 * 7))
    @test length(l) == 66
  end

  @testset "HomAlg" begin
    G = abelian_group([3 1; 0 3])
    S, mS = snf(G)
    H, mH = hom(G,G)
    T, p = tensor_product(G, G)
    D = direct_product(G, G, task = :none)
    for i=1:5
      Th = hom(T, T, map(mH, [rand(H) for x = 1:2])) #induced map in tensor product
      Dh = hom(D, D, map(mH, rand(H, (2,2)))) #induced map on direct prod
    end
    C = free_resolution(G)
    D = free_resolution(S)
    @test isexact(C)
    hom(D, C, mS)
    E = hom(D, T)
    @test 9 == prod(order(x) for x = homology(E))
    @test !isexact(E)
    E = hom(T, C)
    @test !isexact(E)
    E = tensor_product(C, T)
    @test !isexact(E)

    A = abelian_group([3 1; 0 3])
    B = abelian_group([9 2 1; 0 12 1; 0 0 25])
    C = abelian_group([3, 4, 0])
    @test isisomorphic(hom(tensor_product(A, B, task = :none), C)[1], 
                       hom(A, hom(B, C)[1])[1])
  end
  
  @testset "Complement" begin
    d = rand(2:1000)
    d1 = rand(2:1000)
    while !issquarefree(d) || !issquarefree(d1)
      d = rand(2:1000)
      d1 = rand(3:1000)
    end
    G = abelian_group(Int[d, d1])
    ls = subgroups(G)
    for s in ls
      @test Hecke.has_complement(s[2])[1]
    end
  end

  @testset "Diagonalize" begin

    local isdiagonal_subgroup
    function isdiagonal_subgroup(mHH::GrpAbFinGenMap)
      ord = fmpz(1)
      HH = domain(mHH)
      GG = codomain(mHH)
      for i = 1:ngens(GG)
        ss, mss = sub(GG, GrpAbFinGenElem[GG[i]])
        int, mint = intersect(mss, mHH)
        ord *= order(int)
      end
      return order(HH) == ord
    end
    invariants = Vector{Int}(undef, 3)
    for i = 1:3
      k = rand(1:5)
      invariants[i] = 2^k
    end
    G = abelian_group(invariants)
    subs = subgroups(G)
    for s in subs
      H, mH = s
      fl, new_gens = Hecke.isdiagonalisable(mH)
      if !fl
        continue
      end
      mS = inv(sub(G, new_gens)[2])
      @test isdiagonal(rels(codomain(mS)))
      @test isdiagonal_subgroup(mH*mS)
    end
  end

  @testset "Minimal subgroups" begin
    G = abelian_group([5, 5, 10])
    S = @inferred minimal_subgroups(G)
    @test length(S) == 32
    @test all(isprime(order(x[1])) for x in S)
  end
end
