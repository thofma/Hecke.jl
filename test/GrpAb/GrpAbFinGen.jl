@testset "FinGenAbGroup" begin
  @testset "Type stuff" begin
    @test elem_type(FinGenAbGroup) == FinGenAbGroupElem
    @test parent_type(FinGenAbGroupElem) == FinGenAbGroup
  end

  @testset "Constructor" begin
    M1 = matrix(FlintZZ, 2, 3, [1, 2, 3, 4, 5, 6])
    G = @inferred abelian_group(M1)
    @test isa(G, FinGenAbGroup)
    @test is_abelian(G)
    @test G.rels == M1

    G = @inferred abelian_group(FinGenAbGroup, M1)
    @test isa(G, FinGenAbGroup)
    @test is_abelian(G)
    @test G.rels == M1

    M = FlintZZ[1 2 3; 4 5 6] # ZZMatrix
    G = @inferred abelian_group(M)
    @test isa(G, FinGenAbGroup)
    @test is_abelian(G)
    @test G.rels == M1

    M = ZZRingElem[1 2 3; 4 5 6]
    G = @inferred abelian_group(M)
    @test isa(G, FinGenAbGroup)
    @test is_abelian(G)
    @test G.rels == M1

    M = [1 2 3; 4 5 6]
    G = @inferred abelian_group(M)
    @test isa(G, FinGenAbGroup)
    @test is_abelian(G)
    @test G.rels == M1

    M = [3, 0]
    G = @inferred abelian_group(M)
    @test isa(G, FinGenAbGroup)
    @test is_abelian(G)

    M = ZZRingElem[3, 0]
    G = @inferred abelian_group(M)
    @test isa(G, FinGenAbGroup)
    @test is_abelian(G)

    N = [3, 5]
    G = @inferred abelian_group(N)
    @test isa(G, FinGenAbGroup)
    @test is_abelian(G)
    @test G.rels == matrix(FlintZZ, 2, 2, [3, 0, 0, 5])

    N = ZZRingElem[3, 5]
    G = @inferred abelian_group(N)
    @test isa(G, FinGenAbGroup)
    @test is_abelian(G)
    @test G.rels == matrix(FlintZZ, 2, 2, [3, 0, 0, 5])

    G = @inferred free_abelian_group(2)
    @test isa(G, FinGenAbGroup)
    @test is_abelian(G)

    G = @inferred free_abelian_group(FinGenAbGroup, 2)
    @test isa(G, FinGenAbGroup)
    @test is_abelian(G)

  end

  @testset "String I/O" begin
    G = abelian_group([ 3, 5 ])
    @test isa(string(G), String)
  end

  @testset "Field access" begin
    S = abelian_group([3, 0])
    @test @inferred is_snf(S)
    @test @inferred ngens(S) == 2
    @test @inferred nrels(S) == 2
    @test @inferred rels(S) == matrix(FlintZZ, 2, 2, [3, 0, 0, 0])

    G = abelian_group([3, 5])
    @test @inferred !is_snf(G)
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
    @test is_snf(S)
    @test S.snf == ZZRingElem[45, 0]
    @test codomain(mS) == G
    @test domain(mS) == S

    M = FlintZZ[-4 0; 0 4]
    G = abelian_group(M)
    S, mS = @inferred snf(G)
    @test S.snf == ZZRingElem[4, 4]
  end

  @testset "Finiteness" begin
    G = abelian_group([3, 15])
    @test is_snf(G)
    @test @inferred isfinite(G)
    @test @inferred !is_infinite(G)

    G = abelian_group([3, 5])
    @test @inferred isfinite(G)
    @test @inferred !is_infinite(G)

    G = abelian_group([3, 15, 0])
    @test is_snf(G)
    @test @inferred !isfinite(G)
    @test @inferred is_infinite(G)

    G = abelian_group([3, 5, 0])
    @test @inferred !isfinite(G)
    @test @inferred is_infinite(G)
  end

  @testset "Rank" begin
    G = abelian_group([3, 15])
    @test @inferred torsion_free_rank(G) == 0
    #@test @inferred rank(G) == 2

    G = abelian_group([3, 5])
    @test @inferred torsion_free_rank(G) == 0
    #@test @inferred rank(G) == 1

    G = abelian_group([3, 15, 0])
    @test @inferred torsion_free_rank(G) == 1
    #@test @inferred rank(G) == 3

    G = abelian_group([3, 5, 0])
    @test @inferred torsion_free_rank(G) == 1
    #@test @inferred rank(G) == 2
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
    @test @inferred is_trivial(G)
    G = abelian_group([1, 1, 1])
    @test @inferred is_trivial(G)
    G = abelian_group([3, 3])
    @test @inferred !is_trivial(G)
    G = abelian_group([3, 5])
    @test @inferred !is_trivial(G)
  end

  @testset "Isomorphism" begin
    b = @inferred is_isomorphic(abelian_group(Int[]), abelian_group(Int[]))
    @test b

    G = abelian_group([2, 3, 5])
    H = abelian_group([30])
    @test @inferred is_isomorphic(G, H)
  end

  @testset "Direct product" begin
    G = abelian_group([5, 3])
    H = abelian_group([4])
    K = direct_product(G, H)[1]
    @test is_isomorphic(K, abelian_group([60]))
    K2 = direct_sum(H, G)[1]
    @test is_isomorphic(K, K2)
    K3, proj, inj = biproduct(G, H)
    for i in 1:2, j in 1:2
      if i == j
        @test is_injective(inj[i])
        @test is_surjective(proj[j])
        @test isone(compose(inj[i], proj[j]).map)
      else
        @test is_zero(compose(inj[i], proj[j]))
      end
    end
  end

  @testset "Torsion" begin
    G = abelian_group([5, 4])
    @test @inferred is_torsion(G)
    H, mH = torsion_subgroup(G)
    @test order(H) == 20

    G = abelian_group([5, 0, 4, 0])
    @test @inferred !is_torsion(G)
    H, mH = torsion_subgroup(G)
    @test is_isomorphic(H, abelian_group([5, 4]))
  end

  @testset "Freeness" begin
    G = abelian_group([0])
    @test @inferred is_free(G)
    G = abelian_group([2])
    @test @inferred !is_free(G)
    G = abelian_group([0, 2])
    @test @inferred !is_free(G)
    G = abelian_group(Int[])
    @test @inferred is_free(G)
  end

  @testset "Subgroup" begin
    @test_throws ErrorException sub(FinGenAbGroupElem[])

    G = abelian_group(FlintZZ[3 0 0 ; 0 15 0])
    g1 = G[1]
    g2 = G[2]
    g3 = G[3]
    S, S_map = @inferred sub([g1, g2, g3])
    @test is_isomorphic(G, S)

    G = abelian_group(FlintZZ[3 0 0 ; 0 15 0])
    S, mS = snf(G)
    s1 = S[1]
    s2 = S[2]
    s3 = S[3]
    H, mH = @inferred sub(S, [s1, s2, s3])
    @test is_isomorphic(H, G)

    G = abelian_group(FlintZZ[3 0 0 ; 0 15 0])
    g1 = G[1]
    H, mH = @inferred sub(G, [g1])
    @test is_isomorphic(H, abelian_group([3]))

    G = abelian_group(FlintZZ[3 0 0 ; 0 15 0])
    S, mS = snf(G)
    s1 = S[1]
    H, mH = @inferred sub(S, [s1])
    @test is_isomorphic(H, abelian_group([3]))

    # G contains empty relation
    G = abelian_group(FlintZZ[3 0 0 ; 0 15 0 ; 0 0 30 ; 0 0 0])
    g1 = G[3]
    S, mS = @inferred sub(G, [g1])
    @test is_isomorphic(S, abelian_group([30]))

    # n*G

    G = abelian_group([6, 6, 12, 5])
    H, mH = @inferred sub(G, 2)
    @test is_isomorphic(H, abelian_group([3, 3, 6, 5]))

    H, mH = @inferred sub(G, ZZRingElem(2))
    @test is_isomorphic(H, abelian_group([3, 3, 6, 5]))

    G = abelian_group([2, 2, 6, 6])
    H, mH = @inferred sub(G, 2)
    @test is_isomorphic(H, abelian_group([3, 3]))
    H, mH = @inferred sub(G, 1)
    @test is_isomorphic(H, G)
    H, mH = @inferred sub(G, 3)
    @test is_isomorphic(H, abelian_group([2, 2, 2, 2]))
  end

  @testset "Quotient" begin
    G = abelian_group(FlintZZ[3 0 0 ; 0 15 0])

    Q, mQ = @inferred quo(G, FinGenAbGroupElem[])
    @test is_isomorphic(Q, G)

    g2 = G[2]
    Q, mQ = @inferred quo(G, [g2])
    @test is_isomorphic(Q, abelian_group([3, 0]))

    S = abelian_group([3, 15, 0])
    @test is_snf(S)
    g2 = S[2]
    Q, mQ = @inferred quo(S, [g2])
    @test is_isomorphic(Q, abelian_group([3, 0]))

    G = abelian_group([6, 6, 12, 5, 0])
    H, mH = @inferred quo(G, 2)
    @test is_isomorphic(H, abelian_group([2, 2, 2, 2]))

    H, mH = @inferred quo(G, ZZRingElem(2))
    @test is_isomorphic(H, abelian_group([2, 2, 2, 2]))
  end

  @testset "Cyclic" begin
    G = abelian_group([3, 5])
    @test @inferred is_cyclic(G)

    G = abelian_group([1])
    @test @inferred is_cyclic(G)

    G = abelian_group([3, 15])
    @test @inferred !is_cyclic(G)
  end

  @testset "p-Sylow subgroup" begin
    G = abelian_group([1, 3, 9, 5, 15, 20, 7])
    P, mP = sylow_subgroup(G, 3)
    @test order(P) == 3^valuation(order(G), 3)
    P, mP = sylow_subgroup(G, 5)
    @test order(P) == 5^valuation(order(G), 5)
    P, mP = sylow_subgroup(G, 11)
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
    #=

    C, mC = free_resolution(G)
    push!(C, mC)
    push!(C, zero_map(G))
    D, mD = free_resolution(S)
    push!(D, mD)
    push!(D, zero_map(S))
    @test is_exact(C)
    hom(D, C, mS)
    E = hom(D, T)
    @test 9 == prod(order(x) for x = homology(E))
    @test !is_exact(E)
    E = hom(T, C)
    @test !is_exact(E)
    E = tensor_product(C, T)
    @test !is_exact(E)
  =#
    A = abelian_group([3 1; 0 3])
    B = abelian_group([9 2 1; 0 12 1; 0 0 25])
    C = abelian_group([3, 4, 0])
    @test is_isomorphic(hom(tensor_product(A, B, task = :none), C)[1],
                       hom(A, hom(B, C)[1])[1])
  end

  @testset "Complement" begin
    d = rand(2:1000)
    d1 = rand(2:1000)
    while !is_squarefree(d) || !is_squarefree(d1)
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
    function isdiagonal_subgroup(mHH::FinGenAbGroupHom)
      ord = ZZRingElem(1)
      HH = domain(mHH)
      GG = codomain(mHH)
      for i = 1:ngens(GG)
        ss, mss = sub(GG, FinGenAbGroupElem[GG[i]])
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
      fl, new_gens = Hecke.is_diagonalisable(mH)
      if !fl
        continue
      end
      mS = inv(sub(G, new_gens)[2])
      @test is_diagonal(rels(codomain(mS)))
      @test isdiagonal_subgroup(mH*mS)
    end
  end

  @testset "Minimal subgroups" begin
    G = abelian_group([5, 5, 10])
    S = @inferred minimal_subgroups(G)
    @test length(S) == 32
    @test all(is_prime(order(x[1])) for x in S)
  end

  @testset "Neat and Pure" begin
    G = abelian_group([2, 8])
    U = sub(G, [G[1]+2*G[2]])[1]
    @test is_neat(U, G)
    @test !is_pure(U, G)
    V = saturate(U, G)
    @test is_pure(V, G)
    @test has_complement(V, G)[1]
  end
end
