@testset "Elements" begin
  @testset "Constructors" begin
    M = ZZ[1 2 3; 4 5 6]
    G = @inferred abelian_group(M)
    N = ZZ[1 2 3]
    a = @inferred FinGenAbGroupElem(G, N)
    @test parent(a) == G
    @test a.coeff == N
    @test a[begin:end] == [0, 0, 0]
    @test a[:] == [0, 0, 0]

    G = @inferred abelian_group([3, 0])
    N = ZZ[1 1]
    a = @inferred FinGenAbGroupElem(G, N)
    @test @inferred parent(a) == G
    @test a.coeff == N
    @test a[begin:end] == [1, 1]
    @test a[:] == [1, 1]

    N = matrix(ZZ, 1, 2, [ 1, 1 ])
    a = @inferred G(N)
    @test @inferred parent(a) == G
    @test a.coeff == N
    N = transpose(N)
    a = @inferred G(N)
    @test @inferred parent(a) == G
    @test a.coeff == transpose(N)
    @test a[begin:end] == [1, 1]
    @test a[:] == [1, 1]
  end

  @testset "Generators" begin
    M = ZZ[1 2 3; 4 5 6]
    G = abelian_group(M)
    ge = @inferred gens(G)
    @test length(ge) == 3
    @test ge[1] == G[1]
    @test ge[2] == G[2]
    @test ge[3] == G[3]
  end

  @testset "Parent" begin
    G = @inferred abelian_group([3, 0])
    N = ZZ[1 1]
    a = @inferred FinGenAbGroupElem(G, N)
    @test @inferred parent(a) == G
  end

  @testset "String I/O" begin
    G = abelian_group([3, 0])
    N = ZZ[1 1]
    a = FinGenAbGroupElem(G, N)
    @test isa(string(a), String)
  end

  @testset "Hashing" begin
    G = abelian_group([3, 0])
    N = ZZ[1 1]
    a = FinGenAbGroupElem(G, N)
    @test isa(hash(a), UInt)
  end

  @testset "Indexing" begin
    G = abelian_group([3, 0])
    N = ZZ[1 2]
    a = FinGenAbGroupElem(G, N)
    @test @inferred a[1] == 1
    @test @inferred a[2] == 2
  end

  @testset "Comparison" begin
    G = abelian_group([3, 0])
    N = ZZ[1 2]
    a = FinGenAbGroupElem(G, N)
    b = FinGenAbGroupElem(G, deepcopy(N))
    @test @inferred a == b

    H = abelian_group([3, 0])
    c = FinGenAbGroupElem(H, N)
    @test_throws ErrorException a == c
  end

  @testset "Arithmetic" begin
    G = abelian_group([3, 3, 3])
    a = G[1]
    b = G[2]
    c = G([1, 1, 0])
    @test a + b == c
    @test -a == G([2, 0, 0])

    aa = @inferred(2 * a)
    @test aa == G([2, 0, 0])

    aa = @inferred(a * 2)
    @test aa == G([2, 0, 0])


    aa = @inferred(ZZRingElem(2) * a)
    @test aa == G([2, 0, 0])
  end

  @testset "Unsafe operators" begin
    G = abelian_group([3, 3, 0])

    a = G([1, 2, 3])
    @test zero!(a) == G([0, 0, 0])
    @test a == G([0, 0, 0])

    a = G([1, 2, 3])
    @test neg!(a) == G([-1, -2, -3])
    @test a == G([-1, -2, -3])

    # TODO: set! not yet implemented
    #a = G([1, 2, 3])
    #@test Hecke.set!(a, G[1]) == G([1, 0, 0])
    #@test a == G([1, 0, 0])

    a = G([1, 2, 3])
    @test add!(a, a) == G([2, 1, 6])
    @test a == G([2, 1, 6])

    a = G([1, 2, 3])
    @test sub!(a, G([4, 4, 4])) == G([-3, -2, -1])
    @test a == G([-3, -2, -1])

    a = G([1, 2, 3])
    @test mul!(a, 4) == G([1, 2, 12])
    @test a == G([1, 2, 12])

    a = G([1, 2, 3])
    @test mul!(a, ZZ(4)) == G([1, 2, 12])
    @test a == G([1, 2, 12])

    a = G([1, 2, 3])
    @test addmul!(a, G([1,1,1]), 4) == G([2, 0, 7])
    @test a == G([2, 0, 7])

    a = G([1, 2, 3])
    @test addmul!(a, G([1,1,1]), ZZ(4)) == G([2, 0, 7])
    @test a == G([2, 0, 7])

    a = G([1, 2, 3])
    @test Hecke.addmul_delayed_reduction!(a, G([1,1,1]), ZZ(4)) != G([2, 0, 7])
    reduce!(a)
    @test a == G([2, 0, 7])

  end

  @testset "Neutral element" begin
    G = abelian_group([3, 3, 3])
    a = G[1]

    aa = @inferred(a * ZZRingElem(2))
    @test aa == G([2, 0, 0])

    @test !iszero(a)

    c = G([0, 0, 0])
    @test iszero(c)
  end

  @testset "Parent object overloading" begin
    G = abelian_group([3, 3, 3])
    a = @inferred G(ZZRingElem[1, 1, 1])
    @test parent(a) == G
    @test a.coeff == ZZ[1 1 1]

    a = @inferred G([1, 1, 1])
    @test parent(a) == G
    @test a.coeff == ZZ[1 1 1]

    M = ZZ[1 1 1]
    a = @inferred G(M)
    M[1, 1] = 3
    @test parent(a) == G
    @test a.coeff == ZZ[1 1 1]

    a = @inferred G[1]
    @test parent(a) == G
    @test a.coeff == ZZ[1 0 0]
  end

  @testset "Order" begin
    G = abelian_group([3, 3, 0])
    a = G[1]
    @test @inferred order(a) == 3

    G = abelian_group([3, 5, 0])
    a = G[1]
    @test @inferred order(a) == 3

    a = G[3]
    @test_throws ErrorException order(a)
  end

  @testset "Random elements" begin
    G = abelian_group([3, 5])
    a = @inferred rand(G)
    @test parent(a) == G

    G = abelian_group([3, 15])
    a = @inferred rand(G)
    @test parent(a) == G

    G = abelian_group([3, 0])
    @test_throws ErrorException rand(G)

    a = @inferred rand(G, 10)
    @test parent(a) == G
    @test -10 <= a[2] <= 10

    a = @inferred rand(G, ZZRingElem(10))
    @test parent(a) == G
    @test -10 <= a[2] <= 10

    G = abelian_group([3, 0, 5, 0])
    @test_throws ErrorException rand(G)

    a = @inferred rand(G, 10)
    @test parent(a) == G
    @test -10 <= a[2] <= 10
    @test -10 <= a[4] <= 10

    a = @inferred rand(G, ZZRingElem(10))
    @test parent(a) == G
    @test -10 <= a[2] <= 10
    @test -10 <= a[4] <= 10
  end

  @testset "Iterator" begin
    G = abelian_group([2, 0])
    @test_throws ErrorException begin for a in G end end
    G = abelian_group([ZZRingElem(2)^100])
    @test_throws ErrorException begin for a in G end end

    G = abelian_group([3, 5, 10])
    @test length(G) == 3*5*10
    @test length(collect(G)) == 3*5*10

    G = abelian_group([3, 9, 27])
    @test length(G) == 3*9*27
    @test length(collect(G)) == 3*9*27
  end


  @testset "Helper" begin
    @testset "Reduce mod Hermite normal form" begin
      a = ZZ[21 32 43]
      H = ZZ[2 0 0 ; 0 3 0 ; 0 0 5]
      Hecke.reduce_mod_hnf_ur!(a, H)
      @test a == ZZ[1 2 3]

      a = ZZ[1 3 42]
      H = ZZ[1 1 14 ; 0 2 11 ; 0 0 17]
      Hecke.reduce_mod_hnf_ur!(a, H)
      @test a == ZZ[0 0 0]

      a = ZZ[0 0 1]
      H = ZZ[1 32 62 ; 0 45 90 ; 0 0 0]
      Hecke.reduce_mod_hnf_ur!(a, H)
      @test a == ZZ[0 0 1]
    end

    @testset "Smith normal form with transform" begin
      M = matrix_space(ZZ,1,1)([0])
      S = matrix_space(ZZ,1,1)([0])
      T,L,R = snf_with_transform(M, true, true)
      @test S == T
      @test L*M*R == T

      M = matrix_space(ZZ,1,1)([1])
      S = matrix_space(ZZ,1,1)([1])
      T,L,R = snf_with_transform(M, true, true)
      @test S == T
      @test L*M*R == T

      M = ZZ[834 599 214 915 ; 784 551 13 628 ; 986 5 649 100 ; 504 119 64 310 ]
      S = ZZ[1 0 0 0 ; 0 1 0 0 ; 0 0 1 0 ; 0 0 0 36533330310]
      T,L,R = snf_with_transform(M, true, true)
      @test S == T
      @test L*M*R == T
      T,L,R = snf_with_transform(M, false, true)
      T,L,R = snf_with_transform(M, true, false)
      T,L,R = snf_with_transform(M, false, false)

      M = diagonal_matrix(ZZRingElem[-3, 5])
      T,L,R = snf_with_transform(M, true, true)
      @test L*M*R == T
    end
  end
end
