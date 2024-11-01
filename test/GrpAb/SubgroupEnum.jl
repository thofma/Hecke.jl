@testset "Subgroup enumeration" begin
  @testset "p-subgroups" begin
    G = abelian_group([9, 3, 3])
    H = abelian_group([9, 3, 3, 5, 7])

    GG = abelian_group([8])
    @test 4 == length(collect(subgroups(GG)))

    @testset "All subgroups" begin
      @test 50 == length(collect(psubgroups(G, 3)))
    end

    @testset "Given subgroup type" begin

      T = psubgroups(G, 3, subtype = [3])
      @test 0 == length(collect(T))

      T = psubgroups(G, 3, subtype = [1, 1, 1, 1])
      @test 0 == length(collect(T))

      T = psubgroups(G, 3, subtype = [2])
      @test 9 == length(collect(T))
      @test all([snf(t[1])[1].snf == ZZRingElem[9] for t in T])

      T = psubgroups(G, 3, subtype = [2])
      @test 9 == length(collect(T))
      @test all([snf(t[1])[1].snf == ZZRingElem[9] for t in T])

      T = psubgroups(G, 3, subtype = [1, 1])
      @test 13 == length(collect(T))
      @test all([snf(t[1])[1].snf == ZZRingElem[3, 3] for t in T])

      T = psubgroups(G, 3, subtype = Int[])
      @test 1 == length(collect(T))
      @test all([order(t[1]) == 1 for t in T])

      T = psubgroups(G, 3, subtype = Int[2, 1, 1])
      @test 1 == length(collect(T))
      @test all([snf(t[1])[1].snf == ZZRingElem[3, 3, 9] for t in T])

      TH = psubgroups(G, 3, subtype = [3])
      @test 0 == length(collect(TH))

      TH = psubgroups(G, 3, subtype = [1, 1, 1, 1])
      @test 0 == length(collect(TH))

      TH = psubgroups(G, 3, subtype = [2])
      @test 9 == length(collect(TH))
      @test all([snf(t[1])[1].snf == ZZRingElem[9] for t in TH])

      TH = psubgroups(G, 3, subtype = [2])
      @test 9 == length(collect(TH))
      @test all([snf(t[1])[1].snf == ZZRingElem[9] for t in TH])

      TH = psubgroups(G, 3, subtype = [1, 1])
      @test 13 == length(collect(TH))
      @test all([snf(t[1])[1].snf == ZZRingElem[3, 3] for t in TH])

      TH = psubgroups(G, 3, subtype = Int[])
      @test 1 == length(collect(TH))
      @test all([order(t[1]) == 1 for t in TH])

      TH = psubgroups(G, 3, subtype = Int[2, 1, 1])
      @test 1 == length(collect(TH))
      @test all([snf(t[1])[1].snf == ZZRingElem[3, 3, 9] for t in TH])
    end

    @testset "Given quotient type" begin
      T = psubgroups(G, 3, quotype = [2], fun = quo)
      @test 9 == length(collect(T))
      @test all([snf(t[1])[1].snf == ZZRingElem[9] for t in T])

      T = psubgroups(G, 3, quotype = [1, 1], fun = quo)
      @test 13 == length(collect(T))
      @test all([snf(t[1])[1].snf == ZZRingElem[3, 3] for t in T])

      T = psubgroups(G, 3, quotype = [2, 1, 1], fun = quo)
      @test 1 == length(collect(T))
      @test all([snf(t[1])[1].snf == ZZRingElem[3, 3, 9] for t in T])

      T = psubgroups(G, 3, quotype = Int[], fun = quo)
      @test 1 == length(collect(T))
      @test all([order(t[1]) == 1 for t in T])

      TH = psubgroups(G, 3, quotype = [2], fun = quo)
      @test 9 == length(collect(TH))
      @test all([snf(t[1])[1].snf == ZZRingElem[9] for t in TH])

      TH = psubgroups(G, 3, quotype = [1, 1], fun = quo)
      @test 13 == length(collect(TH))
      @test all([snf(t[1])[1].snf == ZZRingElem[3, 3] for t in TH])

      TH = psubgroups(G, 3, quotype = [2, 1, 1], fun = quo)
      @test 1 == length(collect(TH))
      @test all([snf(t[1])[1].snf == ZZRingElem[3, 3, 9] for t in TH])

      TH = psubgroups(G, 3, quotype = Int[], fun = quo)
      @test 1 == length(collect(TH))
      @test all([order(t[1]) == 1 for t in TH])
    end

    @testset "Given order" begin

      T = psubgroups(G, 3, order = 1)
      @test 1 == length(collect(T))
      @test all([order(t[1]) == 1 for t in T])

      T = psubgroups(G, 3, order = 3)
      @test 13 == length(collect(T))
      @test all([order(t[1]) == 3 for t in T])

      T = psubgroups(G, 3, order = 9)
      @test 22 == length(collect(T))
      @test all([order(t[1]) == 9 for t in T])

      T = psubgroups(G, 3, order = 81)
      @test 1 == length(collect(T))
      @test all([order(t[1]) == 81 for t in T])

      TH = psubgroups(G, 3, order = 1)
      @test 1 == length(collect(TH))
      @test all([order(t[1]) == 1 for t in TH])

      TH = psubgroups(G, 3, order = 3)
      @test 13 == length(collect(TH))
      @test all([order(t[1]) == 3 for t in TH])

      TH = psubgroups(G, 3, order = 9)
      @test 22 == length(collect(TH))
      @test all([order(t[1]) == 9 for t in TH])

      TH = psubgroups(G, 3, order = 81)
      @test 1 == length(collect(TH))
      @test all([order(t[1]) == 81 for t in TH])
    end

    @testset "Given index" begin

      T = psubgroups(G, 3, index = 1, fun = quo)
      @test 1 == length(collect(T))
      @test all([order(t[1]) == 1 for t in T])

      T = psubgroups(G, 3, index = 3, fun = quo)
      @test 13 == length(collect(T))
      @test all([order(t[1]) == 3 for t in T])

      T = psubgroups(G, 3, index = 9, fun = quo)
      @test 22 == length(collect(T))
      @test all([order(t[1]) == 9 for t in T])

      T = psubgroups(G, 3, index = 81, fun = quo)
      @test 1 == length(collect(T))
      @test all([order(t[1]) == 81 for t in T])

      TH = psubgroups(G, 3, index = 1, fun = quo)
      @test 1 == length(collect(TH))
      @test all([order(t[1]) == 1 for t in TH])

      TH = psubgroups(G, 3, index = 3, fun = quo)
      @test 13 == length(collect(TH))
      @test all([order(t[1]) == 3 for t in TH])

      TH = psubgroups(G, 3, index = 9, fun = quo)
      @test 22 == length(collect(TH))
      @test all([order(t[1]) == 9 for t in TH])

      TH = psubgroups(G, 3, index = 81, fun = quo)
      @test 1 == length(collect(TH))
      @test all([order(t[1]) == 81 for t in TH])
    end
  end

  @testset "Arbitrary groups" begin
    G = abelian_group([3, 5, 7, 9, 25])

    @test_throws ErrorException subgroups(G, index = 3, subtype = [3, 1])

    @testset "All subgroups" begin
      @test 280 == length(collect(subgroups(G)))
    end

    @test_throws ErrorException subgroups(G, index = 3, order = 2)

    @testset "Given subtype" begin
      T = subgroups(G, subtype = [25, 27])
      @test length(collect(T)) == 0

      T = subgroups(G, subtype = [25, 9, 3])
      @test 5 == length(collect(T))
      @test all([snf(t[1])[1].snf == ZZRingElem[3, 225] for t in T])

      T = subgroups(G, subtype = [5, 5, 9, 3])
      @test 1 == length(collect(T))
      @test all([snf(t[1])[1].snf == ZZRingElem[15, 45] for t in T])

      T = subgroups(G, subtype = [3, 5, 9, 5])
      @test 1 == length(collect(T))
      @test all([snf(t[1])[1].snf == ZZRingElem[15, 45] for t in T])

    end

    @testset "Given quotype" begin
      T = subgroups(G, quotype = [25, 27], fun = quo)
      @test 0 == length(collect(T))

      T = subgroups(G, quotype = [5, 7], fun = quo)
      @test 6 == length(collect(T))
      @test all([snf(t[1])[1].snf == ZZRingElem[35] for t in T])
    end

    @testset "Given order" begin
      T = subgroups(G, order = 5*7*3)
      @test 24 == length(collect(T))
      @test all([order(t[1]) == 5*7*3 for t in T])
    end

    @testset "Given index" begin
      T = subgroups(G, index = 7*3, fun = quo)
      @test 4 == length(collect(T))
      @test all([order(t[1]) == 7*3 for t in T])
    end
  end

  # test for no subgroups

  G = abelian_group([9, 3, 3])
  @test length(collect(subgroups(G; index = 2))) == 0
  @test length(collect(subgroups(G; order = 10001323))) == 0
  @test length(collect(subgroups(G; subtype = [6, 6, 6]))) == 0
  @test length(collect(subgroups(G; quotype = [6, 6, 6]))) == 0

  G = abelian_group([2])
  @test length(collect(subgroups(G; quotype = [3]))) == 0
end
