@testset "AVLTrees" begin
  let
    t = Hecke.AVLTree{Int}()
    for i in 100:-1:1
      insert!(t, i)
    end

    @test length(t) == 100

    for i in 1:100
      @test haskey(t, i)
    end

    for i = 101:150
      @test !haskey(t, i)
    end
  end

  let
    t = Hecke.AVLTree{Int}()
    for i in 1:100
      insert!(t, i)
    end
    for i in 1:2:100
      delete!(t, i)
    end

    @test length(t) == 50

    for i in 1:100
      if iseven(i)
        @test haskey(t, i)
      else
        @test !haskey(t, i)
      end
    end

    for i in 1:2:100
      insert!(t, i)
    end

    @test length(t) == 100
  end

  let
    t2 = Hecke.AVLTree{Int}()
    for i in 1:100000
      insert!(t2, i)
    end

    @test length(t2) == 100000

    nums = rand(1:100000, 8599)
    visited = Set()
    for num in nums
      if !(num in visited)
        delete!(t2, num)
        push!(visited, num)
      end
    end

    for i in visited
      @test !haskey(t2, i)
    end
    @test (length(t2) + length(visited)) == 100000
  end

  let
    nums = rand(1:100000, 1000)
    t3 = Hecke.AVLTree{Int}()
    uniq_nums = Set(nums)
    for num in uniq_nums
      insert!(t3, num)
    end
    @test length(t3) == length(uniq_nums)
  end

  let
    t4 = Hecke.AVLTree{Char}()
    push!(t4, 'a')
    push!(t4, 'b')
    @test length(t4) == 2
    @test in('a', t4)
    @test !in('c', t4)
  end

  let
    t5 = Hecke.AVLTree{Int}()
    for i in 1:32
      push!(t5, i)
    end
    n1 = Hecke.search_node(t5, 21)
    @test n1.data == 21
    n2 = Hecke.search_node(t5, 35)
    @test n2.data == 32
    n3 = Hecke.search_node(t5, 0)
    @test n3.data == 1
  end

  let
    t6 = Hecke.AVLTree{Int}()
    for i in 1:10
      push!(t6, i)
    end
    for i in 1:10
      @test Hecke._getindex(t6, i) == i
    end
    @test_throws BoundsError Hecke._getindex(t6, 0)
    @test_throws BoundsError Hecke._getindex(t6, 11)
  end

  let
    t8 = Hecke.AVLTree{Int}()
    @test Hecke.minimum_node(t8.root) == nothing
    for i in 1:32
      push!(t8, i)
    end
    m1 = Hecke.minimum_node(t8.root)
    @test m1.data == 1
    node = t8.root
    while node.left_child != nothing
      m = Hecke.minimum_node(node.left_child)
      @test m == m1
      node = node.left_child
    end
  end

  let
    t9 = Hecke.AVLTree{Int}()
    for i in 1:20
      push!(t9, i)
    end
    for i in 1:20
      @test Hecke.sorted_rank(t9, i) == i
    end
    @test_throws KeyError Hecke.sorted_rank(t9, 21)
  end

  let
    t10 = Hecke.AVLTree{ZZRingElem}()
    for i in 20:-3:1
      push!(t10, ZZ(i))
    end
    @test haskey(t10, ZZ(17))
    @test !haskey(t10, ZZ(19))
    @test [a for a in t10] == (ZZ.(sort!(collect(20:-3:1))))
  end

  let
    t11 = Hecke.AVLTree{ZZRingElem}(>, ==)
    for i in 1:3:20
      push!(t11, ZZ(i))
    end
    @test haskey(t11, ZZ(7))
    @test !haskey(t11, ZZ(2))
    @test [a for a in t11] == reverse!(ZZ.(collect(1:3:20)))
  end

  let
    t12 = Hecke.AVLTree{Tuple{Int, ZZRingElem}}((x, y) -> x[2] > y[2], (x, y) -> x[2] == y[2])
    for i in 1:3:20
      push!(t12, (1, ZZ(i)))
    end
    @test haskey(t12, (1, ZZ(7)))
    @test !haskey(t12, (1, ZZ(2)))
    @test [a for a in t12] == [(1, a) for a in reverse!(ZZ.(collect(1:3:20)))]
  end
end
