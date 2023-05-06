@testset "fpField" begin

  for p in [31, 11, 101]
    F = GF(p)
    G, mG = unit_group(F)
    #Test generator
    g = mG(G[1])
    g1 = g
    for i = 2:p-2
      g1 *= g
      @test !isone(g1)
    end
    for i = 1:5
      x = rand(F)
      while iszero(x)
        x = rand(F)
      end
      elG = mG\x
      @test mG(elG) == x
    end

    G1, mG1 = unit_group(F, n_quo = 5)
    @test order(G1) == 5
    g = mG1(G1[1])
    g = g^(div(order(F)-1, 5))
    @test !isone(g)
    for i = 1:5
      x = rand(F)
      while iszero(x)
        x = rand(F)
      end
      c = mG1\x
      el = mG1(c)
      if el != x
        dl = mG\(el*inv(x))
        @test iszero(mod(dl[1], 5))
      end
    end
  end
end


@testset "FpField" begin

  for p in [31, 11, 101]
    F = GF(ZZRingElem(p))
    G, mG = unit_group(F)
    #Test generator
    g = mG(G[1])
    g1 = g
    for i = 2:p-2
      g1 *= g
      @test !isone(g1)
    end
    for i = 1:5
      x = rand(F)
      while iszero(x)
        x = rand(F)
      end
      elG = mG\x
      @test mG(elG) == x
    end

    G1, mG1 = unit_group(F, n_quo = 5)
    @test order(G1) == 5

    g = mG1(G1[1])
    g = g^(div(order(F)-1, 5))
    @test !isone(g)
    for i = 1:5
      x = rand(F)
      while iszero(x)
        x = rand(F)
      end
      c = mG1\x
      el = mG1(c)
      if el != x
        dl = mG\(el*inv(x))
        @test iszero(mod(dl[1], 5))
      end
    end
  end
end

@testset "fqPolyRepField" begin

  for p in [31, 11, 101]
    F = FiniteField(p, 2)[1]
    G, mG = unit_group(F)
    #Test generator
    g = mG(G[1])
    g1 = g
    for i = 2:p^2-2
      g1 *= g
      @test !isone(g1)
    end
    for i = 1:5
      x = rand(F)
      while iszero(x)
        x = rand(F)
      end
      elG = mG\x
      @test mG(elG) == x
    end

    G1, mG1 = unit_group(F, n_quo = 5)
    @test order(G1) == 5
    g = mG1(G1[1])
    g = g^(div(order(F)-1, 5))
    @test !isone(g)

    for i = 1:5
      x = rand(F)
      while iszero(x)
        x = rand(F)
      end
      c = mG1\x
      el = mG1(c)
      if el != x
        dl = mG\(el*inv(x))
        @test iszero(mod(dl[1], 5))
      end
    end
  end
end

@testset "FqPolyRepField" begin

  for p in [31, 11, 101]
    _ = FiniteField(ZZRingElem(p), 2, "a")[1]
    _ = FiniteField(ZZRingElem(p), 2, 'a')[1]
    F = FiniteField(ZZRingElem(p), 2, :a)[1]
    G, mG = unit_group(F)
    #Test generator
    g = mG(G[1])
    g1 = g
    for i = 2:p^2-2
      g1 *= g
      @test !isone(g1)
    end
    for i = 1:5
      x = rand(F)
      while iszero(x)
        x = rand(F)
      end
      elG = mG\x
      @test mG(elG) == x
    end

    G1, mG1 = unit_group(F, n_quo = 5)
    @test order(G1) == 5
    g = mG1(G1[1])
    g = g^(div(order(F)-1, 5))
    @test !isone(g)

    for i = 1:5
      x = rand(F)
      while iszero(x)
        x = rand(F)
      end
      c = mG1\x
      el = mG1(c)
      if el != x
        dl = mG\(el*inv(x))
        @test iszero(mod(dl[1], 5))
      end
    end
  end
end

@testset "FqField" begin

  for p in [31, 11, 101]
    _ = Hecke.Nemo._GF(ZZRingElem(p), 2, "a")
    _ = Hecke.Nemo._GF(ZZRingElem(p), 2, 'a')
    F = Hecke.Nemo._GF(ZZRingElem(p), 2, :a)
    G, mG = unit_group(F)
    #Test generator
    g = mG(G[1])
    g1 = g
    for i = 2:p^2-2
      g1 *= g
      @test !isone(g1)
    end
    for i = 1:5
      x = rand(F)
      while iszero(x)
        x = rand(F)
      end
      elG = mG\x
      @test mG(elG) == x
    end

    G1, mG1 = unit_group(F, n_quo = 5)
    @test order(G1) == 5
    g = mG1(G1[1])
    g = g^(div(order(F)-1, 5))
    @test !isone(g)

    for i = 1:5
      x = rand(F)
      while iszero(x)
        x = rand(F)
      end
      c = mG1\x
      el = mG1(c)
      if el != x
        dl = mG\(el*inv(x))
        @test iszero(mod(dl[1], 5))
      end
    end
  end
end
