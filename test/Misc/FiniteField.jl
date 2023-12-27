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
    F = finite_field(p, 2)[1]
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
    _ = finite_field(ZZRingElem(p), 2, "a")[1]
    _ = finite_field(ZZRingElem(p), 2, 'a')[1]
    F = finite_field(ZZRingElem(p), 2, :a)[1]
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
    _ = GF(ZZRingElem(p), 2, "a")
    _ = GF(ZZRingElem(p), 2, 'a')
    F = GF(ZZRingElem(p), 2, :a)
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

@testset "SplittingField - FinField" begin
  k = GF(3)
  kt, t = k["t"]
  K = splitting_field(t^6-2)
  @test absolute_degree(K) == 2
  K, r = splitting_field(t^6-2, do_roots = true)
  @test length(r) == 2
  
  K = splitting_field(t^6-t-1)
  @test degree(K) == 6

  Ks,s = K["s"]
  E, r = splitting_field(s^5-5*s+2*s^2+1, do_roots = true)

  @test absolute_degree(E) == 30
  @test length(r) == 5
end  


