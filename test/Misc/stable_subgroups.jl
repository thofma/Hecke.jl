@testset "ZpnGModules" begin

  @testset "Minimal Submodules" begin

    F, a = finite_field(3,1,"a")
    R = residue_ring(ZZ,9)[1]

    V=abelian_group([3,3,9,9])

    l=[1,1,3,0,2,1,3,3,1,1,1,1,0,0,0,1]
    l1=[1,1,1,0,2,1,1,1,0,0,1,1,0,0,0,1]
    A=matrix_space(R,4,4)(l)
    A1=matrix_space(F,4,4)(l1)

    M = ZpnGModule(V,[A])
    M1 = Hecke.Amodule([A1])

    ls = minimal_submodules(M)
    ls1 = minimal_submodules(M1)

    @test length(ls) == length(ls1)
    for y in ls
      @test Hecke.is_submodule(M,y)
    end

    ls = maximal_submodules(M)
    ls1 = minimal_submodules(M1)

    @test length(ls) == length(ls1)
    for y in ls
      @test Hecke.is_submodule(M,y)
    end
  end


  @testset "Dual Module" begin

    R=residue_ring(ZZ,9)[1]
    V=abelian_group([3,3,9,9])
    V.is_snf=true
    V.snf=[3,3,9,9]
    l=[1,1,3,0,2,1,3,3,1,1,1,1,0,0,0,1]
    A=matrix_space(R,4,4)(l)
    M=ZpnGModule(V,[A])
    N= Hecke.dual_module(M)
    ls=submodules(N)
    v=ZZRingElem[3,3,1,1]
    for y in ls
      @test Hecke.is_submodule(M,Hecke._dualize(y,V,v))
    end
    @test length(ls) == 16
    @test issetequal(howell_form.(ls), map(x -> matrix(R, 4, 4, x),
      [[0 0 0 0; 0 0 0 0; 0 0 0 0; 0 0 0 0],
       [0 0 3 0; 0 0 0 0; 0 0 0 0; 0 0 0 0],
       [1 0 3 0; 0 1 6 0; 0 0 0 0; 0 0 0 0],
       [1 0 0 0; 0 1 0 0; 0 0 3 0; 0 0 0 0],
       [1 2 1 0; 0 0 3 0; 0 0 0 0; 0 0 0 0],
       [1 2 1 3; 0 0 3 0; 0 0 0 0; 0 0 0 0],
       [1 2 1 6; 0 0 3 0; 0 0 0 0; 0 0 0 0],
       [0 0 3 0; 0 0 0 3; 0 0 0 0; 0 0 0 0],
       [1 0 0 0; 0 1 0 0; 0 0 1 0; 0 0 0 0],
       [1 0 0 0; 0 1 0 0; 0 0 1 3; 0 0 0 0],
       [1 0 0 0; 0 1 0 0; 0 0 1 6; 0 0 0 0],
       [1 0 0 0; 0 1 0 0; 0 0 3 0; 0 0 0 3],
       [1 2 1 0; 0 0 3 0; 0 0 0 3; 0 0 0 0],
       [1 0 0 0; 0 1 0 0; 0 0 1 0; 0 0 0 3],
       [1 2 0 2; 0 0 1 1; 0 0 0 3; 0 0 0 0],
       [1 0 0 0; 0 1 0 0; 0 0 1 0; 0 0 0 1]]
     ))
  end


  @testset "submodules with given structure" begin

    R=residue_ring(ZZ,8)[1]
    V=abelian_group([2,4,8,8])
    V.is_snf=true
    V.snf=[2,4,8,8]
    l=[1,2,4,0,1,1,0,2,1,1,1,1,0,2,0,1]
    l1=[1,0,0,0,0,3,4,2,1,0,0,1,0,0,1,0]
    l2=[1,0,0,4,1,1,0,0,0,2,1,0,1,1,1,1]
    A=matrix_space(R,4,4)(l)
    B=matrix_space(R,4,4)(l1)
    C=matrix_space(R,4,4)(l2)
    M=ZpnGModule(V,[A,B,C])
    ls=submodules(M,typesub=[2,3])
    y=subgroups(V,quotype=[4,8])

    mp1=Hecke.FinGenAbGroupHom(V,V,lift(A))
    mp2=Hecke.FinGenAbGroupHom(V,V,lift(B))
    mp3=Hecke.FinGenAbGroupHom(V,V,lift(C))
    act=[mp1,mp2,mp3]

    i=0
    for el in y
      if Hecke.is_stable(act,el[2])
        i+=1
      end
    end
    @test i==length(ls)

    ls=submodules(M,typesub=[3])
    y=subgroups(V,quotype=[8])
    i=0
    for el in y
      if Hecke.is_stable(act,el[2])
        i+=1
      end
    end
    @test i==length(ls)

  end

  @testset "submodules" begin

    R=residue_ring(ZZ,4)[1]
    V=abelian_group([2,2,4])
    V.is_snf=true
    V.snf=[2,2,4]
    A=matrix_space(R,3,3)(1)
    M=ZpnGModule(V,[A])
    ls=submodules(M)
    lsub=subgroups(V)
    @test length(collect(ls))==length(collect(lsub))

  end

  let # cornercase
    A = abelian_group()
    g = id_hom(A)
    l = stable_subgroups(A,[g])
    ll = collect(l)
    @test length(ll) == 1
  end

  let # cornercase
    A = abelian_group([4,4])
    endo = hom(A,A,[2*i for i in gens(A)])
    s = stable_subgroups(A,[endo])
    @test length(s) == 15
  end

  @testset "Given subtype" begin
    for invariants in ([2, 2, 2], [4, 4], [2, 4, 12], [3, 2, 4])
      A = abelian_group(invariants)
      acts = [id_hom(A), hom(A, A, [zero(A); gens(A)[2:end]])]
      for t in (Int[], [1], [2], [2, 2], [4], [3, 2], invariants, [8], [5], [2, 2, 2, 2])
        expected = [(S, m) for (S, m) in subgroups(A, subtype = t) if Hecke.is_stable(acts, m)]
        actual = collect(stable_subgroups(A, acts, subtype = t))
        @test length(actual) == length(expected)
        @test all(is_isomorphic(S, abelian_group(t)) for (S, _) in actual)
        @test all(Hecke.is_stable(acts, m) for (_, m) in actual)
        @test Set(Set(m.(collect(S))) for (S, m) in actual) ==
              Set(Set(m.(collect(S))) for (S, m) in expected)
      end
    end

    A = abelian_group([4, 4])
    act = [id_hom(A)]
    t = [4, 2]
    collect(stable_subgroups(A, act, subtype = t))
    @test t == [4, 2]
    @test length(collect(stable_subgroups(A, act, subtype = [4], op = quo))) == 6
    B = abelian_group()
    @test length(collect(stable_subgroups(B, [id_hom(B)], subtype = Int[]))) == 1
    @test_throws ArgumentError stable_subgroups(A, act, subtype = [2], quotype = [2])
    @test_throws ArgumentError stable_subgroups(A, act, subtype = [2], order = 2)
    @test_throws ArgumentError stable_subgroups(A, act, subtype = [2], minimal = true)
    @test_throws ArgumentError stable_subgroups(A, act, subtype = [0])
    @test_throws ArgumentError stable_subgroups(A, act, subtype = [-2])
  end

  @testset "Given order" begin
    for invariants in ([2, 2, 2], [4, 4], [2, 4, 12], [3, 2, 4])
      A = abelian_group(invariants)
      act = [hom(A, A, [zero(A); gens(A)[2:end]])]
      for n in divisors(order(A))
        expected = [(S, m) for (S, m) in subgroups(A, order = n) if Hecke.is_stable(act, m)]
        actual = collect(stable_subgroups(A, act, order = n))
        @test length(actual) == length(expected)
        @test all(order(S) == n for (S, _) in actual)
        @test Set(Set(m.(collect(S))) for (S, m) in actual) ==
              Set(Set(m.(collect(S))) for (S, m) in expected)
      end
    end

    B = abelian_group()
    @test length(collect(stable_subgroups(B, [id_hom(B)], order = 1))) == 1
    B = abelian_group(fill(2, 70))
    s = collect(stable_subgroups(B, [id_hom(B)], order = 1))
    @test length(s) == 1
    @test order(first(s)[1]) == 1

    A = abelian_group([4, 4])
    g = id_hom(A)

    s = collect(stable_subgroups(A, [g], order = 4))
    @test length(s) == length(collect(subgroups(A, order = 4)))
    @test all(order(S) == 4 for (S, _) in s)

    s = collect(stable_subgroups(A, [g], order = 1))
    @test length(s) == 1
    @test order(first(s)[1]) == 1

    s = collect(stable_subgroups(A, [g], order = ZZ(4)))
    @test length(s) == length(collect(subgroups(A, order = 4)))

    s = collect(stable_subgroups(A, [g], order = 16))
    @test length(s) == 1
    @test order(first(s)[1]) == 16

    @test isempty(stable_subgroups(A, [g], order = 3))
    @test length(collect(stable_subgroups(A, [g], order = 4, op = quo))) == 7
    @test_throws ArgumentError stable_subgroups(A, [g], order = 0)
    @test_throws ArgumentError stable_subgroups(A, [g], order = 4, minimal = true)
    @test_throws ArgumentError stable_subgroups(A, [g], quotype = [4], order = 4)
  end
end
