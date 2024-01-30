@testset "ZpnGModules" begin

  @testset "Minimal Submodules" begin

    F, a = finite_field(3,1,"a")
    R = residue_ring(FlintZZ,9)[1]

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
  end


  @testset "Dual Module" begin

    R=residue_ring(FlintZZ,9)[1]
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

  end


  @testset "submodules with given structure" begin

    R=residue_ring(FlintZZ,8)[1]
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

    R=residue_ring(FlintZZ,4)[1]
    V=abelian_group([2,2,4])
    V.is_snf=true
    V.snf=[2,2,4]
    A=matrix_space(R,3,3)(1)
    M=ZpnGModule(V,[A])
    ls=submodules(M)
    lsub=subgroups(V)
    @test length(collect(ls))==length(collect(lsub))

  end


end
