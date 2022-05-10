@testset "ZpnGModules" begin

  @testset "Minimal Submodules" begin

    F, a = FiniteField(3,1,"a")
    R = ResidueRing(FlintZZ,9)

    V=abelian_group([3,3,9,9])

    l=[1,1,3,0,2,1,3,3,1,1,1,1,0,0,0,1]
    l1=[1,1,1,0,2,1,1,1,0,0,1,1,0,0,0,1]
    A=MatrixSpace(R,4,4)(l)
    A1=MatrixSpace(F,4,4)(l1)

    M = ZpnGModule(V,[A])
    M1 = Hecke.Module([A1])

    ls = minimal_submodules(M)
    ls1 = minimal_submodules(M1)

    @test length(ls) == length(ls1)
    for y in ls
      @test Hecke.is_submodule(M,y)
    end
  end


  @testset "Dual Module" begin

    R=ResidueRing(FlintZZ,9)
    V=abelian_group([3,3,9,9])
    V.is_snf=true
    V.snf=[3,3,9,9]
    l=[1,1,3,0,2,1,3,3,1,1,1,1,0,0,0,1]
    A=MatrixSpace(R,4,4)(l)
    M=ZpnGModule(V,[A])
    N= Hecke.dual_module(M)
    ls=submodules(N)
    v=fmpz[3,3,1,1]
    for y in ls
      @test Hecke.is_submodule(M,Hecke._dualize(y,V,v))
    end

  end


  @testset "submodules with given structure" begin

    R=ResidueRing(FlintZZ,8)
    V=abelian_group([2,4,8,8])
    V.is_snf=true
    V.snf=[2,4,8,8]
    l=[1,2,4,0,1,1,0,2,1,1,1,1,0,2,0,1]
    l1=[1,0,0,0,0,3,4,2,1,0,0,1,0,0,1,0]
    l2=[1,0,0,4,1,1,0,0,0,2,1,0,1,1,1,1]
    A=MatrixSpace(R,4,4)(l)
    B=MatrixSpace(R,4,4)(l1)
    C=MatrixSpace(R,4,4)(l2)
    M=ZpnGModule(V,[A,B,C])
    ls=submodules(M,typesub=[2,3])
    y=subgroups(V,quotype=[4,8])

    mp1=Hecke.GrpAbFinGenMap(V,V,lift(A))
    mp2=Hecke.GrpAbFinGenMap(V,V,lift(B))
    mp3=Hecke.GrpAbFinGenMap(V,V,lift(C))
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

    R=ResidueRing(FlintZZ,4)
    V=abelian_group([2,2,4])
    V.is_snf=true
    V.snf=[2,2,4]
    A=MatrixSpace(R,3,3)(1)
    M=ZpnGModule(V,[A])
    ls=submodules(M)
    lsub=subgroups(V)
    @test length(collect(ls))==length(collect(lsub))

  end


end
