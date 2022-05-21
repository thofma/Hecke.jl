@testset "Meataxe" begin
  @testset "$(typeof(f(3)))" for f in [n -> GF(Int(n)), n -> GF(n), n -> FiniteField(n, 1, "a")[1], n -> FiniteField(fmpz(n), 1, "a")[1]]
    F = f(3)
    @testset "cleanvect" begin
      M=MatrixSpace(F,2,3)([1,1,0,0,1,0])
      v=MatrixSpace(F,1,3)([2,2,0])
      @test iszero(Hecke.cleanvect(M,v))
      v[1,3]=1
      @test !iszero(Hecke.cleanvect(M,v))

    end

    @testset "closure and spinning" begin
     G=[MatrixSpace(F,4,4)([1,2,0,0,1,1,0,0,0,0,1,2,0,0,1,1])]
     M=Hecke.Module(G)
     v=MatrixSpace(F,1,4)([1,0,0,0])
     X=Hecke.closure(v,M.action_of_gens)
     @test nrows(X)==2
     w=MatrixSpace(F,1,4)([0,0,0,1])
     v=vcat(v,w)
     @test nrows(Hecke.closure(v,M.action_of_gens))==4

    end

    @testset "meataxe" begin
      G=[MatrixSpace(F,4,4)([1,2,0,0,1,1,0,0,0,0,1,2,0,0,1,1])]
      M=Hecke.Module(G)
      bool,B=meataxe(M)
      @test !bool
      @test nrows(B)==2
      #@test nrows(Hecke.closure(B, M.action_of_gens))==2

      N=Hecke._actsub(B,G)
      bool,B=meataxe(N)
      @test bool

      G=[MatrixSpace(F,3,3)([1,0,0,0,0,1,0,1,0]), MatrixSpace(F,3,3)([0,0,1,1,0,0,0,1,0])]
      M=Hecke.Module(G)
      bool,B=meataxe(M)
      @test !bool
      #@test nrows(Hecke.closure(B, M.action_of_gens))==nrows(B)

    end

    @testset "composition factors and series" begin
      G=[MatrixSpace(F,4,4)([1,2,0,0,1,1,0,0,0,0,1,2,0,0,1,1])]
      M=Hecke.Module(G)
      lf=Hecke.composition_factors_with_multiplicity(M)
      cs=composition_series(M)
      @test length(lf)==1
      @test length(cs)==2
       x=Hecke._actsub(cs[1],M.action_of_gens)
      @test Hecke.is_isomorphic(lf[1][1],x)
       x,_=Hecke._actquo(cs[1],M.action_of_gens)
      @test Hecke.is_isomorphic(lf[1][1],x)

      M=Hecke.Module([matrix(F,2,2,[0,1,2,0])])
      N=Hecke.Module([matrix(F,2,2,[0,2,1,0])])
      M.is_irreducible= 1
      @test Hecke.is_isomorphic(M,N)


      M1=matrix(F,2,2,[1,0,1,1])
      M2=matrix(F,2,2,[1,1,0,1])
      M=Hecke.Module([M1,M2])
      M.is_irreducible= 1

      N1=matrix(F,2,2,[2,2,1,0])
      N2=matrix(F,2,2,[1,1,0,1])
      N=Hecke.Module([N1,N2])

      @test Hecke.is_isomorphic(M,N)

    end

    @testset "Submodules" begin
      A=MatrixSpace(F,3,3)(1)
      M=Hecke.Module([A])
      ls=minimal_submodules(M)
      @test length(ls)==13

      F = f(2) #FiniteField(2, 1, "a")
      A=MatrixSpace(F,6,6)(1)
      A[5,6]=1
      M=Hecke.Module([A])
      ls=minimal_submodules(M)
      @test length(ls)==31
      ls=submodules(M,4)
      @test length(ls)==171
    end
  end

end
