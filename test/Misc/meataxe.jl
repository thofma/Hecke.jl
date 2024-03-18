@testset "Meataxe" begin

  finite_field_functions = [
    n -> GF(n),
    n -> GF(ZZ(n)),
    n -> finite_field(n, 1, "a")[1],
    n -> finite_field(ZZ(n), 1, "a")[1]
  ]
  finite_fields = 3 .|> finite_field_functions
  infinite_fields = [QQ, number_field(ZZPolyRingElem(ZZRingElem[-1,-1,1]))[1]]

  @testset "$(typeof(F))" for F in [finite_fields; infinite_fields]
    @testset "cleanvect" begin
      M=matrix_space(F,2,3)([1,1,0,0,1,0])
      v=matrix_space(F,1,3)([2,2,0])
      @test iszero(Hecke.cleanvect(M,v))
      v[1,3]=1
      @test !iszero(Hecke.cleanvect(M,v))
    end

    @testset "closure and spinning" begin
      G=[matrix_space(F,4,4)([1,2,0,0,1,1,0,0,0,0,1,2,0,0,1,1])]
      M=Hecke.Amodule(G)
      v=matrix_space(F,1,4)([1,0,0,0])
      X=Hecke.closure(v,M.action_of_gens)
      @test nrows(X)==2
      w=matrix_space(F,1,4)([0,0,0,1])
      v=vcat(v,w)
      @test nrows(Hecke.closure(v,M.action_of_gens))==4
    end

    @testset "meataxe" begin
      G=[matrix_space(F,4,4)([1,2,0,0,1,1,0,0,0,0,1,2,0,0,1,1])]
      M=Hecke.Amodule(G)
      bool,B=meataxe(M)
      @test !bool
      @test nrows(B)==2
      #@test nrows(Hecke.closure(B, M.action_of_gens))==2

      N=Hecke._actsub(B,G)
      bool,B=meataxe(N)
      @test bool

      G=[matrix_space(F,3,3)([1,0,0,0,0,1,0,1,0]), matrix_space(F,3,3)([0,0,1,1,0,0,0,1,0])]
      M=Hecke.Amodule(G)
      bool,B=meataxe(M)
      @test !bool
      #@test nrows(Hecke.closure(B, M.action_of_gens))==nrows(B)
    end

    @testset "composition factors and series" begin
      G=[matrix_space(F,4,4)([1,2,0,0,1,1,0,0,0,0,1,2,0,0,1,1])]
      M=Hecke.Amodule(G)

      lf=Hecke.composition_factors_with_multiplicity(M)
      @test length(lf)==1

      cs=composition_series(M)
      @test length(cs)==2

      x=Hecke._actsub(cs[1],M.action_of_gens)
      @test Hecke.is_isomorphic(lf[1][1],x)
      x,_=Hecke._actquo(cs[1],M.action_of_gens)
      @test Hecke.is_isomorphic(lf[1][1],x)
    end
  end

  @testset "Module Isomorphism" begin
    @testset "$(typeof(F))" for F in finite_fields
      # TODO also for infinite fields
      M=Hecke.Amodule([matrix(F,2,2,[0,1,2,0])])
      N=Hecke.Amodule([matrix(F,2,2,[0,2,1,0])])
      M.is_irreducible= 1
      @test Hecke.is_isomorphic(M,N)

      M1=matrix(F,2,2,[1,0,1,1])
      M2=matrix(F,2,2,[1,1,0,1])
      M=Hecke.Amodule([M1,M2])
      M.is_irreducible=1

      N1=matrix(F,2,2,[2,2,1,0])
      N2=matrix(F,2,2,[1,1,0,1])
      N=Hecke.Amodule([N1,N2])

      @test Hecke.is_isomorphic(M,N)
    end
  end

  @testset "Submodules" begin
    @testset "$(typeof(f(3)))" for f in finite_field_functions
      A=matrix_space(f(3),3,3)(1)
      M=Hecke.Amodule([A])
      ls=minimal_submodules(M)
      @test length(ls)==13

      A=matrix_space(f(2),6,6)(1)
      A[5,6]=1
      M=Hecke.Amodule([A])
      ls=minimal_submodules(M)
      @test length(ls)==31
      ls=submodules(M,4)
      @test length(ls)==171
    end
  end

  k = GF(3)
  Mat = matrix_algebra(k, [k[1 0; 0 1]])
  Mod = Hecke.regular_module(Mat)
  @test length(maximal_submodules(Mod)) == 1
end
