@testset "Meataxe" begin

  @testset "cleanvect" begin
  
    F, a = FiniteField(3, 1, "a")
    M=MatrixSpace(F,2,3)([1,1,0,0,1,0])
    v=MatrixSpace(F,1,3)([2,2,0])
    @test iszero(Hecke.cleanvect(M,v))
    v[1,3]=1
    @test !iszero(Hecke.cleanvect(M,v))
  
  end
  
  @testset "closure and spinning" begin
  
   F, a = FiniteField(3, 1, "a")
   G=[MatrixSpace(F,4,4)([1,2,0,0,1,1,0,0,0,0,1,2,0,0,1,1])]
   M=FqGModule(G)
   v=MatrixSpace(F,1,4)([1,0,0,0])
   X=Hecke.closure(v,M.G)
   Y=Hecke.spinning(v,M.G)
   @test rows(X)==2
   @test rows(Y)==2
   rref!(Y)
   @test X==Y
   w=MatrixSpace(F,1,4)([0,0,0,1])
   v=vcat(v,w)
   @test rows(Hecke.closure(v,M.G))==4
 
  end
  
  @testset "meataxe" begin
  
    F, a = FiniteField(3, 1, "a")
    G=[MatrixSpace(F,4,4)([1,2,0,0,1,1,0,0,0,0,1,2,0,0,1,1])]
    M=FqGModule(G)
    bool,B=meataxe(M)
    @test !bool
    @test rows(B)==2
    @test rows(Hecke.closure(B, M.G))==2
    
    N=Hecke.actsub(B,G)
    bool,B=meataxe(N)
    @test bool
    
    G=[MatrixSpace(F,3,3)([1,0,0,0,0,1,0,1,0]), MatrixSpace(F,3,3)([0,0,1,1,0,0,0,1,0])]
    M=FqGModule(G)
    bool,B=meataxe(M)
    @test !bool
    @test rows(Hecke.closure(B, M.G))==rows(B)
    
  end
  
  @testset "composition factors and series" begin
  
    F, a = FiniteField(3, 1, "a")
    G=[MatrixSpace(F,4,4)([1,2,0,0,1,1,0,0,0,0,1,2,0,0,1,1])]
    M=FqGModule(G)
    lf=composition_factors(M)
    cs=composition_series(M)
    @test length(lf)==1
    @test length(cs)==2
    x=Hecke.actsub(cs[1],M.G)
    @test Hecke.isisomorphic(lf[1][1],x)
  end
  
end



