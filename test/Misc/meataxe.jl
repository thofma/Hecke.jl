@testset "Meataxe" begin
  @testset "$(typeof(f(3)))" for f in [n -> ResidueRing(ZZ, n), n -> FiniteField(n, 1, "a")[1], n -> FiniteField(fmpz(n), 1, "a")[1]]
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
     M=Hecke.ModAlgAss(G)
     v=MatrixSpace(F,1,4)([1,0,0,0])
     X=Hecke.closure(v,M.action)
     Y=Hecke.spinning(v,M.action)
     @test rows(X)==2
     @test rows(Y)==2
     rref!(Y)
     @test X==Y
     w=MatrixSpace(F,1,4)([0,0,0,1])
     v=vcat(v,w)
     @test rows(Hecke.closure(v,M.action))==4
 
    end
    
    @testset "meataxe" begin
      G=[MatrixSpace(F,4,4)([1,2,0,0,1,1,0,0,0,0,1,2,0,0,1,1])]
      M=Hecke.ModAlgAss(G)
      bool,B=meataxe(M)
      @test !bool
      @test rows(B)==2
      @test rows(Hecke.closure(B, M.action))==2
      
      N=Hecke._actsub(B,G)
      bool,B=meataxe(N)
      @test bool
      
      G=[MatrixSpace(F,3,3)([1,0,0,0,0,1,0,1,0]), MatrixSpace(F,3,3)([0,0,1,1,0,0,0,1,0])]
      M=Hecke.ModAlgAss(G)
      bool,B=meataxe(M)
      @test !bool
      @test rows(Hecke.closure(B, M.action))==rows(B)
      
    end
    
    @testset "composition factors and series" begin
      G=[MatrixSpace(F,4,4)([1,2,0,0,1,1,0,0,0,0,1,2,0,0,1,1])]
      M=Hecke.ModAlgAss(G)
      lf=composition_factors(M)
      cs=composition_series(M)
      @test length(lf)==1
      @test length(cs)==2
      x=Hecke._actsub(cs[1],M.action)
      @test Hecke.isisomorphic(lf[1][1],x)
      x,_=Hecke._actquo(cs[1],M.action)
      @test Hecke.isisomorphic(lf[1][1],x)

      M=Hecke.ModAlgAss([matrix(F,2,2,[0,1,2,0])])
      N=Hecke.ModAlgAss([matrix(F,2,2,[0,2,1,0])])
      M.isirreducible= 1
      @test Hecke.isisomorphic(M,N)
      
      
      M1=matrix(F,2,2,[1,0,1,1])
      M2=matrix(F,2,2,[1,1,0,1])
      M=Hecke.ModAlgAss([M1,M2])
      M.isirreducible= 1
      
      N1=matrix(F,2,2,[2,2,1,0])
      N2=matrix(F,2,2,[1,1,0,1])
      N=Hecke.ModAlgAss([N1,N2])
    
      @test Hecke.isisomorphic(M,N)
      
    end
    
    @testset "Submodules" begin
      A=MatrixSpace(F,3,3)(1)
      M=Hecke.ModAlgAss([A])
      ls=minimal_submodules(M)
      @test length(ls)==13
      
      F = f(2) #Nemo.FiniteField(2, 1, "a")
      A=MatrixSpace(F,6,6)(1)
      A[5,6]=1
      M=Hecke.ModAlgAss([A])
      ls=minimal_submodules(M)
      @test length(ls)==31
      ls=submodules(M,4)
      @test length(ls)==171
    end
  end
  
  @testset "cleanvect" begin
    F, a = Nemo.FiniteField(3, 1, "a")
    M=MatrixSpace(F,2,3)([1,1,0,0,1,0])
    v=MatrixSpace(F,1,3)([2,2,0])
    @test iszero(Hecke.cleanvect(M,v))
    v[1,3]=1
    @test !iszero(Hecke.cleanvect(M,v))
  
  end
  
  @testset "closure and spinning" begin
  
   F, a = Nemo.FiniteField(3, 1, "a")
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
  
    F, a = Nemo.FiniteField(3, 1, "a")
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
  
    F, a = Nemo.FiniteField(3, 1, "a")
    G=[MatrixSpace(F,4,4)([1,2,0,0,1,1,0,0,0,0,1,2,0,0,1,1])]
    M=FqGModule(G)
    lf=composition_factors(M)
    cs=composition_series(M)
    @test length(lf)==1
    @test length(cs)==2
    x=Hecke.actsub(cs[1],M.G)
    @test Hecke.isisomorphic(lf[1][1],x)
    x,_=Hecke.actquo(cs[1],M.G)
    @test Hecke.isisomorphic(lf[1][1],x)

    M=FqGModule([matrix(F,2,2,[0,1,2,0])])
    N=FqGModule([matrix(F,2,2,[0,2,1,0])])
    M.isirreducible=true
    @test Hecke.isisomorphic(M,N)
    
    
    M1=matrix(F,2,2,[1,0,1,1])
    M2=matrix(F,2,2,[1,1,0,1])
    M=FqGModule([M1,M2])
    M.isirreducible=true
    
    N1=matrix(F,2,2,[2,2,1,0])
    N2=matrix(F,2,2,[1,1,0,1])
    N=FqGModule([N1,N2])
  
    @test Hecke.isisomorphic(M,N)
    
  end
  
  @testset "Submodules" begin
  
    F, a = Nemo.FiniteField(3, 1, "a")
    A=MatrixSpace(F,3,3)(1)
    M=FqGModule([A])
    ls=minimal_submodules(M)
    @test length(ls)==13
    
    F, a = Nemo.FiniteField(2, 1, "a")
    A=MatrixSpace(F,6,6)(1)
    A[5,6]=1
    M=FqGModule([A])
    ls=minimal_submodules(M)
    @test length(ls)==31
    ls=submodules(M,4)
    @test length(ls)==171
  
  end
end
