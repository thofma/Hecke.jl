@testset "RCF" begin


  @testset "quadratic extensions" begin
  
    l=collect(Hecke.quadratic_extensions(100))
    @test length(l)==61
  
  end
  
  @testset "abelian extensions" begin
    
    Qx,x=PolynomialRing(FlintQQ, "x")
    K,a=NumberField(x-1,"a")
    O=maximal_order(K)
    l=Hecke.abelian_normal_extensions(O,[2,2], fmpz(10)^4)
    @test length(l)==47
    l1=collect(Hecke.C22_extensions(10^4))
    @test length(l1)==47
    
    l=Hecke.abelian_normal_extensions(O,[4], fmpz(10)^3)
    @test length(l)==1
  
    K,a=NumberField(x^2+1, "a")
    O=maximal_order(K)
    l=Hecke.abelian_normal_extensions(O,[2], fmpz(10)^5)
    @test length(l)==41
  end

end
