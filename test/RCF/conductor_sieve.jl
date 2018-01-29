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
  end

end
