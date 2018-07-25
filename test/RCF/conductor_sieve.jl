@testset "RCF" begin
  include(Pkg.dir("Hecke") * "/examples/fields.jl")

  @testset "Various examples" begin
  
    l=collect(Hecke.quadratic_extensions(50))
    @test length(l)==30
    
    fields=Hecke.D5_extensions(3*fmpz(10)^3, l)
    @test length(fields)==1
    
    fields=Hecke.Dn_extensions(3, 2*fmpz(10)^4, l)
    @test length(fields)==1
    
    fields=Hecke.C3xD5_extensions(fmpz(2000000))
    @test length(fields)==0
    
    fields=Hecke.S3xC5_extensions(fmpz(353517))
    @test length(fields)==0
    
    fields1=Hecke.C9semiC4(fmpz(10)^30)
    @test fields1==1
    
    
  
  end
  
  @testset "abelian extensions && related examples" begin
    
    Qx,x=PolynomialRing(FlintQQ, "x")
    K,a=NumberField(x-1,"a")
    O=maximal_order(K)
    l=Hecke.abelian_normal_extensions(O,[2,2], fmpz(10)^4)
    @test length(l)==47
    l1=collect(Hecke.C22_extensions(10^4))
    @test length(l1)==47
    
 
  
    K,a=NumberField(x^2+1, "a")
    O=maximal_order(K)
    l=Hecke.abelian_normal_extensions(O,[2], fmpz(10)^5, with_autos=Val{true})
    @test length(l)==41
    for x in l[1:5]
      K, autos=Hecke._from_relative_to_abs(x)
      @test length(autos)==2
      y=small_generating_set(closure(autos, *))
      @test length(y)==1 || length(y)==2
      if length(y)==2
        @test y[1]*y[2]==y[2]*y[1]
      else
        @test y[1]^2!=Hecke.NfToNfMor(K,K,gen(K))
      end
    end
  end
  
  

end
