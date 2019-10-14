@testset "RCF" begin

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
    l=Hecke.abelian_normal_extensions(O, [2], fmpz(10)^5, with_autos=Val{true})
    @test length(l)==41
    for x in l[1:5]
      K, autos=Hecke._from_relative_to_abs(x[1], x[2])
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
