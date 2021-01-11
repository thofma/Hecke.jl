@testset "RCF" begin

  @testset "abelian extensions && related examples" begin
    
    Qx, x = PolynomialRing(FlintQQ, "x")
    K, a = NumberField(x - 1, "a")
    l = Hecke.abelian_normal_extensions(K, Int[2,2], fmpz(10)^4)
    @test length(l)==47
    l1 = collect(Hecke.C22_extensions(10^4))
    @test length(l1)==47
    @test length(abelian_fields(FlintQQ, [3], fmpz(10)^3)) == 5

    
    
 
  
    K, a = number_field(x^2+1, "a")
    auts = small_generating_set(automorphisms(K, copy = false))
    l = Hecke.abelian_normal_extensions(K, Int[2], fmpz(10)^5)
    @test length(l) == 41
    lnn = Hecke.abelian_extensions(K, Int[2], fmpz(10)^5)
    ln = typeof(l[1])[x for x in lnn if isnormal(x)]
    @test length(ln) == 41
    for x in l[1:5]
      L = number_field(x)
      autsL = absolute_automorphism_group(x, auts)
      K, autos = Hecke._relative_to_absolute(L, autsL)
      @test length(autos)==2
      y = small_generating_set(closure(autos, *))
      @test length(y)==1 || length(y)==2
      if length(y) == 2
        @test y[1]*y[2] == y[2]*y[1]
      else
        @test y[1]^2 != id_hom(K)
      end
    end
  end

end
