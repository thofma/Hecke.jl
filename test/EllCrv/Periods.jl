@testset "Periods of elliptic curves" begin

  @testset "Periods" begin
    K, a = quadratic_field(-5)
    E = EllipticCurve(K, [1-a, a-4, 1, 0, 2])
    L = @inferred periods(E)
    C = AcbField(100)
    R = ArbField(100)
    
    @test contains(C("1.4957398230317969764826659918696261470051680292263", "-1.7172974258712736251613758310814298445068197815882"), L[1][1])
    @test contains(C("1.4432185402614538932714036971746453808628921690048", "0.13590523293148654948722413951015999464720046993453"), L[1][2]) 
  
    @test contains(C("1.4957398230317969764826659918696261470051680292263", "1.7172974258712736251613758310814298445068197815882"), L[2][1])
    @test contains(C("-1.4432185402614538932714036971746453808628921690048", "0.13590523293148654948722413951015999464720046993453"), L[2][2]) 

    K, a = quadratic_field(7)
    E = EllipticCurve(K, [1, a, 3, a+7, -2])
    L = @inferred periods(E)
  
    @test contains(C("2.7629221426067257179910708730994041505062373525092", "0"), L[1][1])
    @test contains(C("-1.3814610713033628589955354365497020752531186762546", "1.0723061100392989886753176174505371703784396785786"), L[1][2]) 
    @test contains(C("1.8732151552347948762918104229736927352409220860319", "0"), L[2][1])
    @test contains(C("-0.93660757761739743814590521148684636762046104301596", "1.1499337130709974851637683595038472294320843580688"), L[2][2]) 
  
    E = EllipticCurve([0, -6, 0, 11, -6])
    L = @inferred periods(E)
   
    @test contains(C("2.6220575542921198104648395898911194136827549514316", "0"), L[1][1])
    @test contains(C("0", "2.6220575542921198104648395898911194136827549514316"), L[1][2])


    @test contains(R("2.6220575542921198104648395898911194136827549514316"), @inferred real_period(E))
  end
  @testset "Faltings height" begin
    @test contains(R("-1.3105329259115095182522750833047286679516075894078"), stable_faltings_height(E))
    @test contains(R("-0.96395933563153686354365902257564038391385752222769"), @inferred faltings_height(E))
  end
end
