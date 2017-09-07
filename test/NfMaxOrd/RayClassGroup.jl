@testset "RayClassGroup" begin

  @testset "quadratic field" begin
    
    Qx,x=PolynomialRing(FlintQQ,"x")
    K,a=NumberField(x^2+87,"a")
    O=maximal_order(K)
    C,mC=class_group(O)
    
    for i=3:11
     R,mR=ray_class_group(ideal(O,i), p_part=3)
     x=mR(R[1])
     x=evaluate(x).num
     @test R[1]==mR\x
    end
    
    Qx,x=PolynomialRing(FlintQQ,"x")
    K,a=NumberField(x^2-5,"a")
    O=maximal_order(K)
    C,mC=class_group(O, redo = true)
    inf_plc=real_places(K)
    
    for i=3:11
     R,mR=ray_class_group(ideal(O,i),inf_plc,p_part=2)
     x=mR(R[1])
     x=evaluate(x).num
     @test R[1]==mR\x
    end
    
    for i=3:11
     R,mR=ray_class_group(ideal(O,i),inf_plc)
     x=mR(R[1])
     @test R[1]==mR\x
    end
    
    for i=3:11
     R,mR=ray_class_group(ideal(O,i),inf_plc)
     x=mR(R[1])
     x=evaluate(x).num
     @test R[1]==mR\x
    end
    
  end
end
