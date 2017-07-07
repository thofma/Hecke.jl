@testset "RayClassGroup" begin

  @testset "quadratic field" begin
    
    Qx,x=PolynomialRing(QQ,"x")
    K,a=NumberField(x^2+87,"a")
    O=maximal_order(K)
    C,mC=class_group(O)
    inf_plc=real_places(K)
    
    for i=3:11
     R,mR=ray_class_group(ideal(O,i),inf_plc)
     x=mR(R[1])
     @test R[1]==mR\x
    end
    
    for i=3:11
     R,mR=ray_class_group_fac_elem(ideal(O,i),inf_plc)
     x=mR(R[1])
     x=evaluate(x).num
     @test R[1]==mR\x
    end
    
    for i=3:11
     R,mR=ray_class_group_p_part(2,ideal(O,i),inf_plc)
     x=mR(R[1])
     x=evaluate(x).num
     @test R[1]==mR\x
    end
    
    for i=3:11
     R,mR=ray_class_group_p_part(3,ideal(O,i),inf_plc)
     x=mR(R[1])
     x=evaluate(x).num
     @test R[1]==mR\x
    end
    
  end




















end
