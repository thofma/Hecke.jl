@testset "RayClassGroup" begin

  @testset "Big prime" begin
    k, _ = wildanger_field(2, 13)
    Zk = maximal_order(k)
    p = next_prime(fmpz(2)^100)
    r, mr = ray_class_group(ideal(Zk, p), n_quo = 2)
    @test order(domain(mr)) == 2
  end

  @testset "quadratic field" begin
    
    Qx,x=PolynomialRing(FlintQQ,"x")
    K,a=NumberField(x^2+199,"a")
    O=maximal_order(K)
    C,mC=class_group(O)
    
    for i=9:13
     R,mR=ray_class_group(ideal(O,i), p_part=3)
     for r in R
       @test r== mR\(mR(r))
     end
    end
    
    for i=9:13
     R,mR=ray_class_group(ideal(O,i), n_quo=3)
     for r in R
       @test r== mR\(mR(r))
     end
    end
    
    Qx,x=PolynomialRing(FlintQQ,"x")
    K,a=NumberField(x^2-5,"a")
    O=maximal_order(K)
    C,mC=class_group(O, redo = true)
    inf_plc=real_places(K)
    
    for i=9:13
     R,mR=ray_class_group(ideal(O,i),inf_plc,p_part=2)
     for r in R
       x=mR\(mR(r))
       @test r== x
     end
    end
    
    for i=9:13
     R,mR=ray_class_group(ideal(O,i),inf_plc)
     mR=Hecke.make_snf(mR)
     for r in domain(mR)
       x=mR\(mR(r))
       @test r== x
     end
    end
    
    for i=9:13
     R,mR=ray_class_group(ideal(O,i), inf_plc, n_quo=2)
     for r in R
       @test r== mR\(mR(r))
     end
    end

  end
  
  @testset "stable subgroups" begin
  
    Qx,x=PolynomialRing(FlintQQ,"x");
    f=x^2+1;
    K,a=NumberField(f,"a");
    O=maximal_order(K);
    C,mC=class_group(O);
    r,mr=ray_class_group(ideal(O,3*5*7), n_quo=8);
    act=Hecke._act_on_ray_class(mr);
    x=Hecke.stable_subgroups(r,[8],act,op = quo);
    y=subgroups(r, quotype=[8])
    i=0
    for el in y
      if Hecke.is_stable(act,el[2])
        i+=1
      end
    end
    @test length(x)==i
    
    x=Hecke.stable_subgroups(r,[2,4],act,op = quo);
    y=subgroups(r, quotype=[2,4])
    i=0
    for el in y
      if Hecke.is_stable(act,el[2])
        i+=1
      end
    end
    @test length(x)==i
    
    r,mr=ray_class_group(ideal(O,9*19*29), n_quo=9);
    act=Hecke._act_on_ray_class(mr);
    x=Hecke.stable_subgroups(r,[9],act,op = quo);
    y=subgroups(r, quotype=[9])
    i=0
    for el in y
      if Hecke.is_stable(act,el[2])
        i+=1
      end
    end
    @test length(x)==i
    
    x=Hecke.stable_subgroups(r,[3,9],act,op = quo);
    y=subgroups(r, quotype=[3,9])
    i=0
    for el in y
      if Hecke.is_stable(act,el[2])
        i+=1
      end
    end
    @test length(x)==i
  end
  
end
