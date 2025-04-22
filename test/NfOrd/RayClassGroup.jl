@testset "RayClassGroup" begin

  #include(joinpath(Hecke.pkgdir, "examples", "RayClass.jl"))

  @testset "Big prime" begin
    k,  = wildanger_field(2, 13)
    Zk = maximal_order(k)
    p = next_prime(ZZRingElem(2)^100)
    r, mr = ray_class_group(ideal(Zk, p), n_quo = 2)
    @test order(domain(mr)) == 2
  end

  @testset "quadratic fields" begin

    Qx,x=polynomial_ring(QQ,"x")
    K,a=number_field(x^2+199,"a")
    O=maximal_order(K)
    C,mC=class_group(O)

    for i=9:13
      R1,mR1=ray_class_group(ideal(O,i), n_quo=3)
      for r in R1
        @test r== mR1\(mR1(r))
      end
      R,mR=ray_class_group(ideal(O,i))
      q,mq=quo(R,3)
      @test Hecke.is_isomorphic(R1,q)
    end

    K,a=number_field(x^2-5,"a")
    O=maximal_order(K)
    C,mC=class_group(O, redo = true)
    inf_plc=real_places(K)

    for i=9:13
      R1,mR1=ray_class_group(ideal(O,i),inf_plc)
      for r in R1
        @test r== mR1\(mR1(r))
      end
      R2, mR2=ray_class_group(ideal(O,i), inf_plc, n_quo=2)
      for r in R2
        @test r== mR2\(mR2(r))
      end
      q1,mq1=quo(R1,2)
      @test Hecke.is_isomorphic(q1,R2)
    end
  end

  @testset "infinite places" begin

     Qx, x = polynomial_ring(QQ, "x");
     K, a = number_field(x^4-4*x^3-11*x^2+30*x+20, cached = false)
    O = maximal_order(K)
    r, mr = ray_class_group(ideal(O,4), real_places(K), n_quo=2)
    @test order(r) == 2^5
    for el in r
      @test el == mr\(mr(el))
    end
  end

  @testset "stable subgroups" begin

     Qx,x=polynomial_ring(QQ,"x");
    f=x^2+1;
    K,a=number_field(f,"a");
    auts = automorphism_list(K)
    auts = small_generating_set(auts, *)
    O = maximal_order(K);
    C, mC = class_group(O);
    r, mr = ray_class_group(ideal(O,3*5*7), n_quo=8);
    act = Hecke.induce_action(mr, auts);
    x=Hecke.stable_subgroups(r,act,op = quo, quotype = [8]);
    y=subgroups(r, quotype=[8])
    i=0
    for el in y
      if Hecke.is_stable(act,el[2])
        i+=1
      end
    end
    @test length(x)==i

    x=Hecke.stable_subgroups(r, act, op = quo, quotype = [2,4]);
    y=subgroups(r, quotype=[2,4])
    i=0
    for el in y
      if Hecke.is_stable(act,el[2])
        i+=1
      end
    end
    @test length(x)==i

    r,mr=ray_class_group(ideal(O,9*19*29), n_quo=9);
    act=Hecke.induce_action(mr, auts);
    x=Hecke.stable_subgroups(r, act, op = quo, quotype = [9]);
    y=subgroups(r, quotype=[9])
    i=0
    for el in y
      if Hecke.is_stable(act,el[2])
        i+=1
      end
    end
    @test length(x)==i

    x=Hecke.stable_subgroups(r, act, op = quo, quotype = [3,9]);
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
