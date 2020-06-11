@testset "RCF" begin
  Qx, x = PolynomialRing(FlintQQ)
  k, a = NumberField(x - 1, "a")
  Z = maximal_order(k)

  function doit(u::UnitRange, p::Int = 3)
    cnt = 0
    for i in u
      I = ideal(Z, i)
      r, mr = ray_class_group(I, n_quo=p)
      for s in index_p_subgroups(r, fmpz(p), (A,x) -> quo(A, x)[2])
        a = ray_class_field(mr, s)
        if isconductor(a, I, check=false)
          K = number_field(a)
          cnt += 1
        end
      end
    end
    return cnt
  end

  @test doit(1:100) == 16
  @test doit(10^18:10^18+100) == 18
  @test doit(10^18:10^18+1000, 11) == 2
  
  
  r, mr = Hecke.ray_class_groupQQ(Z,  32, true, 8);
  q, mq = quo(r, [r[1]])
  C = ray_class_field(mr, mq)
  KC = number_field(C)
  auts = Hecke.rel_auto(C)
  @test length(closure(auts, *)) == 8 

  k, a = wildanger_field(3, 13)
  zk = maximal_order(k)
  r0 = hilbert_class_field(k)
  @test degree(r0) == 9
  r1 = ray_class_field(4*zk, n_quo = 2)
  r2 = ray_class_field(5*zk, n_quo = 2)
  @test isone(conductor(intersect(r1, r2))[1]) 
  @test conductor(r1 * r2)[1] == 20*zk
  @test Hecke.issubfield(r1, r1*r2)
  @test !Hecke.issubfield(r0, r1*r2)

  K = simple_extension(number_field(r1))[1]
  ZK = maximal_order(K)
  lp = factor(2*3*5*maximal_order(k))
  for p = keys(lp)
    t = prime_decomposition_type(r1, p)
    l = prime_decomposition(ZK, p)
    @test t[3] == length(l)
    @test valuation(norm(l[1][1]), p) == t[2]
    @test t[1] * t[2] * t[3] == degree(r1)
    @test all(x->valuation(norm(x[1]), p) == t[2], l)
  end

  ln = [(2, true), (3, false), (5, false), (13, true), (31, false)]
  for (p, b) = ln
    @test Hecke.islocal_norm(r1, zk(p)) == b
  end

  Qx, x = PolynomialRing(FlintQQ, "x");
  k, a = NumberField(x^2 - 10, "a");
  A = ray_class_field(35*maximal_order(k))
  B = Hecke.maximal_abelian_subfield(A, k)
  @test A == B
  @test conductor(A) == conductor(B)

  K, _ = compositum(k, wildanger_field(3, 13)[1])
  A = maximal_abelian_subfield(ClassField, K)
  @test degree(A) == 2
  @test degree(intersect(A, cyclotomic_field(ClassField, 10))) == 1 
end

@testset "Some abelian extensions" begin
  Qx, x = PolynomialRing(FlintQQ, "x")
  K, a = NumberField(x - 1, "a")
  O = maximal_order(K)
  r, mr = Hecke.ray_class_groupQQ(O, 7872, true, 16)
  ls = subgroups(r, quotype = [16], fun = (x, y) -> quo(x, y, false)[2])
  @test Hecke.has_quotient(r, [16])
  class_fields = [];
  for s in ls;
    C = ray_class_field(mr, s)::Hecke.ClassField{Hecke.MapRayClassGrp, GrpAbFinGenMap}
    CC = number_field(C)
    if Hecke._is_conductor_minQQ(C, 16)
      push!(class_fields, CC)
    end
  end
  @test length(class_fields) == 14
end

