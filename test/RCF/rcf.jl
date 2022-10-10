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
        if is_conductor(a, I, check=false)
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

  K, a = quadratic_field(-5)
  H = hilbert_class_field(K)
  L = number_field(H, over_subfield = true)
  @test absolute_degree(L) == 4

  f = x^3 - 36*x -1
  K, a = number_field(f, cached = false, check = false)
  H = hilbert_class_field(K)
  L1 = number_field(H)
  L2 = number_field(H, using_stark_units = true, redo = true)
  @test is_isomorphic(Hecke.simplified_absolute_field(L1)[1], Hecke.simplified_absolute_field(L2)[1])

  f = x^2 - x - 100
  K, a = number_field(f, cached = false, check = false)
  H = hilbert_class_field(K)
  L1 = number_field(H)
  L2 = number_field(H, using_stark_units = true, redo = true)
  @test is_isomorphic(Hecke.simplified_absolute_field(L1)[1], Hecke.simplified_absolute_field(L2)[1])
  @test length(closure(Hecke.absolute_automorphism_group(H), *)) == 10

  r, mr = Hecke.ray_class_groupQQ(Z, 32, true, 8);
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
  @test Hecke.is_subfield(r1, r1*r2)
  @test !Hecke.is_subfield(r0, r1*r2)

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
    @test Hecke.is_local_norm(r1, zk(p)) == b
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

  Qx, x = PolynomialRing(FlintQQ, "x");
  k, a = NumberField(x^2 - 10, "a");
  A = ray_class_field(35*maximal_order(k))

  K, = simple_extension(number_field(A))
  @test A == maximal_abelian_subfield(K)

  K, = simple_extension(number_field(A))
  maximal_order(K)
  @test A == maximal_abelian_subfield(K)

  cyclotomic_extension(k, 6)
  Hecke._cyclotomic_extension_non_simple(k, 6)
end

@testset "Some abelian extensions" begin
  Qx, x = PolynomialRing(FlintQQ, "x")
  K, a = NumberField(x - 1, "a")
  O = maximal_order(K)
  r, mr = Hecke.ray_class_groupQQ(O, 7872, true, 16)
  ls = subgroups(r, quotype = [16], fun = (x, y) -> quo(x, y, false)[2])
  @test Hecke.has_quotient(r, [16])
  class_fields = []
  for s in ls;
    C = ray_class_field(mr, s)::Hecke.ClassField{Hecke.MapRayClassGrp, GrpAbFinGenMap}
    CC = number_field(C)
    if Hecke._is_conductor_minQQ(C, 16)
      push!(class_fields, CC)
    end
  end
  @test length(class_fields) == 14

  K, a = quadratic_field(2, cached = false)
  @test length(abelian_extensions(K, [2], fmpz(10)^4, absolutely_distinct = true)) == 38

  # with target signatures
  K, a = number_field(x^3 - x^2 - 2*x + 1, cached = false)
  l = abelian_extensions(K, [2, 2], fmpz(10)^12)
  @test length(l) == 28
  l1 = abelian_extensions(K, [2, 2], fmpz(10)^12, signatures = [(4, 4)])
  @test length(l1) == 3
  l2 = abelian_extensions(K, [2, 2], fmpz(10)^12, signatures = [(0, 6)])
  @test length(l2) == 25
  l3 = abelian_extensions(K, [2, 2], fmpz(10)^12, signatures = [(0, 6), (4, 4)])
  @test length(l3) == 28
  l4 = abelian_extensions(K, [2, 2], fmpz(10)^12, signatures = [(0, 6), (4, 4), (0, 0)])
  @test length(l4) == 28
  l5 = abelian_extensions(K, [2, 2], fmpz(10)^12, signatures = [(0, 0)])
  @test length(l5) == 0

  # a wrong conductor

  K, = cyclotomic_field(21)
  C = maximal_abelian_subfield(ClassField, K)
  @test norm(conductor(C)[1]) == 21

  C = cyclotomic_field(ClassField, 1)
  @test C == C*C
end


