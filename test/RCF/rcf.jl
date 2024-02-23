@testset "RCF" begin
  Qx, x = polynomial_ring(FlintQQ)
  k, a = number_field(x - 1, "a")
  Z = maximal_order(k)

  function doit(u::AbstractUnitRange, p::Int = 3)
    cnt = 0
    for i in u
      I = ideal(Z, i)
      r, mr = ray_class_group(I, n_quo=p)
      for s in index_p_subgroups(r, ZZRingElem(p), (A,x) -> quo(A, x)[2])
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

  Qx, x = polynomial_ring(FlintQQ, "x");
  k, a = number_field(x^2 - 10, "a");
  A = ray_class_field(35*maximal_order(k))
  B = Hecke.maximal_abelian_subfield(A, k)
  @test A == B
  @test conductor(A) == conductor(B)

  K, _ = compositum(k, wildanger_field(3, 13)[1])
  A = maximal_abelian_subfield(ClassField, K)
  @test degree(A) == 2
  @test degree(intersect(A, cyclotomic_field(ClassField, 10))) == 1

  Qx, x = polynomial_ring(FlintQQ, "x");
  k, a = number_field(x^2 - 10, "a");
  A = ray_class_field(35*maximal_order(k))

  K, = simple_extension(number_field(A))
  @test A == maximal_abelian_subfield(K)

  K, = simple_extension(number_field(A))
  maximal_order(K)
  @test A == maximal_abelian_subfield(K)

  cyclotomic_extension(k, 6)
  Hecke._cyclotomic_extension_non_simple(k, 6)

  r = ray_class_field(5*maximal_order(quadratic_field(3)[1]))
  absaut = absolute_automorphism_group(r)
  @test length(closure(absaut, *)) == 8 # normal

  r = ray_class_field(27*maximal_order(quadratic_field(42)[1]))
  @test absolute_automorphism_group(r) isa Vector
  # Too large to check

  K = quadratic_field(3)[1]
  OK = maximal_order(K)
  rcf = ray_class_field(5*OK, real_places(K))
  absaut = absolute_automorphism_group(rcf) # normal
  @test length(closure(absaut, *)) == 32

  r = hilbert_class_field(quadratic_field(13*17*37)[1])
  @test isone(discriminant(r))
  absaut = absolute_automorphism_group(r) # normal
  @test length(closure(absaut, *)) == 8
  a, ma = automorphism_group(r)
  @assert order(a) == 4
  f = ma(a[1]) * ma(a[2])
  @assert preimage(ma, f) == a([1,1])

  f = frobenius_map(r)
  lp = prime_decomposition(base_ring(r), 19)
  @assert preimage(ma, f(lp[1][1])) == a[2] #true for both actually.
  Hecke.find_frob(r.cyc[1])
  norm_group(r)

  s = ray_class_field(7*base_ring(r))
  h = hom(base_field(r), base_field(r), gen(base_field(r)))
  q = Hecke.extend_hom(r, s, h)
  @test q == "not finished"
  @test Hecke.maximal_p_subfield(s, 2) == r

  @test is_abelian(number_field(r))
  @test is_abelian(base_field(r))
  @test length(subfields(r)) == 5
  @test length(subfields(r; degree = 2)) == 3
  @test is_central(r)

  K = quadratic_field(5)[1]
  OK = maximal_order(K)
  rcf = ray_class_field(9*OK, real_places(K))
  @test length(closure(absolute_automorphism_group(rcf), *)) == 12

  rcf = ray_class_field(21*OK, real_places(K))
  c = conductor(rcf)
  @test c[1] == 21*OK
  @test length(c[2]) == 2 # the order is wrong

  k = quadratic_field(8)[1]
  e = equation_order(k)
  @test degree(Hecke.ring_class_field(e)) == 1
  k = quadratic_field(8*9)[1]
  e = equation_order(k)
  @test degree(Hecke.ring_class_field(e)) == 2

  k, _ = number_field(x^3 - 69*x - 52)
  kk = number_field(ray_class_field(1*maximal_order(k), real_places(k)))
  @test degree(kk) == 2
end

@testset "Jon Yard" begin
  for (D, m) = [(3, 32), (5, 32), (13, 32), (3, 27)]
    K = quadratic_field(D)[1]
    OK = maximal_order(K)
    rcf = ray_class_field(m*OK,real_places(K))
    F = number_field(rcf)
#    @show length(absolute_automorphism_group(rcf))
    @test length(absolute_automorphism_group(rcf)) > 1
  end
end

@testset "Some abelian extensions" begin
  Qx, x = polynomial_ring(FlintQQ, "x")
  K, a = number_field(x - 1, "a")
  O = maximal_order(K)
  r, mr = Hecke.ray_class_groupQQ(O, 7872, true, 16)
  ls = subgroups(r, quotype = [16], fun = (x, y) -> quo(x, y, false)[2])
  @test Hecke.has_quotient(r, [16])
  class_fields = []
  for s in ls;
    C = ray_class_field(mr, s)::Hecke.ClassField{Hecke.MapRayClassGrp, FinGenAbGroupHom}
    CC = number_field(C)
    if Hecke._is_conductor_minQQ(C, 16)
      push!(class_fields, CC)
    end
  end
  @test length(class_fields) == 14

  K, a = quadratic_field(2, cached = false)
  @test length(abelian_extensions(K, [2], ZZRingElem(10)^4, absolutely_distinct = true)) == 38

  # with target signatures
  K, a = number_field(x^3 - x^2 - 2*x + 1, cached = false)
  l = abelian_extensions(K, [2, 2], ZZRingElem(10)^12)
  @test length(l) == 28
  l1 = abelian_extensions(K, [2, 2], ZZRingElem(10)^12, signatures = [(4, 4)])
  @test length(l1) == 3
  l2 = abelian_extensions(K, [2, 2], ZZRingElem(10)^12, signatures = [(0, 6)])
  @test length(l2) == 25
  l3 = abelian_extensions(K, [2, 2], ZZRingElem(10)^12, signatures = [(0, 6), (4, 4)])
  @test length(l3) == 28
  l4 = abelian_extensions(K, [2, 2], ZZRingElem(10)^12, signatures = [(0, 6), (4, 4), (0, 0)])
  @test length(l4) == 28
  l5 = abelian_extensions(K, [2, 2], ZZRingElem(10)^12, signatures = [(0, 0)])
  @test length(l5) == 0

  # a wrong conductor

  K, = cyclotomic_field(21)
  C = maximal_abelian_subfield(ClassField, K)
  @test norm(conductor(C)[1]) == 21

  C = cyclotomic_field(ClassField, 1)
  @test C == C*C
end

@testset "Frobenius at infinity" begin
  K, = quadratic_field(21)
  OK = maximal_order(K)
  C = ray_class_field(6*OK, real_places(K)[1:1])
  sigma = complex_conjugation(C, real_places(K)[1])
  L = number_field(C)
  e = real_embeddings(K)[1]
  @test all(ee -> sigma * ee == conj(ee), extend(e, hom(K, L)))

  k, = quadratic_field(23)
  @test_throws ArgumentError complex_conjugation(C, real_places(k)[1])
  C = ray_class_field(6*OK, real_places(K)[1:1])
  @test_throws ArgumentError complex_conjugation(C, real_places(K)[2])

  K = quadratic_field(15)[1]
  OK = maximal_order(K)
  rcf = ray_class_field(9*OK,real_places(K))
  @test domain(complex_conjugation(rcf,real_places(K)[1])) == number_field(rcf)
end


@testset "extend base field" begin
  Qx, x = QQ["x"]
  k, a = number_field(x^3 - 3*x^2 - 87*x + 424) 
  #random transformation from x^3-5 - so that lll does s.th.
  K, mkK = normal_closure(k)

  zk = lll(maximal_order(k))
  ZK = lll(maximal_order(K))

  C, mC = ray_class_group(27*zk, real_places(k))
  Lambda = ray_class_field(mC)
  G = genus_field(Lambda, rationals_as_number_field()[1])
  @test degree(G) == 54

  GK = Hecke.extend_base_field(G, mkK)
  @test degree(GK) == 27

  GG = genus_field(ray_class_field(27*ZK), k)
  @test degree(GG) == 9*27
end

@testset "Knots - elementary" begin
  Qx, x = QQ["x"]
  f = x^4 - x^3 - 32*x^2 + 23*x + 224
  k = number_field(f, cached = false)[1];
  zk = lll(maximal_order(k))
  Gamma = ray_class_field(8*zk, real_places(k))
  @test degree(Gamma) == 128

  G = genus_field(Gamma)
  @test degree(G) == 8

  Z = Hecke.maximal_central_subfield(Gamma, stable = 20, lower_bound = degree(G))
  @test degree(Z) == 16

  lp = prime_decomposition(zk, 2)
  d = Set([elementary_divisors(decomposition_group(Gamma, p[1])) for p = lp])
  @test d == Set([ZZRingElem[2,2,4], ZZRingElem[2,2,2,2,4]])

  d = Set([elementary_divisors(inertia_subgroup(Gamma, p[1])) for p = lp])
  @test d == Set([ZZRingElem[2,2], ZZRingElem[2,2,2,2]])
end 

@testset "Knots - abelian" begin
  Qx, x = QQ["x"]
  f = x^4 - x^3 - 32*x^2 + 23*x + 224
  k = splitting_field(f)
  s = subfields(k, degree = 3)[1][1]
  k = relative_simple_extension(k, s)[1]
  C = ray_class_field(k)
  @test order(Hecke.knot(C)) == 2

  k = number_field([x^2-3, x^2-5])[1]
  ka = absolute_simple_field(k)[1]
  C = ray_class_field(ka)
  @test order(Hecke.knot(C)) == 1

  k = number_field([x^2+3, x^2-13])[1]
  ka = absolute_simple_field(k)[1]
  C = ray_class_field(ka)
  @test order(Hecke.knot(C)) == 2

  Z, G = Hecke.small_knot(ka)
  @test degree(Z) == 2
  @test degree(G) == 1
end

@testset "Knots - non-abelian" begin
  k, a = cyclotomic_field(7)
  f = minpoly(a+1//a)
  k, a = number_field(f)
  zk = lll(maximal_order(k))
  R = ray_class_field(29*31*37*41*43*zk, n_quo = 2)
  G, mG = automorphism_group(k)
  h = Hecke.norm_group_map(R, R, mG(G[1]))
  hh = Hecke.norm_group_map(R, R, mG(G[2]))
  S = fixed_field(R, kernel(h-hh)[1])

  ns = norm_group(S)[1]
  t = fixed_field(S, sub(ns, [ns[1], ns[3]])[1])
  @test degree(t) == 4
  @test !is_normal(t)
  @test normal_closure(t) == S
end

@testset "Conductor fix" begin
  flds = abelian_extensions(QQ, [2, 2], ZZ(4225), only_real = true)
  @test length(flds) == 4
end

@testset "Kaiser-Lorenz" begin
  Qx, x = QQ["x"]
  f = x^6-x^5+x^4-2*x^3+x^2+1
  k = splitting_field(f)
  I = Hecke.lorenz_module(k, 12)
  @test Hecke.is_consistent(I)
end

@testset "Enumerate by conductor" begin
  l = abelian_extensions([3], collect(1:10^3); only_real = true)
  @test length(l) == 159
  l = abelian_extensions([2], collect(1:10^3))
  @test length(l) == 607
end
