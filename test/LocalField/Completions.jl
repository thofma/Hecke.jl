@testset "Completions" begin
  K, a = cyclotomic_field(7)
  lp = prime_decomposition(maximal_order(K), 7)
  P = lp[1][1]
  C, KtoC = completion(K, P)

  @test is_one(KtoC(one(K)))
  @test is_zero(KtoC(zero(K)))

  a = rand(K, -10:10)
  b = rand(K, -10:10)
  @test KtoC(a * b) == KtoC(a) * KtoC(b)
  @test KtoC(a + b) == KtoC(a) + KtoC(b)

  @test valuation(C(7)) == 1
  @test valuation(KtoC(K(uniformizer(P)))) == 1//6
end

@testset "small height lifts" begin
  k, a = wildanger_field(3, 13)
  c, mc = Hecke.unramified_completion(k, prime_ideals_over(maximal_order(k), 17)[1])
  @test a == preimage(mc, mc(a); small_lift = true, integral = true)
  @test a^3//5-2 == preimage(mc, mc(a^3//5-2); small_lift = true)

  Qx, x = QQ["x"];
  f = x^9 - 828*x^7 - 4371*x^6 + 226071*x^5 + 2371023*x^4 - 14243253*x^3 - 318645900*x^2 - 1637156439*x - 2754662093;

  K, a = number_field(f, "a");
  OK = maximal_order(K);
  p = 3;
  P = prime_ideals_over(OK, p)[1];
  C, mC = completion(K, P, 100);
  b = 5001310657//440423231859045*a^8 - 332069942701//3963809086731405*a^7 - 34477045500619//3963809086731405*a^6 + 22827170414018//1321269695577135*a^5 + 1893757018539416//792761817346281*a^4 + 29698097663762398//3963809086731405*a^3 - 57718358174700707//264253939115427*a^2 - 1362121503883347224//792761817346281*a - 13294109890580232283//3963809086731405;

  bb = mC(b)

  @test b == preimage(mC, mC(b); small_lift=true)
end

@testset "Issue 1075" begin
  Qx, x = QQ["x"];
  f = x^9 - 828*x^7 - 4371*x^6 + 226071*x^5 + 2371023*x^4 - 14243253*x^3 - 318645900*x^2 - 1637156439*x - 2754662093;

  K, a = number_field(f, "a");
  OK = maximal_order(K);
  p = 3;
  P = prime_ideals_over(OK, p)[1];
  C, mC = completion(K, P, 8);
  b = 5001310657//440423231859045*a^8 - 332069942701//3963809086731405*a^7 - 34477045500619//3963809086731405*a^6 + 22827170414018//1321269695577135*a^5 + 1893757018539416//792761817346281*a^4 + 29698097663762398//3963809086731405*a^3 - 57718358174700707//264253939115427*a^2 - 1362121503883347224//792761817346281*a - 13294109890580232283//3963809086731405;

  bb = mC(b)


  @test !iszero(bb)
  @test valuation(bb) == 0
  @test precision(bb) >= 8

  setprecision!(mC, 20)
  bb = mC(b)
  @test !iszero(bb)
  @test valuation(bb) == 0
  @test precision(bb) >= 20

  setprecision!(mC, 100)  #does not seem to work
  @test_broken b == preimage(mC, mC(b); small_lift=true)
  @test_broken setprecision!(mC, 20)
end

@testset "Issue 1509" begin
  F, _ = cyclotomic_field(3)
  OF = maximal_order(F);
  K, toK = completion(F, 2*OF);
  @test iszero(preimage(toK, toK(F(0))))
  setprecision!(toK, 10)
  @test precision(toK(F(1))) == 10
  setprecision!(toK, 70)
  @test precision(toK(F(1))) == 70

  K, toK = Hecke.unramified_completion(F, 2*OF)
  setprecision!(toK, 10)
  @test precision(toK(F(1))) == 10
  setprecision!(toK, 70)
  @test precision(toK(F(1))) == 70

  P = prime_decomposition(OF, 7)[1][1]
  K, toK = Hecke.totally_ramified_completion(F, P)
  setprecision!(toK, 10)
  @test precision(toK(F(1))) == 10
  setprecision!(toK, 70)
  @test precision(toK(F(1))) == 70
end

@testset "another issue" begin
  Qx, x = QQ["x"]
  K, a = number_field(Qx([-881539931206823616,457325902411822080,16029750347584272,-124243211029392,-1536813216432,10162275552,33311655,-246753,0,1]), "a", cached = false)
  OK = maximal_order(K)
  P = prime_ideals_over(OK, 2)[1]
  pi = uniformizer(P)
  el = FacElem(K, Dict{AbsSimpleNumFieldElem, ZZRingElem}(-70023594813717393//2617723003857817722429670559599034368*a^8 - 10407880684532886175//3926584505786726583644505839398551552*a^7 + 33707194712570990804227//5436809315704698346584700393013379072*a^6 - 62515076516634059387169//201363307989062901725359273815310336*a^5 - 82228786092228553653338947//302044961983594352588038910722965504*a^4 + 196643238340174973535016037//11617113922445936638001496566267904*a^3 + 3180029534094418177429253325//968092826870494719833458047188992*a^2 - 150585744322347409640268993759//968092826870494719833458047188992*a - 93002487269570298139627656955//18617169747509513842951116292096 => -1, 63703003782105027//9985820784980078592032129515072*a^8 + 9950469227255232557//14978731177470117888048194272608*a^7 - 30480446199197499888953//20739781630343240152682115146688*a^6 + 52363128338967050450931//768140060383082968617856116544*a^5 + 74063731789035953790041465//1152210090574624452926784174816*a^4 - 169428327173925119764269823//44315772714408632804876314416*a^3 - 2851889520196776289421679927//3692981059534052733739692868*a^2 + 129604649090544897585323888397//3692981059534052733739692868*a + 100562041398575741072466174730//71018866529501014110378709 => -3, K(1) => -35));
  for i in 19:25
    C, mC = completion(K, P, i);
    logel1 = sum(n * log(mC(K(pi)^(-valuation(b, P)) * b)) for (b, n) in el; init = zero(C))
    @test is_zero(logel1) || valuation(logel1) == 3
  end

  let
    Qx, x = QQ["x"]
    f = Qx([79247493, 0, -32097, 0, 1])
    K, a = number_field(f, "a", cached = false)
    OK = maximal_order(K)
    P = prime_ideals_over(OK, 3)[1]
    pi = uniformizer(P)
    pi = K(pi)
    for i in 2:30
      C, mC = completion(K, P, i)
      z = mC(pi^10)
      @test is_zero(z) || valuation(z) == 5
    end
    for i in 1:20
      K, a = number_field(f, "a", cached = false)
      @test Hecke._p_adic_regulator(K, 3) == 4
    end
  end

  let
    Qx, x = QQ["x"]
    t = [
         (x^2 - 3, 3, 1//2), # C2
         (x^2 - 3, 5, 1),
         (x^4 - 12*x^2 + 18, 3, 2), # C4
         (x^4 - 12*x^2 + 18, 5, 3),
         (x^8 - 3588*x^6 + 3218436*x^4 - 962312364*x^2 + 71932849209, 3, 5), # Q8
         (x^8 - 3588*x^6 + 3218436*x^4 - 962312364*x^2 + 71932849209, 5, 7),
         (x^8 - 36*x^6 + 306*x^4 - 540*x^2 + 81, 3, 6), # C2xC4
         (x^8 - 36*x^6 + 306*x^4 - 540*x^2 + 81, 5, 7),
         (x^3 - 21*x + 7, 5, 2), # C3
         (x^3 - 21*x + 7, 7, 1),
         (x^9 - 72*x^7 + 18*x^6 + 1539*x^5 - 864*x^4 - 10503*x^3 + 5832*x^2 + 17820*x + 216, 5, 8), # C3^2
         (x^9 - 72*x^7 + 18*x^6 + 1539*x^5 - 864*x^4 - 10503*x^3 + 5832*x^2 + 17820*x + 216, 7, 6),
         (x^5 - 110*x^3 - 55*x^2 + 2310*x + 979, 3, 4), # C5
         (x^5 - 110*x^3 - 55*x^2 + 2310*x + 979, 7, 4),
         (x^6 - 4420*x^4 + 4963157*x^2 - 871030322, 5, 5), # S3
         (x^6 - 4420*x^4 + 4963157*x^2 - 871030322, 7, 3),
         (x^3 + 394148406*x^2 + 26424291835116684*x + 447850266361023151634504, 5, 2), # non-normal S3
         (x^3 + 394148406*x^2 + 26424291835116684*x + 447850266361023151634504, 5, 2),
        ]
    for (f, p, v) in t
      K, a = number_field(f)
      w1 = Hecke._p_adic_regulator_coates(K, p)
      w2 = Hecke._p_adic_regulator_non_normal(K, p)
      @test w1 == v && w2 == v
    end
  end

  let
    Qx, x = QQ["x"]
    f = x^3 - x^2 - 115*x + 279
    for i in 1:100
      K, = number_field(f, "a", cached = false)
      @test Hecke._p_adic_regulator(K, 2) == 9//2
    end
  end
end
