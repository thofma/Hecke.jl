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
end
