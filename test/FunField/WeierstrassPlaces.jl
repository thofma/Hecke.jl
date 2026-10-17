import Hecke: divisor

@testset "Gap numbers and Weierstrass places" begin
  kx, x = rational_function_field(GF(49), :x)
  kxy, y = kx[:y]
  F, a = function_field(y^7 + y - x^4)
  Ofin = finite_maximal_order(F)
  p1, _ = first(factor(ideal(Ofin, x-1)))
  D = divisor(p1)

  @test gap_numbers(F) == [1, 2, 3, 4, 5, 8, 9, 10, 15]
  @test degree(ramification_divisor(F)) == 912

  gaps, R = @inferred Hecke._gaps_and_ramification_divisor(D, false)
  @test gaps == [1, 2, 3, 4, 5, 8, 9, 10]
  @test degree(R) == 664

  kx, x = rational_function_field(QQ, :x)
  kxy, y = kx[:y]
  F, a = function_field(y^2 - x^7 - 1)
  Ofin = finite_maximal_order(F)
  Oinf = infinite_maximal_order(F)


  @test gap_numbers(F) == [1, 2, 3]
  Ps = weierstrass_places(F)
  test_Ps = [ideal(Ofin, x+1, Ofin(a)),
    ideal(Ofin, x^6 - x^5 + x^4 - x^3 + x^2 - x + 1, Ofin(a)), 
    ideal(Oinf, (1//x), Oinf(1//x^4*a))]
  for P in Ps
    @test P in test_Ps
  end

  P = test_Ps[1]
  @test gap_numbers(divisor(P)) == [1,2]
  P = test_Ps[2]
  @test gap_numbers(divisor(P)) == []
  @test weierstrass_places(divisor(P)) == []
end

@testset "Hasse derivatives beyond Int range" begin
  # we consider the curve y^2 = x^3 + 1: D^(j) x^m = binomial(m, j) x^(m - j)
  monomial_derivative(x, m, j) = parent(x)(binomial(ZZ(m), ZZ(j)))*x^(m - j)

  @testset "char 0, factorial(j) for j >= 21" begin
    kx, x = rational_function_field(QQ, :x; cached = false)
    kxy, y = kx[:y]
    F, a = function_field(y^2 - x^3 - 1; cached = false)

    @test differentiation(F(x)^25, 21) == monomial_derivative(F(x), 25, 21)
    # Leibniz rule applied to a^2 = x^3 + 1
    @test sum(differentiation(a, i)*differentiation(a, 21 - i) for i in 0:21) == 0
  end

  @testset "char p, factorial(j mod p) for j mod p >= 21" begin
    kx, x = rational_function_field(GF(23), :x; cached = false)
    kxy, y = kx[:y]
    F, a = function_field(y^2 - x^3 - 1; cached = false)

    @test differentiation(F(x)^22, 21) == monomial_derivative(F(x), 22, 21)
    # 44 = 1*23 + 21: needs factorial(21)
    @test differentiation(F(x)^45, 44) == monomial_derivative(F(x), 45, 44)
  end

  @testset "char p, binomials in power_representation overflow" begin
    p = 101
    kx, x = rational_function_field(GF(p), :x; cached = false)
    kxy, y = kx[:y]
    F, a = function_field(y^2 - x^3 - 1; cached = false)

    l = power_representation(a)
    @test length(l) == p
    @test sum(l[i + 1]^p*F(x)^i for i in 0:p - 1) == a
    @test differentiation(F(x)^150, 102) == monomial_derivative(F(x), 150, 102)
    # D^(1) D^(p) = binomial(p + 1, 1) D^(p + 1) = D^(p + 1)
    @test differentiation(differentiation(a, p), 1) == differentiation(a, p + 1)
  end
end
