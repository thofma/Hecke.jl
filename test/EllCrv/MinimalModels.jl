@testset "Minimal models of elliptic curves" begin

  @testset "Minimal model (Laska-Kraus-Connell" begin
    E = EllipticCurve([1,2,3,4,5])
    EE = @inferred laska_kraus_connell(E)
    @test a_invars(EE) == (1, -1, 0, 4, 3)

    E = EllipticCurve([625, -15625, 19531250, -2929687500, -34332275390625])
    EE = @inferred laska_kraus_connell(E)
    @test a_invars(EE) == (1, -1, 0, 4, 3)
  end

  @testset "Tates algorithm" begin
    E = EllipticCurve([625, -15625, 19531250, -2929687500, -34332275390625])
    EE = @inferred tates_algorithm_global(E)
    @test a_invars(EE) == (1, -1, 0, 4, 3)

    E = EllipticCurve([1,2,3,4,5])
    EE = @inferred tates_algorithm_global(E)
    @test a_invars(EE) == (1, -1, 0, 4, 3)

    #  25350.a1
    E = EllipticCurve([1, 1, 0, 40050, 7557750])
    Ep, K, f, c = tates_algorithm_local(E, 2)
    @test a_invars(tidy_model(Ep)) == a_invars(E)
    @test K == "I1"
    @test f == 1
    @test c == 1

    Ep, K, f, c = tates_algorithm_local(E, 3)
    @test a_invars(tidy_model(Ep)) == a_invars(E)
    @test K == "I2"
    @test f == 1
    @test c == 2

    Ep, K, f, c = tates_algorithm_local(E, 5)
    @test a_invars(tidy_model(Ep)) == a_invars(E)
    @test K == "III*"
    @test f == 2
    @test c == 2

    Ep, K, f, c = tates_algorithm_local(E, 13)
    @test a_invars(tidy_model(Ep)) == a_invars(E)
    @test K == "IV*"
    @test f == 2
    @test c == 1

    # 150.a1
    E = EllipticCurve([1, 1, 0, -20700, 1134000])
    Ep, K, f, c = tates_algorithm_local(E, 2)
    @test a_invars(tidy_model(Ep)) == a_invars(E)
    @test K == "I5"
    @test f == 1
    @test c == 1

    Ep, K, f, c = tates_algorithm_local(E, 3)
    @test a_invars(tidy_model(Ep)) == a_invars(E)
    @test K == "I10"
    @test f == 1
    @test c == 2

    Ep, K, f, c = tates_algorithm_local(E, 5)
    @test a_invars(tidy_model(Ep)) == a_invars(E)
    @test K == "III*"
    @test f == 2
    @test c == 2
  end
  
  @testset "Tates algorithm over number fields" begin
    #100.1-b2
    Rx, x = PolynomialRing(QQ, "x")
    L, a = number_field(x^2-x-1)
    E = EllipticCurve(L, [1, 1, 1, -3, 1])
    F, phi = transform_rstu(E,[12, -1, 1+2*a, 3+a]) 
    F, phi = integral_model(F)
    OL = ring_of_integers(L)
    P = 2*OL
    Ep, K, f, c, s = tates_algorithm_local(F, P)
    @test K == "I5"
    @test f == 1
    @test c == 5
    @test s == true
    @test valuation(discriminant(E),P) == valuation(discriminant(Ep),P)
    
    P = numerator(ideal(OL, -2*a+1))
    
    Ep, K, f, c, s = tates_algorithm_local(Ep, P)
    @test K == "IV"
    @test f == 2
    @test c == 3
    @test s == true
    
    @test valuation(discriminant(E),P) == valuation(discriminant(Ep),P)
    
    #49.1-CMa1
    L, a = number_field(x^2-x+1)
    E = EllipticCurve(L, [0, 1+a, a, a, 0])
    F, phi = transform_rstu(E,[4, -1+a, 7, a-4]) 
    F, phi = integral_model(F)
    OL = ring_of_integers(L)
    
    P = numerator(ideal(OL, -3*a+1))
    
    Ep, K, f, c, s = tates_algorithm_local(F, P)
    @test K == "II"
    @test f == 2
    @test c == 1
    @test s == true
    
    @test valuation(discriminant(E),P) == valuation(discriminant(Ep),P)
    #673.1-a1 
    E = EllipticCurve(L, [0, a, a, -1+a, 0])
    F, phi = transform_rstu(E,[a, 0, -3+a, 7]) 
    F, phi = integral_model(F)
    P = numerator(ideal(OL, 29*a-8))
    Ep, K, f, c, s = tates_algorithm_local(F, P)
    @test K == "I1"
    @test f == 1
    @test c == 1
    @test s == false
    
    @test valuation(discriminant(E),P) == valuation(discriminant(Ep),P)
    #121.1-c3
    L, a = number_field(x^5 - x^4 - 4*x^3 + 3*x^2 + 3*x - 1)
    E = EllipticCurve(L, [0, a-1, a^3+a^2-2*a-1, -2*a-1, -a^4-a^3+a^2-a-2])
    F, phi = transform_rstu(E,[5, -1+a^2, a^3, 2*a-a^4]) 
    F, phi = integral_model(F)
    OL = ring_of_integers(L)
    P = numerator(ideal(OL, a^2+a-2))
    Ep, K, f, c, s = tates_algorithm_local(F, P)
    @test K == "I5*"
    @test f == 2
    @test c == 2
    @test s == true
    
    @test valuation(discriminant(E),P) == valuation(discriminant(Ep),P)
  end    
end

