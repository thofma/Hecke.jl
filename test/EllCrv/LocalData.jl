@testset "Local Data" begin

  @testset "Tates algorithm" begin
    E = elliptic_curve([625, -15625, 19531250, -2929687500, -34332275390625])
    EE = @inferred tates_algorithm_global(E)
    @test a_invariants(EE) == (1, -1, 0, 4, 3)

    E = elliptic_curve([1,2,3,4,5])
    EE = @inferred tates_algorithm_global(E)
    @test a_invariants(EE) == (1, -1, 0, 4, 3)

    #  25350.a1
    E = elliptic_curve([1, 1, 0, 40050, 7557750])
    Ep, K, f, c = tates_algorithm_local(E, 2)
    @test a_invariants(tidy_model(Ep)) == a_invariants(E)
    @test K == "I1"
    @test f == 1
    @test c == 1

    _, K, f, c = Hecke._tates_algorithm(E, 2)
    @test K == "I1"
    @test f == 1
    @test c == 1

    @test reduction_type(E, 2) == "Nonsplit multiplicative"

    Ep, K, f, c = tates_algorithm_local(E, 3)
    @test a_invariants(tidy_model(Ep)) == a_invariants(E)
    @test K == "I2"
    @test f == 1
    @test c == 2

    _, K, f, c = Hecke._tates_algorithm(E, 3)
    @test K == "I2"
    @test f == 1
    @test c == 2

    Ep, K, f, c = tates_algorithm_local(E, 5)
    @test a_invariants(tidy_model(Ep)) == a_invariants(E)
    @test K == "III*"
    @test f == 2
    @test c == 2

    _, K, f, c = Hecke._tates_algorithm(E, 5)
    @test K == "III*"
    @test f == 2
    @test c == 2

    @test reduction_type(E, 5) == "Additive"

    Ep, K, f, c = tates_algorithm_local(E, 13)
    @test a_invariants(tidy_model(Ep)) == a_invariants(E)
    @test K == "IV*"
    @test f == 2
    @test c == 1


    # 150.a1
    E = elliptic_curve([1, 1, 0, -20700, 1134000])
    Ep, K, f, c = tates_algorithm_local(E, 2)
    @test a_invariants(tidy_model(Ep)) == a_invariants(E)
    @test K == "I5"
    @test f == 1
    @test c == 1

    Ep, K, f, c = tates_algorithm_local(E, 3)
    @test a_invariants(tidy_model(Ep)) == a_invariants(E)
    @test K == "I10"
    @test f == 1
    @test c == 2

    Ep, K, f, c = tates_algorithm_local(E, 5)
    @test a_invariants(tidy_model(Ep)) == a_invariants(E)
    @test K == "III*"
    @test f == 2
    @test c == 2

    E = integral_model(elliptic_curve([0, 0, 0, 1, 1//2]))[1]
    Ep, K, f, c = tates_algorithm_local(E, 2)
    @test K == "II*"
    @test f == 6
    @test c == 1

    @test reduction_type(E, 3) == "Good"

    E= elliptic_curve([0, 0, 0, 2, 2])
    Ep, K, f, c = tates_algorithm_local(E, 2)
    @test K == "II"
    @test f == 6
    @test c == 1

    E = elliptic_curve([1, 0, 4, 7, 14])
    Ep, K, f, c = tates_algorithm_local(E, 3)
    @test K == "I2"
    @test f == 1
    @test c == 2

    @test reduction_type(E, 3) == "Split multiplicative"

    E = elliptic_curve([0, 0, 0, 0, -1])
    Ep, K, f, c = tates_algorithm_local(E, 3)
    @test K == "III"
    @test f == 2
    @test c == 2

    E = elliptic_curve([0, 0, 0, 108, 0])
    Ep, K, f, c = tates_algorithm_local(E, 2)
    @test K == "I2*"
    @test f == 6
    @test c == 2

    E = elliptic_curve([0, -1, 0, -208, 1412])
    Ep, K, f, c = tates_algorithm_local(E, 2)
    @test K == "I0*"
    @test f == 5
    @test c == 2

    E = elliptic_curve([0, 0, 0, 0, -3^2])
    Ep, K, f, c = tates_algorithm_local(E, 3)
    @test K == "IV"
    @test f == 5
    @test c == 1
  end

  @testset "Tates algorithm over number fields" begin
    #100.1-b2
    Rx, x = polynomial_ring(QQ, "x")
    L, a = number_field(x^2-x-1)
    E = elliptic_curve(L, [1, 1, 1, -3, 1])
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

    @test reduction_type(E, P) == "Split multiplicative"

    P = 3*OL
    Ep, K, f, c, s = tates_algorithm_local(F, P)
    @test K == "I0"
    @test f == 0
    @test c == 1
    @test s == true

    @test reduction_type(E, 3*OL) == "Good"

    P = numerator(ideal(OL, -2*a+1))

    Ep, K, f, c, s = tates_algorithm_local(Ep, P)
    @test K == "IV"
    @test f == 2
    @test c == 3
    @test s == true

    @test valuation(discriminant(E),P) == valuation(discriminant(Ep),P)

    #49.1-CMa1
    L, a = number_field(x^2-x+1)
    E = elliptic_curve(L, [0, 1+a, a, a, 0])
    F, phi = transform_rstu(E,[4, -1+a, 7, a-4])
    F, phi = integral_model(F)
    OL = ring_of_integers(L)

    P = numerator(ideal(OL, -3*a+1))

    Ep, K, f, c, s = tates_algorithm_local(F, P)
    @test K == "II"
    @test f == 2
    @test c == 1
    @test s == true

    #144.1-CMa2
    E = elliptic_curve(L, [0, 0, 0, -15, 22])
    F, phi = transform_rstu(E,[4, -1+a, 7, a-4])
    F, phi = integral_model(F)

    P = numerator(ideal(OL, -2*a+1))

    Ep, K, f, c, s = tates_algorithm_local(F, P)
    @test K == "I0*"
    @test f == 2
    @test c == 2
    @test s == true

    P = 2*OL

    Ep, K, f, c, s = tates_algorithm_local(F, P)
    @test K == "IV*"
    @test f == 2
    @test c == 3
    @test s == true

    @test valuation(discriminant(E),P) == valuation(discriminant(Ep),P)
    #673.1-a1
    E = elliptic_curve(L, [0, a, a, -1+a, 0])
    F, phi = transform_rstu(E,[a, 0, -3+a, 7])
    F, phi = integral_model(F)
    P = numerator(ideal(OL, 29*a-8))
    Ep, K, f, c, s = tates_algorithm_local(F, P)
    @test K == "I1"
    @test f == 1
    @test c == 1
    @test s == false

    @test reduction_type(Ep, P) == "Nonsplit multiplicative"

    #2401,3-a1
    E = elliptic_curve(L, [1, -1, 0, -2, -1])
    F, phi = transform_rstu(E,[a, 0, -3+a, 7])
    F, phi = integral_model(F)
    P = numerator(ideal(OL, 3*a -2))
    Ep, K, f, c, s = tates_algorithm_local(F, P)
    @test K == "III"
    @test f == 2
    @test c == 2
    @test s == true

     @test reduction_type(Ep, P) == "Additive"

    #12321.1-b2
    E = elliptic_curve(L, [1, -1, 0, 6 - 57*a, 108 - 162*a])
    F, phi = transform_rstu(E,[a, 0, -3+a, 7])
    F, phi = integral_model(F)
    P = numerator(ideal(OL, -2*a + 1))
    Ep, K, f, c, s = tates_algorithm_local(F, P)
    @test K == "III*"
    @test f == 2
    @test c == 2
    @test s == true

    L, a = quadratic_field(3)
    OL = ring_of_integers(L)
    E = elliptic_curve(L, [0, 0, 0, 81, 243*a])
    P = numerator(a*OL)
    Ep, K, f, c, s = tates_algorithm_local(E, P)
    @test K == "II*"
    @test f == 4
    @test c == 1
    @test s == true

    E = elliptic_curve(L, [0, 0, 0, 3, 1])
    Ep, K, f, c, s = tates_algorithm_local(E, numerator(a*OL))
    @test K == "IV"
    @test f == 4
    @test c == 1
    @test s == true

    E = elliptic_curve(L, [0, 0, 27, 0, 486])
    Ep, K, f, c, s = tates_algorithm_local(E, numerator(a*OL))
    @test K == "IV*"
    @test f == 8
    @test c == 1
    @test s == true

    E = elliptic_curve(L, [1, 0, 4, 7, 14])
    Ep, K, f, c, s = tates_algorithm_local(E, numerator(a*OL))
    @test K == "I4"
    @test f == 1
    @test c == 4
    @test s == true


    @test valuation(discriminant(E),P) == valuation(discriminant(Ep),P)
    #121.1-c3
    L, a = number_field(x^5 - x^4 - 4*x^3 + 3*x^2 + 3*x - 1)
    E = elliptic_curve(L, [0, a-1, a^3+a^2-2*a-1, -2*a-1, -a^4-a^3+a^2-a-2])
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

  @testset "Conductors, local getters" begin

    E = elliptic_curve([1, 1, 0, 40050, 7557750])
    @test conductor(E) == 25350
    @test @inferred tamagawa_numbers(E) == [1, 2 ,2, 1]
    @test @inferred kodaira_symbols(E) == ["I1", "I2", "III*", "IV*"]

    Rx, x = polynomial_ring(QQ, "x")
    K, a = number_field(x^2-x+3)
    E = elliptic_curve(K, [0, -1, 1, -7820, -263580])
    OK = ring_of_integers(K)
    I = (-2*a+1)*OK
    @test @inferred conductor(E) == I

    L, a = number_field(x^2-x+1)
    E = elliptic_curve(L, [0, 0, 0, -15, 22])
    @test @inferred tamagawa_numbers(E) == [3, 2]
    @test @inferred kodaira_symbols(E) == ["IV*", "I0*"]
  end

  # Another test
  Qx, x = QQ["x"]
  K, a = number_field(x^2- x + 1)
  E = elliptic_curve(K, [16807*a - 84035, 41241385934*a + 5367031656, 20124912723078142//3*a + 13331154044930911//3, 928925752459624769703*a - 289907255041158152853, -221729762092842673528466044620617//9*a + 22979609049341545658321384288371//9])
  lp = prime_decomposition(maximal_order(K), 7)
  if a + 4 in lp[1][1]
    P = lp[1][1]
  else
    P = lp[2][1]
  end
  @test @inferred kodaira_symbol(E, P) == "I0"

  # rational function field
  QQt, t = rational_function_field(QQ, "t")
  E = elliptic_curve_from_j_invariant(t)
   _, K, f, c, s = tates_algorithm_local(E, 1//t)
  @test K == "I1"
  @test f == 1
  @test c == 1
  @test s == true

   _, K, f, c, s = tates_algorithm_local(E, t)
  @test K == "II"
  @test f == 2
  @test c == 1
  @test s == true

   _, K, f, c, s = tates_algorithm_local(E, t - 1728)
  @test K == "III*"
  @test f == 2
  @test c == 2
  @test s == true

  E = elliptic_curve_from_j_invariant(t^3 + t + 1)
   _, K, f, c, s = tates_algorithm_local(E, 1//t)
  @test K == "I3"
  @test f == 1
  @test c == 3
  @test s == true

   _, K, f, c, s = tates_algorithm_local(E, t^3 + t - 1727)
  @test K == "III*"
  @test f == 2
  @test c == 2
  @test s == true

   _, K, f, c, s = tates_algorithm_local(E, t^3 + t + 1)
  @test K == "II"
  @test f == 2
  @test c == 1
  @test s == true

  k, a = quadratic_field(2)
  kt, t = rational_function_field(k, "t")
  E = elliptic_curve_from_j_invariant(1//(t^2 + t + a))

   _, K, f, c, s = tates_algorithm_local(E, 1//t)
  @test K == "IV"
  @test f == 2
  @test c == 1
  @test s == true

   _, K, f, c, s = tates_algorithm_local(E, t^2 + t + 1//1728*(1728*a - 1))
  @test K == "III*"
  @test f == 2
  @test c == 2
  @test s == true

   _, K, f, c, s = tates_algorithm_local(E, t^2 + t + a)
  @test K == "I1"
  @test f == 1
  @test c == 1
  @test s == true

  kt, t = rational_function_field(GF(2), "t")
  E = elliptic_curve_from_j_invariant(t^3/(t^2 + t + 1))
   _, K, f, c, s = tates_algorithm_local(E, t^2 + t + 1)
  @test K == "I1"
  @test f == 1
  @test c == 1
  @test s == true
   _, K, f, c, s = tates_algorithm_local(E, t)
  @test K == "I0*"
  @test f == 5
  @test c == 2
  @test s == true
   _, K, f, c, s = tates_algorithm_local(E, 1//t)
  @test K == "I1"
  @test f == 1
  @test c == 1
  @test s == true

  kt,t = rational_function_field(GF(113),:t)
  ainvs = kt.([(66*t^7 + 86*t^3)//(t^8 + 31*t^4 + 99), (41*t^14 + 34*t^10 + 72*t^6 + 47*t^2)//(t^16 + 62*t^12 + 29*t^8 + 36*t^4 + 83), (65*t^17 + 48*t^13 + 71*t^9 + 48*t^5 + 6*t)//(t^24 + 93*t^20 + 16*t^16 + 67*t^12 + 2*t^8 + 35*t^4 + 81), (58*t^24 + 93*t^20 + 98*t^16 + 26*t^12 + 55*t^8 + 46*t^4 + 15)//(t^32 + 11*t^28 + 60*t^24 + 52*t^20 + 47*t^16 + 63*t^12 + 8*t^8 + 100*t^4 + 109), 0])
  E = elliptic_curve(ainvs)

  @test all(isone(denominator(i)) for i in a_invariants(integral_model(E)[1]))
  Eglobal = tates_algorithm_global(E)
  ainvs_minimal = kt.([0, 103*t^4 + 53*t^2 + 78, 0, 14*t^8 + 61*t^6 + 2*t^4 + 44*t^2 + 50, 86*t^12 + 59*t^10 + 93*t^8 + 27*t^6 + 109*t^4 + 17*t^2 + 48])
  @test elliptic_curve(ainvs_minimal) == Eglobal
end

