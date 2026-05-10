@testset "Minimal models of elliptic curves" begin
  function test_minimal_model_at_bad_primes(E, minD)
    for p in bad_primes(E)
      v = Hecke._tates_algorithm(E, p).discriminant_valuation
      @test v == valuation(discriminant(minimal_model(E, p)[1]), p)
      @test v == valuation(minD, p)
    end
  end

  @testset "Minimal model over QQ" begin
    E = elliptic_curve([1,2,3,4,5])
    F, _ = @inferred minimal_model(E)
    @test a_invariants(F) == (1, -1, 0, 4, 3)
    F = @inferred tates_algorithm_global(E)
    @test a_invariants(F) == (1, -1, 0, 4, 3)
    minD = @inferred minimal_discriminant(E)
    @test minD == abs(discriminant(F))
    test_minimal_model_at_bad_primes(E, minD)

    E = elliptic_curve([625, -15625, 19531250, -2929687500, -34332275390625])
    F, _ = @inferred minimal_model(E)
    @test a_invariants(F) == (1, -1, 0, 4, 3)
    F = @inferred tates_algorithm_global(E)
    @test a_invariants(F) == (1, -1, 0, 4, 3)
    minD = @inferred minimal_discriminant(E)
    @test minD == abs(discriminant(F))
    test_minimal_model_at_bad_primes(E, minD)

    E = elliptic_curve([6^2*3^3, 6^5*2^2])
    F, _ = @inferred minimal_model(E)
    @test a_invariants(F) == (0, 0, 0, 972, 31104)
    minD = @inferred minimal_discriminant(E)
    @test minD == abs(discriminant(F))
    test_minimal_model_at_bad_primes(E, minD)

    E = elliptic_curve([2^2*15, 2^4*15])
    F, _ = minimal_model(E)
    @test a_invariants(F) == (0, 0, 0, 60, 240)
    minD = @inferred minimal_discriminant(E)
    @test minD == abs(discriminant(F))
    test_minimal_model_at_bad_primes(E, minD)
  end

  @testset "Minimal model over number field" begin
    x = gen(Hecke.Globals.Qx)
    K, a = number_field(x^2 - x + 1; cached = false)
    OK = ring_of_integers(K)
    E = elliptic_curve(K, [1, -1, 0, 6 - 57*a, 108 - 162*a])
    minD = @inferred minimal_discriminant(E)

    F, phi, phi_inv, P = @inferred semi_global_minimal_model(E)
    @test has_global_minimal_model(E) == true
    D = discriminant(F)*OK
    @test minD == D
    @test is_one(P)
    test_minimal_model_at_bad_primes(E, minD)

    F, _ = transform_rstu(E,[a, 0, -3+a, 7])
    F, _ = @inferred minimal_model(integral_model(F)[1])
    D = discriminant(F)*OK
    @test minD == D
    test_minimal_model_at_bad_primes(F, minD)

    K, a = quadratic_field(10; cached = false)
    OK = ring_of_integers(K)
    E = elliptic_curve(K, [0,0,0,-186408*a - 589491, 78055704*a + 246833838])
    minD = @inferred minimal_discriminant(E)
    F, phi, phi_inv, P = @inferred semi_global_minimal_model(E)
    @test has_global_minimal_model(E) == true
    D = discriminant(F)*OK
    @test minD == D
    @test is_one(P)
    test_minimal_model_at_bad_primes(E, minD)

    K, a = number_field(x^2 - x + 31821453; cached = false)
    OK = ring_of_integers(K)
    E = elliptic_curve(K, [0, 0, 0, -382586771000351226384*a - 2498023791133552294513515, 358777608829102441023422458989744*a + 1110881475104109582383304709231832166])
    minD = @inferred minimal_discriminant(E)
    F, phi, phi_inv, P = @inferred semi_global_minimal_model(E)
    @test has_global_minimal_model(E) == false
    D = discriminant(F)*OK
    @test minD*P^12 == D
    @test !is_one(P)
    @test bad_primes(F) == [P]
    test_minimal_model_at_bad_primes(E, minD)
  end

  function test_minimal_model_rff(E, minD)
    # minimal discriminant prime factors are bad primes
    @test issubset(first.(minD), bad_primes(E))
    # test minimal discriminant is returned as actual support
    @test all(e > 0 for (_, e) in minD)

    # test minimal_model(E, p) agrees with minimal discriminant
    for (p, e) in minD
      v = Hecke._tates_algorithm(E, p).discriminant_valuation
      @test v == e
      @test v == valuation(discriminant(minimal_model(E, p)[1]), p)
    end

    dDict = Dict(minD)
    cDict = Dict(conductor(E))
    # minimal discriminant support is same as conductor
    @test keys(dDict) == keys(cDict)
    # Ogg-Saito: vD = fp + mp - 1 >= fp
    @test all(dDict[p] >= cDict[p] for p in keys(dDict))
  end

  @testset "Minimal model over rational function field" begin
    K, t = rational_function_field(QQ, :t; cached = false)
    E = elliptic_curve_from_j_invariant(t)
    @test issetequal(@inferred(bad_primes(E)), K.([t, t - 1728, 1//t]))
    minD = @inferred minimal_discriminant(E)
    test_minimal_model_rff(E, minD)

    E = elliptic_curve_from_j_invariant(t^3 + t + 1)
    @test issetequal(@inferred(bad_primes(E)), K.([t^3 + t - 1727, t^3 + t + 1, 1//t]))
    minD = @inferred minimal_discriminant(E)
    test_minimal_model_rff(E, minD)

    E = elliptic_curve_from_j_invariant((t+1)//t)
    @test issetequal(@inferred(bad_primes(E)), K.([1727*t - 1, t, t+1, 1//t]))
    minD = @inferred minimal_discriminant(E)
    test_minimal_model_rff(E, minD)

    E = elliptic_curve(K, [0, t, 0, t^4, 0])
    # NOTE: bad_primes prefers to have polynomials with integer coefficients
    # in LocalData.jl we have same primes but written as t - 1//2, t + 1//2
    @test issetequal(@inferred(bad_primes(E)), K.([2*t - 1, 2*t + 1, t, 1//t]))
    minD = @inferred minimal_discriminant(E)
    test_minimal_model_rff(E, minD)

    K, t = rational_function_field(GF(2), :t; cached = false)
    E = elliptic_curve_from_j_invariant(t^3//(t^2 + t + 1))
    @test issetequal(@inferred(bad_primes(E)), K.([t, t^2 + t + 1, 1//t]))
    minD = @inferred minimal_discriminant(E)
    test_minimal_model_rff(E, minD)
  end

  # _minimize and integral model
  Kt, t = rational_function_field(QQ, :t; cached = false)
  E = elliptic_curve(Kt.([0, t^21, 1//216, -7//1296, 1//t]))
  EE, = integral_model(E)
  @test all(p -> is_one(denominator(p)) && is_one(denominator(numerator(p))), a_invariants(EE))
  EE = Hecke.reduce_model(E)
  @test all(p -> is_one(denominator(p)) && is_one(denominator(numerator(p))), a_invariants(EE))

  Qx, x = QQ["x"]
  K, z = number_field(x^2 + 1, :z; cached = false)
  Kt, t = rational_function_field(K, :t; cached = false)
  E = elliptic_curve(Kt.([0, t^21, (z + 1)//216, -7//1296, (z + 3)//t]))
  EE, = integral_model(E)
  EE = Hecke.reduce_model(E)

  let
    x = gen(Hecke.Globals.Qx)
    K, a = number_field(x^16 + 36*x^12 - 120*x^10 + 392*x^8 - 432*x^6 + 216*x^4 - 48*x^2 + 4, :x; cached = false)
    Kt, t = rational_function_field(K, :t; cached = false)
    p = ((101//168*x^15 - 1//84*x^13 + 905//42*x^11 - 6101//84*x^9 + 19627//84*x^7 - 5356//21*x^5 + 4379//42*x^3 - 67//6*x)*t^7 + (17//56*x^15 - 1//42*x^13 + 919//84*x^11 - 149//4*x^9 + 3425//28*x^7 - 5905//42*x^5 + 1627//21*x^3 - 185//14*x)*t^3)//(t^8 + (11//42*x^14 - 5//42*x^12 + 65//7*x^10 - 752//21*x^8 + 2347//21*x^6 - 3067//21*x^4 + 428//7*x^2 - 164//21)*t^4 + 29//42*x^14 + 13//42*x^12 + 524//21*x^10 - 502//7*x^8 + 4975//21*x^6 - 565//3*x^4 + 1082//21*x^2 - 5)
    fun = Hecke._factor_rational_function_field(p)
    @test unit(fun) * prod(q^e for (q, e) in fun) == p
  end
end

