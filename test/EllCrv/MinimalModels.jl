@testset "Minimal models of elliptic curves" begin

  @testset "Minimal model (Laska-Kraus-Connell)" begin
    E = elliptic_curve([1,2,3,4,5])
    EE, phi = @inferred minimal_model(E)
    @test a_invariants(EE) == (1, -1, 0, 4, 3)
    EE = @inferred tates_algorithm_global(E)
    @test a_invariants(EE) == (1, -1, 0, 4, 3)

    E = elliptic_curve([625, -15625, 19531250, -2929687500, -34332275390625])
    EE, phi = @inferred minimal_model(E)
    @test a_invariants(EE) == (1, -1, 0, 4, 3)
    EE = @inferred tates_algorithm_global(E)
    @test a_invariants(EE) == (1, -1, 0, 4, 3)

    F, phi = minimal_model(elliptic_curve([6^2*3^3, 6^5*2^2]))
    @test a_invariants(F) == (0, 0, 0, 972, 31104)

    F, phi = minimal_model(elliptic_curve([2^2*15, 2^4*15]))
    @test a_invariants(F) == (0, 0, 0, 60, 240)

  end

  @testset "Global minimal models" begin
    Rx, x = polynomial_ring(QQ, "x")
    K, a = number_field(x^2-x+1)
    OK = ring_of_integers(K)
    E = elliptic_curve(K, [1, -1, 0, 6 - 57*a, 108 - 162*a])
    F, phi = transform_rstu(E,[a, 0, -3+a, 7])
    F, phi = integral_model(F)
    F, phi = @inferred minimal_model(F)
    minD = @inferred minimal_discriminant(E)
    D = discriminant(F)*OK
    @test_broken minD == D

    K, a = quadratic_field(10)
    OK = ring_of_integers(K)
    E = elliptic_curve(K, [0,0,0,-186408*a - 589491, 78055704*a + 246833838])
    minD = @inferred minimal_discriminant(E)
    F, phi, phi_inv, P = @inferred semi_global_minimal_model(E)
    D = discriminant(F)*OK
    @test minD*P^12 == D
    @test has_global_minimal_model(E) == true

    Qx, x = polynomial_ring(QQ, "x")
    K, a = number_field(x^2-x+31821453)
    OK = ring_of_integers(K)
    E = elliptic_curve(K, [0, 0, 0, -382586771000351226384*a - 2498023791133552294513515, 358777608829102441023422458989744*a + 1110881475104109582383304709231832166])
    minD = @inferred minimal_discriminant(E)
    F, phi, phi_inv, P = @inferred semi_global_minimal_model(E)
    @test has_global_minimal_model(E) == false
    D = discriminant(F)*OK
    @test minD*P^12 == D
  end

  # _minimize and integral model
  Kt, t = rational_function_field(QQ, "t")
  E = elliptic_curve(Kt.([0, t^21, 1//216, -7//1296, 1//t]))
  EE, = integral_model(E)
  @test all(p -> is_one(denominator(p)) && is_one(denominator(numerator(p))), a_invariants(EE))
  EE = Hecke.reduce_model(E)
  @test all(p -> is_one(denominator(p)) && is_one(denominator(numerator(p))), a_invariants(EE))

  Qx, x = QQ["x"]
  K, z = number_field(x^2 + 1, "z", cached = false)
  Kt, t = rational_function_field(K, "t")
  E = elliptic_curve(Kt.([0, t^21, (z + 1)//216, -7//1296, (z + 3)//t]))
  EE, = integral_model(E)
  EE = Hecke.reduce_model(E)

  let
    Qx, x = QQ["x"]
    K, a = number_field(x^16 + 36*x^12 - 120*x^10 + 392*x^8 - 432*x^6 + 216*x^4 - 48*x^2 + 4, "x")
    Kt, t = rational_function_field(K, "t")
    p = ((101//168*x^15 - 1//84*x^13 + 905//42*x^11 - 6101//84*x^9 + 19627//84*x^7 - 5356//21*x^5 + 4379//42*x^3 - 67//6*x)*t^7 + (17//56*x^15 - 1//42*x^13 + 919//84*x^11 - 149//4*x^9 + 3425//28*x^7 - 5905//42*x^5 + 1627//21*x^3 - 185//14*x)*t^3)//(t^8 + (11//42*x^14 - 5//42*x^12 + 65//7*x^10 - 752//21*x^8 + 2347//21*x^6 - 3067//21*x^4 + 428//7*x^2 - 164//21)*t^4 + 29//42*x^14 + 13//42*x^12 + 524//21*x^10 - 502//7*x^8 + 4975//21*x^6 - 565//3*x^4 + 1082//21*x^2 - 5)
    fun = Hecke._factor_rational_function_field(p)
    @test unit(fun) * prod(q^e for (q, e) in fun) == p
  end
end

