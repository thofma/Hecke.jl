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
end

