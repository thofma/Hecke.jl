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
end
