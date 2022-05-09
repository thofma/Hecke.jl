@testset "Models of elliptic curves" begin
  @testset "Weierstraß model computation" begin
    E = EllipticCurve([1,2,3,4,5])
    EE, f, g = @inferred short_weierstrass_model(E)
    @test is_short_weierstrass_model(EE)
    @test a_invars(EE) == (0, 0, 0, fmpq(61, 16), fmpq(127, 32))
    P = E([1, 2])
    @test P == g(f(P))

    R = GF(5)
    E = EllipticCurve(map(R, [1, 2, 3, 4, 5]))
    EE, f, g = @inferred short_weierstrass_model(E)
    @test is_short_weierstrass_model(EE)
    @test a_invars(EE) == (0, 0, 0, R(1), R(1))
    P = rand(EE)
    @test P == f(g(P))
    # @inferred will break the tests
  end
  
end
