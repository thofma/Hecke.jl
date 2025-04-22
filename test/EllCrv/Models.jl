@testset "Models of elliptic curves" begin
  @testset "Weierstraß model computation" begin
    E = elliptic_curve([1,2,3,4,5])
    EE, f, g = @inferred short_weierstrass_model(E)
    @test is_short_weierstrass_model(EE)
    @test a_invariants(EE) == (0, 0, 0, QQFieldElem(61, 16), QQFieldElem(127, 32))
    P = E([1, 2])
    @test P == g(f(P))

    R = GF(5)
    E = elliptic_curve(map(R, [1, 2, 3, 4, 5]))
    EE, f, g = @inferred short_weierstrass_model(E)
    @test is_short_weierstrass_model(EE)
    @test a_invariants(EE) == (0, 0, 0, R(1), R(1))
    P = rand(EE)
    @test P == f(g(P))
    # @inferred will break the tests
  end
  @testset "Simplified model computation" begin
    #j!=0
    R = GF(2, 5)
    o = gen(R)
    E = elliptic_curve(map(R, [o^3, 1+o, 1, 1, o^2+o+1]))
    EE, f, g = @inferred simplified_model(E)
    @test is_simplified_model(EE)
    @test a_invariants(EE) == (1, o^4 + o^3 + o + 1, 0, 0, o^2 + 1)
    P = rand(EE)
    @test P == f(g(P))

    #j=0
    o = gen(R)
    E = elliptic_curve(map(R, [0, o^3 + o, o^3 + o^2 + 1, o^3 + o^2 + o, o + 1]))
    EE, f, g = @inferred simplified_model(E)
    @test is_simplified_model(EE)
    @test a_invariants(EE) == (0, 0, o^3 + o^2 + 1, 0, 0)
    P = rand(EE)
    @test P == f(g(P))

    #j!=0
    R = GF(3, 5)
    o = gen(R)
    E = elliptic_curve(map(R, [o^3, 1+o, 1, 1, o^2+o+1]))
    EE, f, g = @inferred simplified_model(E)
    @test is_simplified_model(EE)
    @test a_invariants(EE) == (0, o^2 + 1, 0, 0, o^4 + 2*o^3 + o + 2)
    P = rand(EE)
    @test P == f(g(P))

    #j=0
    E = elliptic_curve(map(R, [2*o^4 + 2*o^3 + o^2 + o + 1, 2*o^4 + 2*o^3 + o + 1, 0, o^4 + 2*o^3 + o^2, o^3 + o + 2]))
    EE, f, g = @inferred simplified_model(E)
    @test is_simplified_model(EE)
    @test a_invariants(EE) == (0, 0, 0, o^4 + 2*o^3 + o^2, o^3 + o + 2)
    P = rand(EE)
    @test P == f(g(P))

  end

end
