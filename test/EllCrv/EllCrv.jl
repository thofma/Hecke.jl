@testset "Generic elliptic curve" begin

  @testset "Constructors" begin
    @test_throws ErrorException EllipticCurve([1])
    @test_throws ErrorException EllipticCurve([1, 2, 3])
    @test_throws ErrorException EllipticCurve([1, 2, 3, 4, 5, 6])
    @test_throws ErrorException EllipticCurve([0, 0])
    @test_throws ErrorException EllipticCurve([0, 0, 0, 0, 0])

    E = @inferred EllipticCurve([1, 2], false)
    @test typeof(E) == EllCrv{fmpq}

    E = @inferred EllipticCurve([1, 2, 3, 4, 5])
    @test typeof(E) == EllCrv{fmpq}

    # this is Cremona: 11a2, lmfdb: 11.a1
    E11_a1 = @inferred EllipticCurve([0, -1, 1, -7820, -263580], false)

    # this is Cremona: 41a1, lmfdb: 41.a1
    E43_a1 = @inferred EllipticCurve([0, 1, 1, 0, 0])

    Qx, x = PolynomialRing(FlintQQ, "x")
    K, a = NumberField(x^2 - x - 1, "a")
    OK = maximal_order(K)

    E31_1_a1 = @inferred EllipticCurve([K(1), a + 1, a, a, K(0)])
    @test typeof(E31_1_a1) == EllCrv{nf_elem}

    # lmfdb: 116.1-a1
    E116_1_a1 = @inferred EllipticCurve([K(1), K(-1), a, -a, K(0)] )
    @test typeof(E31_1_a1) == EllCrv{nf_elem}

    # short example
    Eshort = @inferred EllipticCurve([4, 0])
    @test typeof(Eshort) == EllCrv{fmpq}
  end

  # The following curves will be used in later tests
  # Creation of these was tested in previous testset
  E11_a1 = EllipticCurve([0, -1, 1, -7820, -263580], false)

  E43_a1 = EllipticCurve([0, 1, 1, 0, 0])

  Qx, x = PolynomialRing(FlintQQ, "x")
  K, a = NumberField(x^2 - x - 1, "a")
  OK = maximal_order(K)

  E31_1_a1 = EllipticCurve([K(1), a + 1, a, a, K(0)])

  E116_1_a1 =EllipticCurve([K(1), K(-1), a, -a, K(0)] )

  Eshort = EllipticCurve([4, 0])

  @testset "Field access" begin
    @test base_field(E11_a1) == FlintQQ
    @test base_field(E43_a1) == FlintQQ
    @test base_field(E31_1_a1) == K
    @test base_field(E116_1_a1) == K
    @test base_field(Eshort) == FlintQQ
  end

  @testset "Weierstraß model computation" begin
    E = EllipticCurve([1,2,3,4,5])
    EE, f, g = @inferred short_weierstrass_model(E)
    @test isshort(EE)
    @test EE.coeff == [fmpq(61, 16), fmpq(127, 32)]
    P = E([1, 2])
    @test P == g(f(P))

    R = ResidueRing(FlintZZ, 5)
    E = EllipticCurve(map(R, [1, 2, 3, 4, 5]))
    EE, f, g = @inferred short_weierstrass_model(E)
    @test isshort(EE)
    @test EE.coeff == [R(1), R(1)]
    P = rand(EE)
    @test P == f(g(P))
    # @inferred will break the tests
  end

  @testset "Point construction" begin
    P = @inferred E43_a1([FlintQQ(-1), FlintQQ(0)])
    @test typeof(P) == EllCrvPt{fmpq}
    @test parent(P) == E43_a1
    @test @inferred isfinite(P)
    @test @inferred !isinfinite(P)

    P = @inferred E43_a1([-1, 0], false)
    @test typeof(P) == EllCrvPt{fmpq}
    @test parent(P) == E43_a1
    @test @inferred isfinite(P)
    @test @inferred !isinfinite(P)

    P = @inferred E43_a1([fmpz(-1), fmpz(0)])
    @test typeof(P) == EllCrvPt{fmpq}
    @test parent(P) == E43_a1
    @test @inferred isfinite(P)
    @test @inferred !isinfinite(P)

# the error is/was from doing QQ(K(0)) - which is possible now    
#    @test_throws MethodError E43_a1([gen(K), gen(K)])

    @test_throws ErrorException E43_a1([2, 2])

    P = @inferred infinity(E43_a1)
    @test @inferred !isfinite(P)
    @test @inferred isinfinite(P)

    P = @inferred E43_a1([FlintQQ(-1), FlintQQ(0)])

    P = @inferred E116_1_a1([K(0), -K(a)])
    @test typeof(P) == EllCrvPt{nf_elem}
    @test parent(P) == E116_1_a1
    @test @inferred isfinite(P)
    @test @inferred !isinfinite(P)

    P = @inferred infinity(E116_1_a1)
    @test !isfinite(P)
    @test isinfinite(P)

    @test_throws ErrorException E116_1_a1([1, 1])

    P = @inferred Eshort([2, 4], false)
    @test @inferred isfinite(P)
    @test typeof(P) == EllCrvPt{fmpq}
    @test parent(P) == Eshort
  end

  @testset "Discriminant" begin
    @test (2*a + 10)*OK == @inferred (disc(E116_1_a1)*OK)
    @test -43 == @inferred disc(E43_a1)
  end

  @testset "j-invariant" begin
    b = (fmpq(-215055, 58) * a - fmpq(65799, 29))
    @test  b == @inferred j_invariant(E116_1_a1)
    @test fmpq(-4096, 43) == @inferred j_invariant(E43_a1)
  end

  @testset "Point aritmetic" begin
    #addition
    P = @inferred E43_a1([FlintQQ(-1), FlintQQ(0)])
    O = infinity(E43_a1)

    @test P == @inferred P + O
    @test E43_a1([2, -4]) == P + P
    @test E43_a1([fmpq(-2, 9), fmpq(1, 27)]) == P + P + P

    P = @inferred E116_1_a1([K(0), -K(a)])
    @test E116_1_a1([1, -1]) == @inferred P + P
    @test E116_1_a1([K(1), -a]) == @inferred P + P + P
    @test infinity(E116_1_a1) == @inferred P + P + P + P + P
    @test P == @inferred P + infinity(E116_1_a1)

    P = @inferred Eshort([2, 4])
    O = @inferred infinity(Eshort)
    @test_throws ErrorException Eshort([-1, -1])

    @test Eshort([0, 0]) == @inferred P + P
    @test P == @inferred O + P

    P = Eshort([2, 4])
    @test Eshort([2, -4]) == @inferred -P
    P = infinity(Eshort)
    @test P == @inferred -P

    P = E43_a1([-1, 0])
    @test E43_a1([-1, -1]) == @inferred -P
    P = infinity(E43_a1)
    @test P == @inferred -P

    # inversion
    P = @inferred E116_1_a1([K(0), -K(a)])
    @test E116_1_a1([0, 0]) == @inferred -P
    P = infinity(E116_1_a1)
    @test P == @inferred -P

    # equality
    P1 = Eshort([2, 4])
    @test @inferred ==(P1, P1)
    P2 = infinity(Eshort)
    @test @inferred ==(P2, P2)
    @test @inferred !==(P2, P1)

    P1 = E43_a1([-1, 0])
    @test @inferred ==(P1, P1)
    P2 = infinity(E43_a1)
    @test @inferred ==(P2, P2)
    @test @inferred !==(P2, P1)

    P1 = E116_1_a1([K(0), -K(a)])
    @test @inferred ==(P1, P1)
    P2 = infinity(E116_1_a1)
    @test @inferred ==(P2, P2)
    @test @inferred !==(P2, P1)

    # scalar multiplication
    P1 = Eshort([2, 4])
    @test Eshort([0, 0]) == @inferred 2*P1
    @test infinity(Eshort) == @inferred 4*P1

    P1 = E43_a1([-1, 0])
    @test E43_a1([fmpq(11, 49), fmpq(-363, 343)]) == @inferred 4*P1

    P1 = E116_1_a1([K(0), -K(a)])
    @test E116_1_a1([K(0), K(0)]) == @inferred 4*P1
    @test infinity(E116_1_a1) == @inferred 5*P1
  end
end
