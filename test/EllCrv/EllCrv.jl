@testset "Generic elliptic curve" begin

  @testset "Constructors" begin
    @test_throws ErrorException elliptic_curve([1])
    @test_throws ErrorException elliptic_curve([1, 2, 3])
    @test_throws ErrorException elliptic_curve([1, 2, 3, 4, 5, 6])
    @test_throws ErrorException elliptic_curve([0, 0])
    @test_throws ErrorException elliptic_curve([0, 0, 0, 0, 0])

    E = @inferred elliptic_curve([1, 2], check = false)
    @test typeof(E) == EllipticCurve{QQFieldElem}
    @test a_invariants(E) == (0, 0, 0, 1, 2)
    @test coefficients(E) == (0, 0, 0, 1, 2)

    E = @inferred elliptic_curve([1, 2, 3, 4, 5])
    @test typeof(E) == EllipticCurve{QQFieldElem}
    @test a_invariants(E) == (1, 2, 3, 4, 5)

    # this is Cremona: 11a2, lmfdb: 11.a1
    E11_a1 = @inferred elliptic_curve([0, -1, 1, -7820, -263580], check = false)

    # this is Cremona: 41a1, lmfdb: 41.a1
    E43_a1 = @inferred elliptic_curve([0, 1, 1, 0, 0])

    E = @inferred elliptic_curve([0, 0, 0, 1, 2])
    @test is_short_weierstrass_model(E)

    E = @inferred elliptic_curve([0, 0, 0, 1, 2], check = false)
    @test is_short_weierstrass_model(E)

    Qx, x = polynomial_ring(FlintQQ, "x")

    f1 = x^3+3*x+5
    g1 = x+2
    E = elliptic_curve(f1, g1)
    f2, g2 = hyperelliptic_polynomials(E)
    @test f1 == f2 && g1 == g2

    E = @inferred elliptic_curve(f1)
    @test E isa EllipticCurve{QQFieldElem}
    E = @inferred elliptic_curve(f1, check = false)
    @test E isa EllipticCurve{QQFieldElem}

    E = elliptic_curve(f1, 1)
    f2, g2 = hyperelliptic_polynomials(E)
    @test f1 == f2 && 1 == g2

    E = elliptic_curve(x^3 + 1, zero(Qx))
    @test E isa EllipticCurve{QQFieldElem}

    @test_throws ArgumentError elliptic_curve(x^10-21, x^3+5)
    @test_throws ArgumentError elliptic_curve(x^3+3, x^3+5)
    @test_throws ArgumentError elliptic_curve(3*x^3 + 1)

    K, a = number_field(x^2 - x - 1, "a")
    OK = maximal_order(K)

    E31_1_a1 = @inferred elliptic_curve([K(1), a + 1, a, a, K(0)])
    @test typeof(E31_1_a1) == EllipticCurve{AbsSimpleNumFieldElem}

    # lmfdb: 116.1-a1
    E116_1_a1 = @inferred elliptic_curve([K(1), K(-1), a, -a, K(0)] )
    @test typeof(E31_1_a1) == EllipticCurve{AbsSimpleNumFieldElem}

    # short example
    Eshort = @inferred elliptic_curve([4, 0])
    @test typeof(Eshort) == EllipticCurve{QQFieldElem}
    @test a_invariants(Eshort) == (0, 0, 0, 4, 0)
  end

  QQx, = polynomial_ring(QQ, 5)
  F = fraction_field(QQx)
  a1, a2, a3, a4, a6 = F.(gens(QQx))
  E = elliptic_curve([a1, a2, a3, a4, a6])
  @test b_invariants(E) == (a1^2 + 4*a2, a1*a3 + 2*a4, a3^2 + 4*a6, a1^2*a6 - a1*a3*a4 + a2*a3^2 + 4*a2*a6 - a4^2)
  b2,b4,b6,b8 = b_invariants(E)
  c4, c6 = c_invariants(E)
  @test (c4, c6) == c_invariants(E) # to test caching
  @test (c4, c6) == (a1^4 + 8*a1^2*a2 - 24*a1*a3 + 16*a2^2 - 48*a4, -a1^6 - 12*a1^4*a2 + 36*a1^3*a3 - 48*a1^2*a2^2 + 72*a1^2*a4 + 144*a1*a2*a3 - 64*a2^3 + 288*a2*a4 - 216*a3^2 - 864*a6)
  @test c4 == b2^2 - 24*b4
  @test c6 == -b2^3 + 36*b2*b4 - 216*b6
  d = discriminant(E)
  @test d == -b2^2*b8 - 8*b4^3 - 27*b6^2 + 9*b2*b4*b6
  @test 1728*d == c4^3 - c6^2

  # base change
  E = elliptic_curve([1, 0, 0, 0, 1])
  K, = quadratic_field(-1)
  EK = @inferred base_change(K, E)
  @test a_invariants(EK) == (1, 0, 0, 0, 1)
  @test base_field(EK) === K

  F = GF(2)
  f = x -> divexact(F(numerator(x)), F(denominator(x)))
  EF = base_change(f, E)
  @test a_invariants(EF) == (1, 0, 0, 0, 1)
  @test base_field(EF) === F

  # The following curves will be used in later tests
  # Creation of these was tested in previous testset
  E11_a1 = elliptic_curve([0, -1, 1, -7820, -263580], check =false)

  E43_a1 = elliptic_curve([0, 1, 1, 0, 0])

  Qx, x = polynomial_ring(FlintQQ, "x")
  K, a = number_field(x^2 - x - 1, "a")
  OK = maximal_order(K)

  E31_1_a1 = elliptic_curve([K(1), a + 1, a, a, K(0)])

  E116_1_a1 =elliptic_curve([K(1), K(-1), a, -a, K(0)] )

  Eshort = elliptic_curve([4, 0])

  @testset "Field access" begin
    @test base_field(E11_a1) == FlintQQ
    @test base_field(E43_a1) == FlintQQ
    @test base_field(E31_1_a1) == K
    @test base_field(E116_1_a1) == K
    @test base_field(Eshort) == FlintQQ
  end

  @testset "Point construction" begin
    P = @inferred E43_a1([FlintQQ(-1), FlintQQ(0)])
    @test typeof(P) == EllipticCurvePoint{QQFieldElem}
    @test parent(P) == E43_a1
    @test @inferred is_finite(P)
    @test @inferred !is_infinite(P)

    P = @inferred E43_a1([-1, 0], check = false)
    @test typeof(P) == EllipticCurvePoint{QQFieldElem}
    @test parent(P) == E43_a1
    @test @inferred is_finite(P)
    @test @inferred !is_infinite(P)

    P = @inferred E43_a1([ZZRingElem(-1), ZZRingElem(0)])
    @test typeof(P) == EllipticCurvePoint{QQFieldElem}
    @test parent(P) == E43_a1
    @test @inferred is_finite(P)
    @test @inferred !is_infinite(P)

# the error is/was from doing QQ(K(0)) - which is possible now
#    @test_throws MethodError E43_a1([gen(K), gen(K)])

    @test_throws ErrorException E43_a1([2, 2])

    P = @inferred infinity(E43_a1)
    @test @inferred !is_finite(P)
    @test @inferred is_infinite(P)

    P = @inferred E43_a1([FlintQQ(-1), FlintQQ(0)])

    P = @inferred E116_1_a1([K(0), -K(a)])
    @test typeof(P) == EllipticCurvePoint{AbsSimpleNumFieldElem}
    @test parent(P) == E116_1_a1
    @test @inferred is_finite(P)
    @test @inferred !is_infinite(P)

    P = @inferred infinity(E116_1_a1)
    @test !is_finite(P)
    @test is_infinite(P)

    @test_throws ErrorException E116_1_a1([1, 1])

    P = @inferred Eshort([2, 4], check = false)
    @test @inferred is_finite(P)
    @test typeof(P) == EllipticCurvePoint{QQFieldElem}
    @test parent(P) == Eshort

    E = elliptic_curve(GF(7,2),[1,2,3,4,5])
    L = @inferred points_with_x_coordinate(E,0)
    @test E([0,5]) in L && E([0, 6]) in L


  end

  @testset "Equation" begin
    E = elliptic_curve( [1, 2, 3, 4, 5])
    Kxy, (x,y) = polynomial_ring(base_field(E), ["x","y"])
    @test y^2 + x*y + 3*y - x^3 - 2*x^2 - 4*x - 5 == @inferred Kxy(equation(E))
  end

  @testset "Discriminant" begin
    @test (2*a + 10)*OK == @inferred (discriminant(E116_1_a1)*OK)
    @test -43 == @inferred discriminant(E43_a1)
    @test -4096 == @inferred discriminant(Eshort)
    E43_a1 = elliptic_curve([0, 1, 1, 0, 0], check = false)
    @test discriminant(E43_a1) == -43
    Eshort = @inferred elliptic_curve([4, 0], check = false)
    @test discriminant(Eshort) == -4096
  end

  @testset "j-invariant" begin
    b = (QQFieldElem(-215055, 58) * a - QQFieldElem(65799, 29))
    @test  b == @inferred j_invariant(E116_1_a1)
    @test QQFieldElem(-4096, 43) == @inferred j_invariant(E43_a1)
    @test 1728 == @inferred j_invariant(Eshort)

    E = @inferred elliptic_curve_from_j_invariant(23)
    @test j_invariant(E) == 23

    E = @inferred elliptic_curve_from_j_invariant(1728)
    @test j_invariant(E) == 1728

    E = @inferred elliptic_curve_from_j_invariant(GF(3,2)(0))
    @test j_invariant(E) == 0

    E = @inferred elliptic_curve_from_j_invariant(GF(2,4)(0))
    @test j_invariant(E) == 0

  end

  @testset "Point arithmetic" begin
    #addition
    P = @inferred E43_a1([FlintQQ(-1), FlintQQ(0)])
    O = infinity(E43_a1)

    @test P == @inferred P + O
    @test E43_a1([2, -4]) == P + P
    @test E43_a1([QQFieldElem(-2, 9), QQFieldElem(1, 27)]) == P + P + P

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
    @test E43_a1([QQFieldElem(11, 49), QQFieldElem(-363, 343)]) == @inferred 4*P1

    P1 = E116_1_a1([K(0), -K(a)])
    @test E116_1_a1([K(0), K(0)]) == @inferred 4*P1
    @test infinity(E116_1_a1) == @inferred 5*P1

    #division

    P1 = Eshort([2, 4])
    Q = (2*P1)//2
    @test Q == P1 || Q == -P1

    P1 = E116_1_a1([K(0), -K(a)])
    @test (3*P1)//3 == P1
    @test @inferred 3*(3*P1)//(-3) == -3*P1
    @test_throws ErrorException P1//5
  end
end

@testset "additional constructors" begin
  R, (x, y) = polynomial_ring(QQ, [:x, :y])
  f = y^2 - x^3 - 3*x^2 + 7*x - 4
  elliptic_curve(f, x, y)

  pt, t = polynomial_ring(QQ, :t)
  kt = fraction_field(pt)
  R, (x, y) = polynomial_ring(kt, [:x, :y])
  f = y^2 - x^3 - 3*t*x^2 + 7*x - 4*t^2 - 3
  elliptic_curve(f, x, y)
end
