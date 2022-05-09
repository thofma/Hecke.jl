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
    
    f1 = x^3+3*x+5
    g1 = x+2
    E = EllipticCurve(f1, g1)
    f2, g2 = hyperelliptic_polynomials(E)
    @test f1 == f2 && g1 == g2
    
    E = EllipticCurve(f1, 1)
    f2, g2 = hyperelliptic_polynomials(E)
    @test f1 == f2 && 1 == g2
    
    @test_throws AssertionError EllipticCurve(x^10-21, x^3+5)
    @test_throws AssertionError EllipticCurve(x^3+3, x^3+5)
    @test_throws ErrorException EllipticCurve(x^3, 0)
     
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

  @testset "Point construction" begin
    P = @inferred E43_a1([FlintQQ(-1), FlintQQ(0)])
    @test typeof(P) == EllCrvPt{fmpq}
    @test parent(P) == E43_a1
    @test @inferred is_finite(P)
    @test @inferred !is_infinite(P)

    P = @inferred E43_a1([-1, 0], false)
    @test typeof(P) == EllCrvPt{fmpq}
    @test parent(P) == E43_a1
    @test @inferred is_finite(P)
    @test @inferred !is_infinite(P)

    P = @inferred E43_a1([fmpz(-1), fmpz(0)])
    @test typeof(P) == EllCrvPt{fmpq}
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
    @test typeof(P) == EllCrvPt{nf_elem}
    @test parent(P) == E116_1_a1
    @test @inferred is_finite(P)
    @test @inferred !is_infinite(P)

    P = @inferred infinity(E116_1_a1)
    @test !is_finite(P)
    @test is_infinite(P)

    @test_throws ErrorException E116_1_a1([1, 1])

    P = @inferred Eshort([2, 4], false)
    @test @inferred is_finite(P)
    @test typeof(P) == EllCrvPt{fmpq}
    @test parent(P) == Eshort
    
    E = EllipticCurve(GF(7,2),[1,2,3,4,5])
    L = @inferred points_with_x(E,0)
    @test E([0,5]) in L && E([0, 6]) in L
    
    
  end

  @testset "Equation" begin
    E = EllipticCurve( [1, 2, 3, 4, 5])
    Kxy, (x,y) = PolynomialRing(base_field(E), ["x","y"])
    @test y^2 + x*y + 3*y - x^3 - 2*x^2 - 4*x - 5 == @inferred Kxy(equation(E))
  end

  @testset "Discriminant" begin
    @test (2*a + 10)*OK == @inferred (discriminant(E116_1_a1)*OK)
    @test -43 == @inferred discriminant(E43_a1)
    @test -4096 == @inferred discriminant(Eshort)
  end

  @testset "j-invariant" begin
    b = (fmpq(-215055, 58) * a - fmpq(65799, 29))
    @test  b == @inferred j_invariant(E116_1_a1)
    @test fmpq(-4096, 43) == @inferred j_invariant(E43_a1)
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
