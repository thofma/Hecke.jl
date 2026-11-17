@testset "Poly" begin

  K = padic_field(2, precision = 100)
  Kx, x = polynomial_ring(K, "x")
  L, gL = eisenstein_extension(x^2+2, "a")

  @testset "Norm" begin
    Qq, gQq = qadic_field(3, 2, precision = 20)
    for (F, a) in ((L, gL), (Qq, gQq))
      Fx, x = polynomial_ring(F, "x")
      R, y = polynomial_ring(base_field(F), "y", cached = false)
      f = x - a
      g = norm(R, f)
      expected = R(collect(coefficients(defining_polynomial(F))))
      @test parent(g) === R
      @test g == expected
      @test norm(R, x^2 - a) == expected(y^2)
      @test norm(R, f^2) == expected^2
      @test norm(R, x - 2) == (y - 2)^degree(F)

      h = norm(f)
      @test base_ring(h) === base_field(F)
      @test collect(coefficients(h)) == collect(coefficients(g))
      @test_throws ArgumentError norm(Fx, f)
    end
  end

  @testset "Fun Factor" for F in [K, L]
    Fx, x = polynomial_ring(F, "x")
    f = x^5
    for i = 0:4
      c = K(rand(ZZ, 1:100))
      f += c*x^i
    end
    u = 1
    for i = 1:5
      c = K(rand(ZZ, 1:100))
      u += 2*c*x^i
    end

    g = f*u
    u1, f1 = @inferred Hecke.fun_factor(g)
    @test u == u1
    @test f1 == f
  end

  @testset "Gcd" for F in [K, L]
    Fx, x = polynomial_ring(F, "x")
    f = (2*x+1)*(x+1)
    g = x^3+1
    gg = @inferred gcd(f, g)
    @test gg == x+1

    f = (2*x+1)*(x+1)
    g = (2*x+1)*(x+2)
    @test gcd(f, g) == 2*x+1

    f = (x + 1//K(2)) * (2*x^2+x+1)
    g = 2*x+1
    @test gcd(f, g) == g
    @test gcd(f, zero(Fx)) == f
    @test gcd(zero(Fx), f) == f
    @test iszero(gcd(zero(Fx), zero(Fx)))
  end

  @testset "Gcdx" for F in [K, L]
    Fx, x = polynomial_ring(F, "x")
    f = (2*x+1)*(x+1)
    g = x^3+1
    d, u, v = gcdx(f, g)
    @test d == gcd(f, g)
    @test u*f + v*g == d

    f = (2*x+1)*(x+1)
    g = (2*x+1)*(x+2)
    d, u, v = @inferred gcdx(f, g)
    @test gcd(f, g) == d
    @test d == u*f + v*g

    f = (x + 1//K(2)) * (2*x^2+x+1)
    g = 2*x+1
    d, u, v = gcdx(f, g)
    @test g == d
    @test u*f + v*g == d
  end

  @testset "Hensel" for F in [K, L]
    Fx, x = polynomial_ring(F, "x")
    f = (x+1)^3
    g = (x^2+x+1)
    h = x^2 +2*x + 8
    ff = f*g*h
    lf = @inferred Hecke.Hensel_factorization(ff)
    @test prod(values(lf)) == ff
  end

  @testset "Slope Factorization" for F in [K, L]
    Fx, x = polynomial_ring(F, "x")
    f = prod(x-2^i for i = 1:5)
    lf = @inferred Hecke.slope_factorization(f)
    @test prod(keys(lf)) == f
    @test all(x -> isone(degree(x)), keys(lf))
    @test length(Hecke.slope_factorization(2*x+1)) == 1
  end

  @testset "Roots" begin
    _, t = padic_field(3, precision = 10)["t"]
    f = ((t-1+81)*(t-1+2*81))
    rt = roots(f)
    @test length(rt) == 2
    @test allunique(rt)
    @test all(iszero, map(f, rt))
  end

  @testset "Roots with non-lifting residue roots" begin
    for p in (2, 3), n in (3, 10)
      Q, = qadic_field(p, 2, precision = n)
      for F in (padic_field(p, precision = n), Q)
        _, x = polynomial_ring(F, "x")
        @test isempty(@inferred Hecke.Hensel_factorization(F(p)*x + 1))
        @test isempty(@inferred Hecke.Hensel_factorization(parent(x)(1)))
        if p == 2
          f = x^3 + 3*x - 2
          rt = @inferred roots(f)
          @test length(rt) == 1
          @test all(iszero, map(f, rt))
        else
          @test isempty(@inferred roots(x^3 + 3*x - 1))
          @test isempty(@inferred roots(x^3 + 3*x - 2))
        end
      end
    end
  end

  @testset "Roots at low precision" begin
    _, X = polynomial_ring(ZZ, "X")
    for p in (2, 3)
      Q, = qadic_field(p, 2, precision = 1)
      for F in (padic_field(p, precision = 1), Q)
        # The derivative is nonzero, but truncation to its minimum coefficient
        # precision erases it. Detect this before computing its content.
        g = change_base_ring(F, X^p + 1)
        @test_throws ArgumentError gcd(g, derivative(g))
        g = change_base_ring(F, X^3 + 3*X - 2)
        @test_throws ArgumentError roots(g)
      end
    end

    Q, = qadic_field(2, 2, precision = 2)
    for F in (padic_field(2, precision = 2), Q)
      # At this precision a spurious common factor with the derivative would
      # otherwise cause squarefree factorization to report two extra roots.
      g = change_base_ring(F, X^3 + 3*X - 2)
      @test_throws ArgumentError roots(g)
    end

    Q, = qadic_field(3, 2, precision = 10)
    for F in (padic_field(3, precision = 10), Q)
      # Finite precision also cannot certify a genuinely repeated factor.
      @test_throws ArgumentError roots(change_base_ring(F, (X - 1)^2))
    end

    Q, = qadic_field(3, 2, precision = 2)
    # The constant coefficient loses all precision after the residue-class
    # substitution and content division. Report this before Hensel lifting.
    for f in (X^4 + 2*X - 3, X^4 + 11*X - 3)
      g = change_base_ring(Q, f)
      @test_throws ArgumentError roots(g)
    end

    Q, = qadic_field(3, 2, precision = 3)
    # The auxiliary characteristic polynomial in slope factorization loses
    # precision and cannot be reduced to the residue field.
    g = change_base_ring(Q, X^4 + 2*X - 3)
    @test_throws ArgumentError roots(g)

    Q, = qadic_field(3, 2, precision = 6)
    # With only one digit in the auxiliary characteristic polynomial, the
    # computed gcd is the whole cubic rather than a proper slope component.
    g = change_base_ring(Q, X^4 + 2*X - 3)
    @test_throws ArgumentError roots(g)

    P = padic_field(3, precision = 1)
    # The transformed polynomial has too little information to determine
    # the number of roots. Report this before attempting Hensel lifting.
    @test_throws ArgumentError Hecke._roots(change_base_ring(P, (X - 1)^2))
  end

  @testset "Root precision guards" begin
    _, X = polynomial_ring(ZZ, "X")
    # Reject incomplete slope factorizations, zero auxiliary polynomials,
    # and Newton polygons that cannot be determined at the available precision.
    cases = ((2, 4, (X - 1)*(X - 3)),
             (2, 4, X*(X - 1)*(X - 2)*(X - 4)),
             (3, 3, (X - 3)*(X - 6)*(X - 9)),
             (2, 3, (X - 1)*(X - 5)),
             (2, 3, X^4 + 6*X^3 + 10*X^2 - 8*X - 9))
    for (p, n, f) in cases
      Q, = qadic_field(p, 2, precision = n)
      for F in (padic_field(p, precision = n), Q)
        @test_throws ArgumentError roots(change_base_ring(F, f))
      end
    end

    # These examples formerly returned roots with nonzero residuals or exposed
    # an uninformative exact-division error in the quadratic extension.
    Q, = qadic_field(2, 2, precision = 2)
    f = X^3 - 7*X^2 + 6*X - 4
    @test_throws ArgumentError roots(change_base_ring(Q, f))
    @test_throws ArgumentError roots(change_base_ring(padic_field(2, precision = 2), f))

    Q, = qadic_field(2, 2, precision = 3)
    f = X*(X - 2)*(X^2 - 2)
    @test_throws ArgumentError roots(change_base_ring(Q, f))
    @test_throws ArgumentError roots(change_base_ring(padic_field(2, precision = 3), f))
    g = change_base_ring(Q, f)
    @test_throws ArgumentError divexact(g, gen(parent(g))^2)

    P = padic_field(2, precision = 4)
    L, a = eisenstein_extension(change_base_ring(P, X^2 - 2))
    # Both returned values used to approximate a, although -a is distinguishable
    # at their claimed precision. Zero residuals alone did not detect this.
    for f in (X^2 - 2, X*(X^2 - 2), (X - 1)*(X^2 - 2))
      @test_throws ArgumentError roots(change_base_ring(L, f))
    end

    for p in (3, 5)
      P = padic_field(p, precision = 2)
      L, = eisenstein_extension(change_base_ring(P, X^2 - p))
      for f in (X^2 - p, X*(X^2 - p), (X - 1)*(X^2 - p))
        @test_throws ArgumentError roots(change_base_ring(L, f))
      end
    end

    # Products with different slopes also lost precision in ramified fields:
    # the computed roots could overlap, fail evaluation, or reach a hull error.
    for (p, n, f) in ((2, 6, (X^2 - 2)*(X^2 - 8)),
                      (2, 8, (X^2 - 2)*(X^2 - 8)),
                      (2, 8, (X^2 - 2)*(X^2 - 4)),
                      (3, 8, (X^2 - 3)*(X^2 - 27)),
                      (5, 8, (X^2 - 5)*(X^2 - 125)))
      L, = eisenstein_extension(change_base_ring(padic_field(p, precision = n), X^2 - p))
      @test_throws ArgumentError roots(change_base_ring(L, f))
    end
  end

  @testset "Root examples across precisions" begin
    _, X = polynomial_ring(ZZ, "X")
    # Below the minimum precisions, the examples must throw. At higher
    # precisions they must return the complete set of roots.
    cases = ((2, X^3 + 3*X - 2, (1, 1), (3, 3)),
             (3, X^3 + 3*X - 1, (0, 0), (2, 2)),
             (3, X^3 + 3*X - 2, (0, 0), (2, 2)),
             (3, X^4 + 2*X - 3, (2, 2), (8, 8)),
             (3, X^3 + 3*X - 36, (1, 1), (5, 5)),
             (2, X^3 + 3*X, (1, 3), (3, 3)),
             (3, X^3 + 3*X, (1, 1), (3, 2)))
    for (p, f, counts, min_precisions) in cases, n in (1:12..., 20, 30)
      Q, = qadic_field(p, 2, precision = n)
      for (F, count, min_precision) in zip((padic_field(p, precision = n), Q), counts, min_precisions)
        g = change_base_ring(F, f)
        if n < min_precision
          @test_throws ArgumentError roots(g)
        else
          rt = @inferred roots(g)
          @test length(rt) == count
          @test allunique(rt)
          @test all(r -> precision(r) > 0 && iszero(g(r)), rt)
        end
      end
    end
  end

  @testset "Unsupported root inputs" begin
    _, X = polynomial_ring(ZZ, "X")
    Q, = qadic_field(3, 2, precision = 20)
    for F in (padic_field(3, precision = 20), Q)
      @test_throws ArgumentError roots(change_base_ring(F, 3*X - 1))
      @test_throws ArgumentError roots(change_base_ring(F, zero(parent(X))))
      # Removing scalar content still permits polynomials with integral roots.
      f = change_base_ring(F, 3*(X^2 - 1))
      rt = @inferred roots(f)
      @test length(rt) == 2
      @test all(iszero, map(f, rt))
    end
    Q, = qadic_field(2, 2, precision = 20)
    for F in (padic_field(2, precision = 20), Q)
      f = QQ(1//2)*change_base_ring(QQ, X*(X - 1))
      @test_throws ArgumentError roots(change_base_ring(F, f))
    end
  end

  # this is a test for roots(Q::QadicField, f::ZZPolyRingElem)
  @testset "Qadic Roots" begin
    X = polynomial_ring(ZZ, "X")[2]
    Q = qadic_field(3, 4, precision=2)[1]

    # currently only simple roots are supported
    # f' = 0
    @test isempty(@inferred roots(Q, X^3 - 1))
    # in residue field 2 is the root, and f'(2) = 0
    @test isempty(@inferred roots(Q, X^2 - 2*X + 1))

    # residue field is F_{3^4} thus -1 is a square and we have all four fourth roots
    # f'(x) = 4x^3 = x^3 [characteristic 3], clearly non-zero at roots, so we can lift all four
    rt = @inferred roots(Q, X^4-1)
    @test length(rt) == 4
    @test allunique(rt)
    @test all(iszero, map(X^4-1, rt))
  end

  # this is a test for newton_lift(f, r::QadicFieldElem, prec:, starting_prec)
  @testset "Newton lift (qadic)" begin
    Q = qadic_field(3, 4, precision=5)[1]
    X = polynomial_ring(ZZ, "X")[2]
    Y = polynomial_ring(Q, "Y")[2]

    R, QtoR = residue_field(Q)
    a = gen(R)

    # For X^4-1 we have 4 roots:
    # 1, -1, and a^3+a^2+1, -(a^3+a^2+1)
    f1 = X^4-1

    # lift a^3+a^2+1
    z = preimage(QtoR, a^3 + a^2 + 1)

    z_lift = @inferred newton_lift(f1, z)
    @test is_zero(f1(z_lift))
    @test z_lift in roots(Q, f1)

    # Now consider (we write with precision 2)
    # sqrt(3*a^2 + a + 1) = a^3 + (1 + 3^1)*a^2 + (1 + 2*3^1)*a + (2 + 2*3^1)
    # Thus, starting from residue field, we may lift a^3 + a^2 + a + 2 as a solution to Y^2 - (a+1)
    c = preimage(QtoR, a + 1)
    z = preimage(QtoR, a^3 + a^2 + a + 2)

    f2 = Y^2 - c
    z_lift = @inferred newton_lift(f2, z)
    @test is_zero(f2(z_lift))
  end

  @testset "Resultant" begin
    R, x = polynomial_ring(padic_field(853, precision = 2), "x")
    a = 4*x^5 + x^4 + 256*x^3 + 192*x^2 + 48*x + 4
    b = derivative(a)
    rab = @inferred resultant(a, b)
    @test rab == det(sylvester_matrix(a, b))
  end

  let # factor via number field
    Qpx, x = padic_field(19)[:x]
    @test length(Hecke._factor_via_number_field(x^2 - 2)) == 1
    @test length(Hecke._factor_via_number_field(x^2 - 5)) == 2
  end
end
