@testset "Poly" begin

  K = padic_field(2, precision = 100)
  Kx, x = polynomial_ring(K, "x")
  L, gL = eisenstein_extension(x^2+2, "a")

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

    # For X^4-1 we have 4 roots:
    # 1, -1, and a^3+a^2+1, -(a^3+a^2+1), where a is the generator of the residue field
    f1 = X^4-1

    # lift a^3+a^2+1
    # TODO: we have _qadic_from_residue_element in src/EllCrv/FinitePointCount.jl
    # TODO: we should move this to Nemo and use better api
    z = Q()
    setcoeff!(z, 3, ZZ(1))
    setcoeff!(z, 2, ZZ(1))
    setcoeff!(z, 0, ZZ(1))

    z_lift = @inferred newton_lift(f1, z)
    @test is_zero(f1(z_lift))
    @test z_lift in roots(Q, f1)

    # Now consider (we write with precision 2)
    # sqrt(3*a^2 + a + 1) = a^3 + (1 + 3^1)*a^2 + (1 + 2*3^1)*a + (2 + 2*3^1)
    # Thus, starting from residue field, we may lift a^3 + a^2 + a + 2 as a solution to Y^2 - (a+1)
    # As above, we write a for the generator of the residue field
    c = Q()
    setcoeff!(c, 1, ZZ(1))
    setcoeff!(c, 0, ZZ(1))

    z = Q()
    setcoeff!(z, 3, ZZ(1))
    setcoeff!(z, 2, ZZ(1))
    setcoeff!(z, 1, ZZ(1))
    setcoeff!(z, 0, ZZ(2))

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
end
