@testset "Poly" begin

  K = PadicField(2, 100)
  Kx, x = polynomial_ring(K, "x")
  L, gL = eisenstein_extension(x^2+2, "a")

  @testset "Fun Factor" for F in [K, L]
    Fx, x = polynomial_ring(F, "x")
    f = x^5
    for i = 0:4
      c = K(rand(FlintZZ, 1:100))
      f += c*x^i
    end
    u = 1
    for i = 1:5
      c = K(rand(FlintZZ, 1:100))
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
    _, t = PadicField(3, 10)["t"]
    f = ((t-1+81)*(t-1+2*81))
    rt = roots(f)
    @test length(rt) == 2
    @test rt[1] != rt[2]
    @test all(iszero, map(f, rt))
  end

  @testset "Resultant" begin
    R, x = polynomial_ring(PadicField(853, 2), "x")
    a = 4*x^5 + x^4 + 256*x^3 + 192*x^2 + 48*x + 4
    b = derivative(a)
    rab = @inferred resultant(a, b)
    @test rab == det(sylvester_matrix(a, b))
  end
end
