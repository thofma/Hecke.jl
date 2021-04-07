@testset "Poly" begin
  K = PadicField(2, 100)
  Kx, x = PolynomialRing(K, "x")
   
  @testset "Fun Factor" begin   
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
    u1, f1 = Hecke.fun_factor(g)
    @test u == u1
    @test f1 == f
  end
   
  @testset "Gcd" begin
    f = (2*x+1)*(x+1)
    g = x^3+1
    @test gcd(f, g) == x+1 
    
    f = (2*x+1)*(x+1)
    g = (2*x+1)*(x+2)
    @test gcd(f, g) == 2*x+1
     
    f = (x + 1//K(2)) * (2*x^2+x+1)
    g = 2*x+1
    @test gcd(f, g) == g
  end
   
  @testset "gcdx" begin
    f = (2*x+1)*(x+1)
    g = x^3+1
    d, u, v = gcdx(f, g)
    @test d == gcd(f, g)
    @test u*f + v*g == d
     
    f = (2*x+1)*(x+1)
    g = (2*x+1)*(x+2)
    d, u, v = gcdx(f, g)
    @test gcd(f, g) == d
    @test d == u*f + v*g
    
    f = (x + 1//K(2)) * (2*x^2+x+1)
    g = 2*x+1
    d, u, v = gcdx(f, g)
    @test g == d
    @test u*f + v*g == d
  end 
   
  @testset "Hensel" begin
    f = (x+1)^3 
    g = (x^2+x+1) 
    h = x^2 +2*x + 8
    ff = f*g*h
    lf = Hecke.Hensel_factorization(ff)
    @test prod(values(lf)) == ff
  end

  @testset "Slope Factorization" begin
    f = x^4 + 2*x^3 + 8*x^2+ 32*x + 256
    lf = Hecke.slope_factorization(f)
    @test prod(keys(lf)) == f
  end 

  @testset "Resultant" begin
    R, x = PolynomialRing(PadicField(853, 2), "x")
    a = 4*x^5 + x^4 + 256*x^3 + 192*x^2 + 48*x + 4
    b = derivative(a)
    @test resultant(a, b) == det(sylvester_matrix(a, b))
  end   
end
