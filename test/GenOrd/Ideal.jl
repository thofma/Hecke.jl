@testset "Ideals for orders over function fields" begin

  k = GF(7)
  kx, x = rational_function_field(k, "x")
  kt = parent(numerator(x))
  ky, y = polynomial_ring(kx, "y")
  F, a = function_field(y^2+x)
  O = integral_closure(kt, F)

  h = O.R(x^2+1)

  f1 = y+5*x+2
  f2 = y+2*x+5

  I = ideal(O, h, O(y+5*x+2))
  J = ideal(O, h, O(y+2*x+5))
  K2 = ideal(O, h)
  @test K2 == I*J

  A = I^3*J
  L = @inferred factor(A)
  G = [(fac,e) for (fac,e) in L]
  @test (I,3) in G
  @test (J,1) in G
  @test length(G)==2


  k = QQ
  kx, x = rational_function_field(k, "x")
  kt = parent(numerator(x))
  ky, y = polynomial_ring(kx, "y")
  F, a = function_field(y^2+x*y+x^3+y^3)
  O = integral_closure(kt, F)

  @test @inferred index(O) == x^2 - 1//3*x
  h = O.R(x)
  L = prime_decomposition(O, h)
  @test prod([f[1]^f[2] for f in L]) == Hecke.GenOrdIdl(O, h)
end
