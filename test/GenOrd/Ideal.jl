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

  for (P, _) in L
    F, OtoF = residue_field(O, P)
    for i in 1:10
      a = dot([rand(base_ring(O), 1:5, 1:5) for i in 1:degree(O)], basis(O))
      b = dot([rand(base_ring(O), 1:5, 1:5) for i in 1:degree(O)], basis(O))
      @test OtoF(a) * OtoF(b) == OtoF(a * b)
      c = OtoF(a)
      @test OtoF(OtoF\c) == c
    end
  end

  k = GF(5)
  kt, t = rational_function_field(k, "t")
  ktx, x = kt["x"]
  F, a = function_field(x^5+x+3*t+1)
  OF = Hecke.finite_maximal_order(F)
  OI = Hecke.infinite_maximal_order(F)
  lp = prime_decomposition(OF, numerator(t-1))
  for (P, _) in lp
    K, OFtoK = residue_field(OF, P)
    for i in 1:10
      a = dot([rand(base_ring(OF), 1:5) for i in 1:degree(OF)], basis(OF))
      b = dot([rand(base_ring(OF), 1:5) for i in 1:degree(OF)], basis(OF))
      @test OFtoK(a) * OFtoK(b) == OFtoK(a * b)
      c = rand(K)
      @test OFtoK(OFtoK\c) == c
    end
  end
  lp = prime_decomposition(OI, base_ring(OI)(1//t))
  for (P, _) in lp
    K, OItoK = residue_field(OI, P)
    for i in 1:10
      a = OI(numerator(rand(kt, 1:5))(1//t))
      b = OI(numerator(rand(kt, 1:5))(1//t))
      @test OItoK(a) * OItoK(b) == OItoK(a * b)
      c = rand(K)
      @test OItoK(OItoK\c) == c
    end
  end
end

let
  # hashing of fractional ideals
  k = GF(7)
  kx, x = rational_function_field(k, "x")
  kt = parent(numerator(x))
  ky, y = polynomial_ring(kx, "y")
  F, a = function_field(y^2+x)
  O = integral_closure(kt, F)
  @test hash(fractional_ideal(a*O)) == hash(fractional_ideal(a*O))

  @test fractional_ideal(a * O) + fractional_ideal(a * O) == fractional_ideal(a * O)
end
