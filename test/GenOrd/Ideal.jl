@testset "Ideals for orders over function fields" begin

  @testset "minimum" begin
    function check_ideal(I, expected_min)
      @test istril(basis_matrix(I))
      @test divides(norm(I), minimum(I))[1]
      @test expected_min == @inferred minimum(I)
    end

    function create_order_with_nontrivial_basis(Omax)
      kx = base_field(Omax.F)
      T = identity_matrix(kx, degree(Omax.F))
      T[1, 2] = one(kx)
      O = Hecke.GenOrd(Omax, T, one(kx))
      @assert !is_equation_order(O)
      @assert !isone(basis(O, copy = false)[1])
      return O
    end

    @testset "over F_2(x)" begin
      kx, x = rational_function_field(GF(2), :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)
      L, t = function_field(y^3 - x^3 - 1; cached = false)

      OL = finite_maximal_order(L)
      I = ideal(OL, x^3 + y^2)
      check_ideal(I, norm(OL(x^3 + y^2))) # x^3 + y^2 is irreducible

      I = ideal(OL, representation_matrix(OL(x^2 + 1)))
      check_ideal(I, x^2 + 1)
      @test I == ideal(OL, OL(x^2 + 1))

      I = ideal(OL, x*y, OL(x^2))
      check_ideal(I, x)

      OL = infinite_maximal_order(L)
      I = ideal(OL, 3//x^2)
      check_ideal(I, 1//x^2)

      Omax = finite_maximal_order(L)
      OL = create_order_with_nontrivial_basis(Omax)

      I = ideal(OL, OL(x^2 + x + 1))
      Imax = ideal(Omax, Omax(x^2 + x + 1))
      check_ideal(I, @inferred minimum(Imax))

      I = ideal(OL, x, OL(y + 1))
      Imax = ideal(Omax, x, Omax(y + 1))
      check_ideal(I, @inferred minimum(Imax))
    end

    @testset "Q(x) with non-monic defining polynomial" begin
      kx, x = rational_function_field(QQ, :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)
      L, t = function_field(1//2*y^3 - 1//3*x^3 - 1; cached = false)

      OL = finite_maximal_order(L)
      @assert !is_equation_order(OL)

      I = ideal(OL, x^3 + y^2)
      check_ideal(I, norm(OL(x^3 + y^2)))

      I = ideal(OL, x*y, OL(x^2))
      check_ideal(I, x)

      OL = infinite_maximal_order(L)
      I = ideal(OL, 3//x^2)
      check_ideal(I, 1//x^2)

      Omax = finite_maximal_order(L)
      OL = create_order_with_nontrivial_basis(Omax)

      I = ideal(OL, OL(x^2 + x + 1))
      Imax = ideal(Omax, Omax(x^2 + x + 1))
      check_ideal(I, @inferred minimum(Imax))

      I = ideal(OL, x^2*y + y, OL(y^2 + x*y))
      Imax = ideal(Omax, x^2*y + y, Omax(y^2 + x*y))
      check_ideal(I, @inferred minimum(Imax))
    end
  end

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

  @test (@inferred index(O)) == x^2 - 1//3*x
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
  @test hash(a*O) == hash(a*O)

  @test a * O + a * O == a * O
end
