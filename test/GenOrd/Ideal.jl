@testset "Ideals for orders over general PID" begin
  # Here we test basic ideal operations.
  # Function fields are the main use case for GenOrd.
  # We also add tests for other settings where GenOrd is not normally used,
  #   to make sure our implementation is robust enough to handle a general PID.

  # Builds a non-equation order whose first basis vector isn't 1,
  # to exercise corner cases.
  # The lattice itself is unchanged (unimodular change of basis),
  #   so norms and minima match those in Omax
  function create_order_with_nontrivial_basis(Omax)
    K = base_field(Omax.F)
    T = identity_matrix(K, degree(Omax.F))
    T[1, 2] = one(K)
    O = Hecke.GenOrd(Omax, T, one(K))
    @assert !is_equation_order(O)
    @assert !isone(basis(O, copy = false)[1])
    return O
  end

  @testset "norm" begin
    @testset "over F_2(x)" begin
      kx, x = rational_function_field(GF(2), :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)
      L, t = function_field(y^3 - x^3 - 1; cached = false)

      OL = finite_maximal_order(L)
      @test norm(ideal(OL, x^3 + y^2)) == norm(OL(x^3 + y^2))
      @test norm(ideal(OL, x*y, OL(x^2))) == x^3

      OL = create_order_with_nontrivial_basis(OL)
      @test norm(ideal(OL, x^3 + y^2)) == norm(OL(x^3 + y^2))
      @test norm(ideal(OL, x*y, OL(x^2))) == x^3

      OL = infinite_maximal_order(L)
      @test norm(ideal(OL, 1//x^2)) == 1//x^6
    end

    @testset "Q(x) with non-monic defining polynomial" begin
      kx, x = rational_function_field(QQ, :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)
      L, t = function_field(1//2*y^3 - 1//3*x^3 - 1; cached = false)

      OL = finite_maximal_order(L)
      @assert !is_equation_order(OL)

      @test norm(ideal(OL, x^3 + y^2)) == norm(OL(x^3 + y^2))
      @test norm(ideal(OL, x*y, OL(x^2))) == x^3

      OL = create_order_with_nontrivial_basis(OL)
      @test norm(ideal(OL, x^3 + y^2)) == norm(OL(x^3 + y^2))
      @test norm(ideal(OL, x*y, OL(x^2))) == x^3

      OL = infinite_maximal_order(L)
      @test norm(ideal(OL, 3//x^2)) == 27//x^6
    end

    @testset "number field" begin
      x = gen(Hecke.Globals.Qx)
      K, a = number_field(x^2 - 2, :a)
      OK = Hecke.GenOrd(ZZ, K)

      @test norm(ideal(OK, ZZ(3))) == 9
      @test norm(ideal(OK, ZZ(2), OK(a))) == 2
      @test norm(ideal(OK, ZZ(2))) == 4

      OK = create_order_with_nontrivial_basis(OK)
      @test norm(ideal(OK, ZZ(3))) == 9
      @test norm(ideal(OK, ZZ(2), OK(a))) == 2
      @test norm(ideal(OK, ZZ(2))) == 4

      K, a = number_field(2*x^2 - 4, :a)
      OK = Hecke.GenOrd(ZZ, K)

      @test norm(ideal(OK, ZZ(3))) == 9
      @test norm(ideal(OK, ZZ(2), OK(2*a))) == 2
      @test norm(ideal(OK, ZZ(2))) == 4
    end
  end

  @testset "minimum" begin
    function check_ideal(I, expected_min)
      @test istril(basis_matrix(I))
      @test divides(norm(I), minimum(I))[1]
      @test expected_min == @inferred minimum(I)
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

      I = ideal(OL, L(x^2)//t^3)
      check_ideal(I, 1//x)

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

    @testset "number field" begin
      x = gen(Hecke.Globals.Qx)
      K, a = number_field(x^2 - 2, :a)
      OK = Hecke.GenOrd(ZZ, K)

      check_ideal(ideal(OK, ZZ(3)), 3)
      check_ideal(ideal(OK, ZZ(2), OK(a)), 2)
      check_ideal(ideal(OK, ZZ(2)), 2)

      OK = create_order_with_nontrivial_basis(OK)
      check_ideal(ideal(OK, ZZ(3)), 3)
      check_ideal(ideal(OK, ZZ(2), OK(a)), 2)
      check_ideal(ideal(OK, ZZ(2)), 2)

      K, a = number_field(2*x^2 - 4, :a)
      OK = Hecke.GenOrd(ZZ, K)
      check_ideal(ideal(OK, ZZ(3)), 3)
      check_ideal(ideal(OK, ZZ(2), OK(2*a)), 2)
      check_ideal(ideal(OK, ZZ(2)), 2)
    end
  end

  @testset "prime decomposition" begin
    function _test_prime_2elem(P, f, e)
      @test inertia_degree(P) == f
      @test ramification_index(P) == e
      @test Hecke.has_2_elem(P)
      @test 1 == @inferred valuation(ideal(order(P), P.gen_two), P)
    end

    @testset "over F_2(x)" begin
      kx, x = rational_function_field(GF(2), :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)
      L, t = function_field(y^3 - x - 1; cached = false)
      Ofin = finite_maximal_order(L)
      Oinf = infinite_maximal_order(L)

      pd = prime_decomposition(Ofin, Ofin.R(x^2 + x + 1))
      @test length(pd) == 1
      P, e = first(pd)
      @test e == 1
      _test_prime_2elem(P, 3, 1)

      pd = prime_decomposition(Ofin, Ofin.R(x + 1))
      @test length(pd) == 1
      P, e = first(pd)
      @test e == 3
      _test_prime_2elem(P, 1, 3)

      # modulo x: y^3 - x - 1 = (y+1)(y^2+y+1)
      pd = prime_decomposition(Ofin, Ofin.R(x))
      @test length(pd) == 2
      for (P, e) in pd
        @test e == 1
        f_expected = degree(numerator(data(P.gen_two)))
        _test_prime_2elem(P, f_expected, 1)
      end

      pd = prime_decomposition(Oinf, Oinf.R(1//x))
      @test length(pd) == 1
      P, e = first(pd)
      @test e == 3
      @test inertia_degree(P) == 1
    end
  end
end

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
