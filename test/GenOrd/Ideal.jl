@testset "Ideals for orders over general PID" begin
  # Here we test basic ideal operations.
  # Function fields are the main use case for GenOrd.
  # We also add tests for other settings where GenOrd is not normally used,
  #   to make sure our implementation is robust enough to handle a general PID.

  # Builds a non-equation order whose first basis vector isn't 1, to exercise corner cases.
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

  function check_ideal_norm_min(I, expected_norm, expected_min)
    @test istril(basis_matrix(I))
    @test divides(norm(I), minimum(I))[1]
    @test expected_norm == @inferred norm(I)
    @test expected_min == @inferred minimum(I)
  end

  function check_prime_2elem(P, expected_f, expected_e)
    @test inertia_degree(P) == expected_f
    @test ramification_index(P) == expected_e
    @test Hecke.has_2_elem(P)
    @test 1 == @inferred valuation(ideal(order(P), P.gen_two), P)
  end

  function check_prime_2elem_single_above(O, a, expected_f, expected_e)
    pd = @inferred prime_decomposition(O, base_ring(O)(a))
    @test length(pd) == 1
    P, e = first(pd)
    @test e == expected_e
    check_prime_2elem(P, expected_f, expected_e)
  end

  @testset "over F_2(x)" begin
    kx, x = rational_function_field(GF(2), :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    L, t = function_field(y^3 - x^3 - 1; cached = false)
    Ofin = finite_maximal_order(L)
    Oinf = infinite_maximal_order(L)

    @testset "norm/min: finite maximal order" begin
      I = ideal(Ofin, representation_matrix(Ofin(x^2 + 1)))
      @test I == ideal(Ofin, Ofin(x^2 + 1))

      a = Ofin(x^3 + y^2)
      I = ideal(Ofin, a)
      check_ideal_norm_min(I, norm(a), norm(a)) # x^3 + y^2 is irreducible

      I = ideal(Ofin, x*y, Ofin(x^2))
      check_ideal_norm_min(I, x^3, x)
    end

    @testset "norm/min: finite non-equation order" begin
      OL = create_order_with_nontrivial_basis(Ofin)
      @assert !is_equation_order(OL)
      a = OL(x^3 + y^2)
      I = ideal(OL, a)
      check_ideal_norm_min(I, norm(a), norm(a)) # x^3 + y^2 is irreducible

      I = ideal(OL, x*y, OL(x^2))
      check_ideal_norm_min(I, x^3, x)

      I = ideal(OL, OL(x^2 + x + 1))
      Imax = ideal(Ofin, Ofin(x^2 + x + 1))
      check_ideal_norm_min(I, @inferred(norm(Imax)), @inferred(minimum(Imax)))

      I = ideal(OL, x, OL(y + 1))
      Imax = ideal(Ofin, x, Ofin(y + 1))
      check_ideal_norm_min(I, @inferred(norm(Imax)), @inferred(minimum(Imax)))
    end

    @testset "norm/min: infinite maximal order" begin
      I = ideal(Oinf, 3//x^2)
      check_ideal_norm_min(I, 1//x^6, 1//x^2)

      I = ideal(Oinf, L(x^2)//t^3)
      check_ideal_norm_min(I, norm(Oinf(L(x^2)//t^3)), 1//x)
    end

    @testset "prime decomposition" begin
      check_prime_2elem_single_above(Ofin, x + 1, 1, 3)
      check_prime_2elem_single_above(Ofin, x^2 + x + 1, 1, 3)
      check_prime_2elem_single_above(Ofin, x^4 + x + 1, 3, 1)

      # modulo x: y^3 - x^3 - 1 = (y+1)(y^2+y+1)
      pd = @inferred prime_decomposition(Ofin, Ofin.R(x))
      @test length(pd) == 2
      for (P, e) in pd
        @test e == 1
        f_expected = degree(numerator(data(P.gen_two)))
        check_prime_2elem(P, f_expected, 1)
      end

      pd = @inferred prime_decomposition(Oinf, Oinf.R(1//x))
      @test length(pd) == 2
      for (P, e) in pd
        @test e == 1
        f_expected = (norm(P) == 1//x ? 1 : 2)
        @test inertia_degree(P) == f_expected
      end

      let (L, t) = function_field(y^3 - x - 1; cached = false)
        Ofin = finite_maximal_order(L)
        Oinf = infinite_maximal_order(L)

        check_prime_2elem_single_above(Ofin, x + 1, 1, 3)
        check_prime_2elem_single_above(Ofin, x^2 + x + 1, 3, 1)

        # modulo x: y^3 - x - 1 = (y+1)(y^2+y+1)
        pd = @inferred prime_decomposition(Ofin, Ofin.R(x))
        @test length(pd) == 2
        for (P, e) in pd
          @test e == 1
          f_expected = degree(numerator(data(P.gen_two)))
          check_prime_2elem(P, f_expected, 1)
        end

        pd = @inferred prime_decomposition(Ofin, Ofin.R(x^4 + x^3 + 1))
        @test length(pd) == 3
        for (P, e) in pd
          @test e == 1
          check_prime_2elem(P, 1, 1)
        end

        pd = @inferred prime_decomposition(Oinf, Oinf.R(1//x))
        @test length(pd) == 1
        P, e = first(pd)
        @test e == 3
        @test inertia_degree(P) == 1
      end
    end
  end

  @testset "over Q(x) with non-monic defining polynomial" begin
    kx, x = rational_function_field(QQ, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    L, t = function_field(1//2*y^3 - 1//3*x^3 - 1; cached = false)

    Ofin = finite_maximal_order(L)
    Oinf = infinite_maximal_order(L)
    @assert !is_equation_order(Ofin)

    @testset "norm/min: finite maximal order" begin
      a = Ofin(x^3 + y^2)
      I = ideal(Ofin, a)
      check_ideal_norm_min(I, norm(a), norm(a)) # x^3 + y^2 is irreducible

      I = ideal(Ofin, x*y, Ofin(x^2))
      check_ideal_norm_min(I, x^3, x)
    end

    @testset "norm/min: infinite maximal order" begin
      I = ideal(Oinf, 3//x^2)
      check_ideal_norm_min(I, 27//x^6, 1//x^2)

      I = ideal(Oinf, L(x^2)//t^3)
      check_ideal_norm_min(I, norm(Oinf(L(x^2)//t^3)), 1//x)
    end
  end

  @testset "over number field" begin
    x = gen(Hecke.Globals.Qx)
    K, a = number_field(x^2 - 2, :a)
    OK = Hecke.GenOrd(ZZ, K)

    @testset "norm/min: maximal order" begin
      check_ideal_norm_min(ideal(OK, ZZ(3)), 9, 3)
      check_ideal_norm_min(ideal(OK, ZZ(2), OK(a)), 2, 2)
      check_ideal_norm_min(ideal(OK, ZZ(2)), 4, 2)
    end

    @testset "norm/min: non-equation order" begin
      let OK = create_order_with_nontrivial_basis(OK)
        @assert !is_equation_order(OK)
        check_ideal_norm_min(ideal(OK, ZZ(3)), 9, 3)
        check_ideal_norm_min(ideal(OK, ZZ(2), OK(a)), 2, 2)
        check_ideal_norm_min(ideal(OK, ZZ(2)), 4, 2)
      end
    end

    @testset "norm/min: with non-monic defining polynomial" begin
      let (K, a) = number_field(2*x^2 - 4, :a), OK = Hecke.GenOrd(ZZ, K)
        @assert !is_equation_order(OK)
        check_ideal_norm_min(ideal(OK, ZZ(3)), 9, 3)
        check_ideal_norm_min(ideal(OK, ZZ(2), OK(2*a)), 2, 2)
        check_ideal_norm_min(ideal(OK, ZZ(2)), 4, 2)
      end
    end

    @testset "prime decomposition" begin
      check_prime_2elem_single_above(OK, ZZ(3), 2, 1)
      check_prime_2elem_single_above(OK, ZZ(2), 1, 2)

      pd = @inferred prime_decomposition(OK, ZZ(7))
      @test length(pd) == 2
      for (P, e) in pd
        @test e == 1
        check_prime_2elem(P, 1, 1)
      end

      # Currently GenOrd's prime decomposition does not work with
      #   number fields defined by non-monic polynomials,
      #   since the Lenstra order is a sub-order of the equation order.
    end
  end

  @testset "over number field localized at prime" begin
    x = gen(Hecke.Globals.Qx)
    K, a = number_field(x^2 - 2, :a)

    @testset "split (p = 7)" begin
      R = Hecke.localization(ZZ, 7)
      OK = integral_closure(R, K)

      check_ideal_norm_min(ideal(OK, R(7)),             R(49), R(7))
      check_ideal_norm_min(ideal(OK, R(7), OK(a - 3)),  R(7),  R(7))

      pd = @inferred prime_decomposition(OK, R(7))
      @test length(pd) == 2
      for (P, e) in pd
        @test e == 1
        check_prime_2elem(P, 1, 1)
      end
    end

    @testset "inert (p = 3)" begin
      R = Hecke.localization(ZZ, 3)
      OK = integral_closure(R, K)

      check_ideal_norm_min(ideal(OK, R(3)), R(9), R(3))
      check_prime_2elem_single_above(OK, R(3), 2, 1)
    end

    @testset "ramified (p = 2)" begin
      R = Hecke.localization(ZZ, 2)
      OK = integral_closure(R, K)

      check_ideal_norm_min(ideal(OK, R(2)),          R(4), R(2))
      check_ideal_norm_min(ideal(OK, R(2), OK(a)),   R(2), R(2))

      check_prime_2elem_single_above(OK, R(2), 1, 2)
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
