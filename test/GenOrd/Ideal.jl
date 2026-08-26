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
    @test AbstractAlgebra.is_lower_triangular(basis_matrix(I))
    @test divides(norm(I), minimum(I))[1]
    @test @inferred(norm(I)) == Hecke._make_canonical_in(order(I), expected_norm)
    @test @inferred(minimum(I)) == Hecke._make_canonical_in(order(I), expected_min)
  end

  function check_prime_2elem(P, expected_f, expected_e)
    @test inertia_degree(P) == expected_f
    @test ramification_index(P) == expected_e
    @test Hecke.has_2_elem(P)
    @test Hecke.has_2_elem_normal(P)
    @test 1 == @inferred valuation(ideal(order(P), P.gen_two), P)
  end

  function check_prime_2elem_single_above(O, a, expected_f, expected_e)
    pd = @inferred prime_decomposition(O, base_ring(O)(a))
    @test length(pd) == 1
    P, e = first(pd)
    @test e == expected_e
    check_prime_2elem(P, expected_f, expected_e)
  end

  function test_containment_common(O, a, t)
    L = Hecke.field(O)

    a = O(a)
    I = ideal(O, a)
    Ifrac = fractional_ideal(I)

    for v in (a, a * O(t), O(0))
      @test v in I
      @test v in Ifrac
    end
    for v in (O(1), O(t))
      @test !(v in I)
      @test !(v in Ifrac)
    end

    Iinv = inv(I)
    for v in (zero(L), one(L), L(a), L(1)//L(a))
      @test v in Iinv
    end
    @test a in Iinv

    @test !(L(1)//L(a)^2 in Iinv)

    # In a local ring O.R, units are everything coprime to the prime, so this test doesnt make sense
    # Similar in KInftyRing: this is localization
    if !isa(O.R, LocalizedEuclideanRing) && !isa(O.R, KInftyRing)
      @test !(L(1)//L(t) in Iinv)
    end
  end

  function test_colon_common_ideal(O, I)
    L = Hecke.field(O)
    U = ideal(O, one(O))
    @test Hecke.colon(I, U) == fractional_ideal(I)
    @test one(L) in Hecke.colon(I, I)
    @test Hecke.colon(U, I) * I == U

    I = fractional_ideal(I)
    U = fractional_ideal(U)
    @test Hecke.colon(I, U) == I
    @test Hecke.colon(U, I) * I == U
  end

  function test_ideal_inv(O, I)
    U = ideal(O, one(O))
    @test inv(I) == colon(U, I)     # agrees with colon
    @test is_one(I * inv(I))        # defining property: A * A^{-1} = O
    @test inv(inv(I)) == I
  end

  function test_frac_ideal_inv(O, I_list)
    for I in I_list
      test_ideal_inv(O, I)
    end
  end

  function test_ideal_inv_2elem_normal(O, p_list)
    I = ideal(O, one(O))

    for p in p_list
      P = prime_decomposition(O, p)[1][1]
      @test Hecke.has_2_elem_normal(P)
      test_ideal_inv(O, P)

      Pe = P^3
      @test Hecke.has_2_elem_normal(Pe)
      test_ideal_inv(O, Pe)

      I = I*Pe
      @test Hecke.has_2_elem_normal(I)
      test_ideal_inv(O, I)
    end
  end

  test_colon_common(O, p) = test_colon_common_ideal(O, ideal(O, O(p)))

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
        check_prime_2elem(P, f_expected, 1)
      end

      let (L, t) = function_field(y^3 - x - 1; cached = false),
          Ofin = finite_maximal_order(L),
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

        check_prime_2elem_single_above(Oinf, 1//x, 1, 3)
      end
    end

    @testset "containment" begin
      test_containment_common(Ofin, x^4 + x + 1, t)
      test_containment_common(Oinf, 1//(x^4 + x + 1), 1//t)
    end

    @testset "colon" begin
      test_colon_common(Ofin, x^4 + x + 1)
      test_colon_common(Ofin, t + x^4)
      test_colon_common_ideal(Ofin, ideal(Ofin, [Ofin(t), Ofin(x+1)]) * ideal(Ofin, Ofin(t + x^2)))
      test_colon_common(Oinf, 1//(t + x^4))
    end

    @testset "ideal inv" begin
      O = Ofin
      test_frac_ideal_inv(O, (t*O, (t + 1)*O, (1//x)*(t*O), (x//(x + 1))*(t*O)))
      test_ideal_inv_2elem_normal(O, (numerator(x+1), numerator(x^2+x+1), numerator(x^3+x+1)))
      O = Oinf
      test_frac_ideal_inv(O, (t*O, (t + 1)*O, (1//x)*(t*O), (x//(x + 1))*(t*O)))
      test_ideal_inv_2elem_normal(O, (O.R(1//x), O.R(1//(x+1))))
    end
  end

  @testset "over Q(x) with non-monic defining polynomial" begin
    kx, x = rational_function_field(QQ, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    L, t = function_field(x^3 + x^2 + x*y^3 - x*y^2 + y^2 - y; cached = false)

    Ofin = finite_maximal_order(L)
    Oinf = infinite_maximal_order(L)

    @testset "norm/min" begin
      I = ideal(Ofin, x*t)
      check_ideal_norm_min(I, x^5 + x^4, x^4 + x^3)

      I = ideal(Oinf, 3//(x^2*t^2))
      check_ideal_norm_min(I, 1//x^10, 1//x^4)
    end

    @testset "prime decomposition" begin
      # <x + 1> = <x + 1, x*y> * <x + 1, x*y + 1>^2
      pd = @inferred prime_decomposition(Ofin, Ofin.R(x + 1))
      @test length(pd) == 2
      for (P, e) in pd
        if e == 1
          check_prime_2elem(P, 1, 1)
        else
          check_prime_2elem(P, 1, 2)
        end
      end

      # x^2 + 2 is inert
      check_prime_2elem_single_above(Ofin, x^2 + 2, 3, 1)
    end

    @testset "containment" begin
      test_containment_common(Ofin, x^2 + x*t + 1, x*t)
      test_containment_common(Oinf, 1//(x^2 + x*t + 1), 1//(x*t))
    end

    @testset "colon" begin
      test_colon_common(Ofin, x^2 + 2)
      test_colon_common(Ofin, t*x + x^2)
      test_colon_common_ideal(Ofin, ideal(Ofin, [Ofin(t*x), Ofin(x+1)]) * ideal(Ofin, Ofin(x^2+2)))
      test_colon_common(Oinf, 1//(t*x + x^2))
    end

    @testset "ideal inv" begin
      O = Ofin
      test_frac_ideal_inv(O, (t*O, (t + 1)*O, (1//x)*(t*O), (x//(x + 1))*(t*O)))
      test_ideal_inv_2elem_normal(O, (numerator(x+1), numerator(x^2+x+1), numerator(x^3+x+1)))
      O = Oinf
      test_frac_ideal_inv(O, (t*O, (t + 1)*O, (1//x)*(t*O), (x//(x + 1))*(t*O)))
      test_ideal_inv_2elem_normal(O, (O.R(1//x), O.R(1//(x+3)), O.R(1//(2*x+25))))
    end
  end

  @testset "over Q(x)" begin
    kx, x = rational_function_field(QQ, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    L, t = function_field(y^2 - x^3 - x^2; cached = false)

    Ofin = finite_maximal_order(L)
    Oinf = infinite_maximal_order(L)

    @testset "norm/min: finite maximal order" begin
      I = ideal(Ofin, L(y)//L(x))
      check_ideal_norm_min(I, x + 1, x + 1)
      @test is_prime(I)
    end

    @testset "containment" begin
      test_containment_common(Ofin, x^2 + 1, t)
      test_containment_common(Oinf, 1//(x^2 + 1), 1//t)
    end

    @testset "colon" begin
      test_colon_common(Ofin, x^2 + 1)
      test_colon_common(Ofin, t*x + x^2)
      test_colon_common_ideal(Ofin, ideal(Ofin, [Ofin(t), Ofin(x+1)]) * ideal(Ofin, Ofin(x^2+2)))
      test_colon_common(Oinf, 1//(t*x + x^2))
    end

    @testset "ideal inv" begin
      O = Ofin
      test_frac_ideal_inv(O, (t*O, (t + 1)*O, (1//x)*(t*O), (x//(x + 1))*(t*O)))
      test_ideal_inv_2elem_normal(O, (numerator(x+1), numerator(x^2+x+1), numerator(x^3+x+1)))
      O = Oinf
      test_frac_ideal_inv(O, (t*O, (t + 1)*O, (1//x)*(t*O), (x//(x + 1))*(t*O)))
      test_ideal_inv_2elem_normal(O, (O.R(1//x), O.R(1//(x+3)), O.R(1//(2*x+25))))
    end
  end

  @testset "over number field" begin
    x = gen(Hecke.Globals.Qx)
    K, a = number_field(x^2 - 2, :a)
    # NOTE: Hecke.integral_closure(ZZ,K) will go through number fields
    # NOTE: Hecke.GenOrd(ZZ, K) will not set maximal order flag
    OK = Hecke._integral_closure(ZZ, K)

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
      check_prime_2elem_single_above(OK, 3, 2, 1)
      check_prime_2elem_single_above(OK, 2, 1, 2)

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

    @testset "containment" begin
      test_containment_common(OK, ZZ(3), ZZ(5))
    end

    @testset "colon" begin
      test_colon_common(OK, 3)
      test_colon_common(OK, 15)
      test_colon_common_ideal(OK, ideal(OK, [OK(a*2), OK(4)]) * ideal(OK, 15))
    end

    @testset "ideal inv" begin
      test_frac_ideal_inv(OK, (a*OK, (a + 1)*OK, ((a//ZZ(3))*OK)))
      test_ideal_inv_2elem_normal(OK, (ZZ(2), ZZ(3), ZZ(5), ZZ(7)))
    end
  end

  @testset "over number field localized at prime" begin
    x = gen(Hecke.Globals.Qx)
    K, a = number_field(x^2 - 2, :a)

    @testset "split (p = 7)" begin
      R = Hecke.localization(ZZ, 7; cached = false)
      OK = integral_closure(R, K)

      check_ideal_norm_min(ideal(OK, R(7)),             R(49), R(7))
      check_ideal_norm_min(ideal(OK, R(7), OK(a - 3)),  R(7),  R(7))

      pd = @inferred prime_decomposition(OK, R(7))
      @test length(pd) == 2
      for (P, e) in pd
        @test e == 1
        check_prime_2elem(P, 1, 1)
      end

      test_containment_common(OK, R(7), R(5))
      test_colon_common_ideal(OK, ideal(OK, R(7), OK(a - 3)))
      test_frac_ideal_inv(OK, (a*OK, (a + 1)*OK, (a//49)*OK))
    end

    @testset "inert (p = 3)" begin
      R = Hecke.localization(ZZ, 3; cached = false)
      OK = integral_closure(R, K)

      check_ideal_norm_min(ideal(OK, R(3)), R(9), R(3))
      check_prime_2elem_single_above(OK, R(3), 2, 1)

      test_containment_common(OK, R(3), R(5))
      test_colon_common(OK, R(3))
      test_frac_ideal_inv(OK, (a*OK, (a + 1)*OK, (a//3)*OK))
    end

    @testset "ramified (p = 2)" begin
      R = Hecke.localization(ZZ, 2; cached = false)
      OK = integral_closure(R, K)

      check_ideal_norm_min(ideal(OK, R(2)),          R(4), R(2))
      check_ideal_norm_min(ideal(OK, R(2), OK(a)),   R(2), R(2))

      check_prime_2elem_single_above(OK, R(2), 1, 2)

      test_containment_common(OK, R(2), R(5))
      test_colon_common_ideal(OK, ideal(OK, R(2), OK(a)))
      test_frac_ideal_inv(OK, (a*OK, (a + 1)*OK, (a//16)*OK))
    end
  end

  # We have plenty of tests for usual prime decomposition above
  # In here we test "hard" cases:
  # - Kummer-Dedekind with only locally nice generator
  # - index divisor (or not-nice polynomial) finding normal two generators form
  @testset "Prime Decomposition" begin
    @testset "over F_7(x) with non-integral defining polynomial" begin
      kx, x = rational_function_field(GF(7), :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)
      L, t = function_field(y^2 - (x + 1)//x; cached = false)
      Ofin = finite_maximal_order(L)
      Oinf = infinite_maximal_order(L)

      @test !(t in Ofin) # t has a pole at x = 0, so it is not integral there

      Rfin = base_ring(Ofin)
      pd = @inferred prime_decomposition(Ofin, Rfin(x - 1))
      @test length(pd) == 2
      for (P, e) in pd
        @test e == 1
        check_prime_2elem(P, 1, 1)
        @test P.gen_two in Ofin
      end
      @test prod(P^e for (P, e) in pd) == ideal(Ofin, Rfin(x - 1))

      check_prime_2elem_single_above(Ofin, x, 1, 2)

      @testset "non-maximal sub-order: index divisor at det denominator" begin
        # Sub-order with basis [1, w], w = x^2*(x-1)*t. It is closed under
        #   multiplication since w^2 = x^3*(x-1)^2*(x+1) in Rfin, hence an order.
        # It is non-maximal at x-1 (and x): det(basis_matrix_inverse(O))
        #   = 1//(x^2*(x-1)), so both x and x-1 divide the *denominator* of the index,
        #   not the numerator.
        w = x^2*(x - 1)*t
        M = matrix(kx, 2, 2, vcat(coordinates(one(L), Ofin), coordinates(w, Ofin)))
        O = Hecke.GenOrd(Ofin, M, one(kx))
        @assert !is_equation_order(O)

        # O is non-maximal at p, so p IS an index divisor.
        for p in (Rfin(x - 1), Rfin(x))
          @test is_index_divisor(O, p)
          pd = @inferred prime_decomposition(O, p)
          @test !isempty(pd)
          for (P, _) in pd
            @test is_prime(P)
            @test O(p) in P
          end
        end
      end
    end

    @testset "over F_7(x) with 1/x not index divisor: split" begin
      kx, x = rational_function_field(GF(7), :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)
      L, t = function_field(y^2 - (x + 1)//x; cached = false)

      Oinf = infinite_maximal_order(L)
      p = base_ring(Oinf)(1//x)

      @test Hecke._is_defining_polynomial_nice_at(Oinf, p)
      @test !is_index_divisor(Oinf, p)

      pd = @inferred prime_decomposition(Oinf, p)
      @test prod(P^e for (P, e) in pd) == ideal(Oinf, p)

      @test length(pd) == 2
      for (P, e) in pd
        @test e == 1
        check_prime_2elem(P, 1, 1)
      end

      Ofin = finite_maximal_order(L)
      p = base_ring(Ofin)(x)
      @test !Hecke._is_defining_polynomial_nice_at(Ofin, p)
      @test is_index_divisor(Ofin, p)
      check_prime_2elem_single_above(Ofin, x, 1, 2)
    end

    @testset "over F_7(x) with 1/x not index divisor: inert" begin
      kx, x = rational_function_field(GF(7), :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)
      L, t = function_field(y^2 - (3*x + 1)//x; cached = false)

      Oinf = infinite_maximal_order(L)
      p = base_ring(Oinf)(1//x)

      @test Hecke._is_defining_polynomial_nice_at(Oinf, p)
      @test !is_index_divisor(Oinf, p)

      pd = @inferred prime_decomposition(Oinf, p)
      @test prod(P^e for (P, e) in pd) == ideal(Oinf, p)
      check_prime_2elem_single_above(Oinf, p, 2, 1)

      Ofin = finite_maximal_order(L)
      p = base_ring(Ofin)(x)
      @test !Hecke._is_defining_polynomial_nice_at(Ofin, p)
      @test is_index_divisor(Ofin, p)
      check_prime_2elem_single_above(Ofin, x, 1, 2)
    end

    @testset "over F_7(x) with 1/x not index divisor: ramified" begin
      kx, x = rational_function_field(GF(7), :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)
      L, t = function_field(y^2 - 1//x; cached = false)

      Oinf = infinite_maximal_order(L)
      p = base_ring(Oinf)(1//x)

      @test Hecke._is_defining_polynomial_nice_at(Oinf, p)
      @test !is_index_divisor(Oinf, p)

      pd = @inferred prime_decomposition(Oinf, p)
      @test prod(P^e for (P, e) in pd) == ideal(Oinf, p)
      check_prime_2elem_single_above(Oinf, p, 1, 2)

      Ofin = finite_maximal_order(L)
      p = base_ring(Ofin)(x)
      @test !Hecke._is_defining_polynomial_nice_at(Ofin, p)
      @test is_index_divisor(Ofin, p)
      check_prime_2elem_single_above(Ofin, x, 1, 2)
    end

    @testset "over number with non-integral defining polynomial" begin
      x = gen(Hecke.Globals.Qx)
      K, a = number_field(x^2 - 1//2, :a)
      O = Hecke.maximal_order(Hecke.GenOrd(ZZ, K))
      check_prime_2elem_single_above(O, 3, 2, 1)
      check_prime_2elem_single_above(O, 5, 2, 1)

      pd = @inferred prime_decomposition(O, ZZ(2))
      check_prime_2elem_single_above(O, 2, 1, 2)

      pd = @inferred prime_decomposition(O, ZZ(7))
      @test length(pd) == 2
      for (P, e) in pd
        @test e == 1
        check_prime_2elem(P, 1, 1)
      end
    end

    @testset "common index divisor (Dedekind's cubic)" begin
      # x^3 - x^2 - 2x - 8: the generator is nice, yet 2 divides the index of
      #   every element (essential index divisor) and splits P1*P2*P3
      x = gen(Hecke.Globals.Qx)
      K, a = number_field(x^3 - x^2 - 2*x - 8, :a)
      O = Hecke.maximal_order(Hecke.GenOrd(ZZ, K))
      @test is_index_divisor(O, ZZ(2))

      pd = @inferred prime_decomposition(O, ZZ(2))
      @test length(pd) == 3
      for (P, e) in pd
        check_prime_2elem(P, 1, 1)
      end
      @test prod(P^e for (P, e) in pd) == ideal(O, ZZ(2))
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
  @test prod([f[1]^f[2] for f in L]) == ideal(O, h)

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

let # 2266
  K = algebraic_closure(QQ)
  Kx, x = rational_function_field(K,"x")
  KxY, Y = polynomial_ring(Kx, "Y")
  P = Y^2 - x^3 - x^2
  kC, y = function_field(P, "y")
  OC = finite_maximal_order(kC)
  I = ideal(OC(x),OC(y))
  lp = factor(I)
  @test all(is_prime(p) for (p,_) in lp)
  @test prod(p^e for (p, e) in lp) == I
end

@testset "Scaling ideals in function field by base-field elements" begin
  kx, x = rational_function_field(GF(5), :x; cached = false)
  ky, y = polynomial_ring(kx, :y; cached = false)
  F, a = function_field(y^2 - x^3 - x - 1; cached = false)

  function check_scaling(I, c)
    O = order(I)
    cI = @inferred c*I
    @test order(cI) === O
    @test cI == I*c
    @test inv(c)*cI == I
    @test cI == @inferred (F(c)*O)*I
    @test cI == fractional_ideal(O, c*basis_matrix(I))
  end

  Ofin = finite_maximal_order(F)
  Oinf = infinite_maximal_order(F)

  for (O, c) in ((Ofin, x), (Ofin, x^2+1), (Ofin, x//(x + 1)),
                 (Oinf, 1//x), (Oinf, 1//(x^2+1)), (Oinf, (x + 1)//x))
    # a*O is GenOrdFracIdl
    check_scaling(a*O, c)
  end

  # check multiplication of "integral" ideal by the scalar in the base field
  I0 = ideal(Ofin, Ofin(x^2 + 1))
  @test @inferred(x*I0) isa GenOrdFracIdl
  @test @inferred((x//(x + 1))*I0) isa GenOrdFracIdl
  @test @inferred(x*I0) == @inferred(x*fractional_ideal(I0))

  # x has a pole at infinity so we cannot construct (x)_inf directly
  #   yet scaling must work
  I = @inferred a*Oinf
  @test_throws ErrorException Oinf(x)
  @test_throws ErrorException ideal(Oinf, x) * I
  check_scaling(I, x)
end

@testset "Equality in non-maximal order" begin
  x = gen(Hecke.Globals.Qx)
  K, a = number_field(x^2 - 5, :a)
  O = Hecke.GenOrd(ZZ, K) # non-maximal of conductor 2

  I = ideal(O, 2, O(1 + a)) # prime above 2
  A = fractional_ideal(I)
  @test I*inv(I) == A # I is non-invertible!
  @test A == A
  @test A == deepcopy(A)

  O2 = Hecke.GenOrd(ZZ, K)
  @test ideal(O, 2) != ideal(O2, 2)
  @test fractional_ideal(ideal(O, 2)) != fractional_ideal(ideal(O2, 2))
end

@testset "Reduction modulo ideal" begin
  # x and x shifted by a random combination of the ideal's basis vectors must
  # reduce to the same representative: this is what distinguishes a
  # canonical reduction from merely finding *some* congruent representative
  function test_mod_common(O, I, rand_range; ntests::Int = 10)
    @test iszero(mod(zero(O), I))

    b = basis(I)
    for _ in 1:ntests
      x = O([rand(base_ring(O), rand_range) for _ in 1:degree(O)])
      m = mod(x, I)
      @test x - m in I
      @test mod(m, I) == m # already reduced elements are fixed points

      shift = sum(rand(base_ring(O), rand_range)*b[i] for i in 1:length(b))
      @test mod(x + shift, I) == m
    end
  end

  @testset "over F_3(t): unit ideal" begin
    k, t = rational_function_field(GF(3), :t; cached = false)
    K, a = function_field(polynomial(k, [t, 0, 1]); cached = false)
    OK = finite_maximal_order(K)

    I = OK(2)*OK
    @test isone(I)
    test_mod_common(OK, I, 0:3)

    # everything is zero modulo the unit ideal
    for _ in 1:5
      x = OK([rand(base_ring(OK), 0:3) for _ in 1:degree(OK)])
      @test iszero(mod(x, I))
    end
  end

  @testset "over F_3(t): ideal with non-diagonal HNF" begin
    k, t = rational_function_field(GF(3), :t; cached = false)
    K, a = function_field(polynomial(k, [t, 0, 1]); cached = false)
    OK = finite_maximal_order(K)
    kt = base_ring(OK)
    tt = gen(kt)

    # a prime above t+1 (it splits since -t is a square mod t+1);
    # its lower-left HNF basis matrix has a nonzero off-diagonal entry, so
    # that the reduction order (ascending vs descending) actually matters
    I = prime_decomposition(OK, tt + 1)[1][1]
    @test !iszero(Hecke.basis_matrix(I)[2, 1])

    test_mod_common(OK, I, 0:5)

    # regression test: reducing in ascending coordinate order (instead of
    # descending) does not give a canonical representative
    b = basis(I)
    x = OK([tt^3 + tt + 2, tt^2 + 1])
    y = x + b[1] - tt*b[2]
    @test mod(x, I) == mod(y, I)
  end
end
