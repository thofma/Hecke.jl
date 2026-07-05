import Hecke: divisor

@testset "Divisors" begin
  @testset "Basic Operations" begin
    for base_field in [QQ, finite_field(2, 4)[1], finite_field(101)[1]]
      kx, x = rational_function_field(base_field, :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)

      F, a = function_field(y^3 - x^3 - 1; cached = false)
      Ofin = @inferred finite_maximal_order(F)
      Oinf = @inferred infinite_maximal_order(F)

      p1, _ = first(@inferred factor(ideal(Ofin, x-1)))
      p2    = ideal(Ofin, x^2+x+1)
      p3    = ideal(Ofin, x-3, Ofin(a+3))
      p4, _ = first(@inferred factor(ideal(Oinf, base_ring(Oinf)(1//x))))

      d1, d2, d3, d4 = divisor.((p1, p2, p3, p4))
      Hecke.assure_has_support.((d1, d2, d3, d4))

      D1 = trivial_divisor(F)
      D2 = d1 - d2 # note that this is guaranteed to be non-trivial
      @test !(D1 < D2)
      @test !(D2 < D1)

      D1 = d1 + 5*d2
      D2 = d1 + 2*d2 - 3*d3
      Dgcd = @inferred(gcd(D1, D2))
      Dlcm = @inferred(lcm(D1, D2))

      @test Dgcd == d1 + 2*d2 - 3*d3
      @test Dgcd == gcd(D2, D1)
      @test Dlcm == d1 + 5*d2
      @test Dlcm == lcm(D2, D1)
      @test Dgcd + Dlcm == D1 + D2

      @test valuation(Dgcd, p1) == valuation(Dgcd.finite_ideal, p1)
      @test valuation(Dgcd, p4) == valuation(Dgcd.infinite_ideal, p4)
      @test valuation(Dlcm, p1) == valuation(Dlcm.finite_ideal, p1)
      @test valuation(Dlcm, p4) == valuation(Dlcm.infinite_ideal, p4)

      D1 = d1 + 3*d4
      D2 = 2*d1 - 3*d3
      Dgcd = @inferred(gcd(D1, D2))
      Dlcm = @inferred(lcm(D1, D2))

      @test Dgcd == d1 - 3*d3
      @test Dgcd == gcd(D2, D1)
      @test Dlcm == 2*d1 + 3*d4
      @test Dlcm == lcm(D2, D1)
      @test Dgcd + Dlcm == D1 + D2

      @test valuation(Dgcd, p1) == valuation(Dgcd.finite_ideal, p1)
      @test valuation(Dgcd, p4) == valuation(Dgcd.infinite_ideal, p4)
      @test valuation(Dlcm, p1) == valuation(Dlcm.finite_ideal, p1)
      @test valuation(Dlcm, p4) == valuation(Dlcm.infinite_ideal, p4)

      D1 = d1 - 3*d4
      D2 = 2*d1
      Dgcd = @inferred(gcd(D1, D2))
      Dlcm = @inferred(lcm(D1, D2))
      @test Dgcd == D1
      @test Dgcd == gcd(D2, D1)
      @test Dlcm == 2*d1
      @test Dlcm == lcm(D2, D1)
      @test Dgcd + Dlcm == D1 + D2

      @test valuation(Dgcd, p1) == valuation(Dgcd.finite_ideal, p1)
      @test valuation(Dgcd, p4) == valuation(Dgcd.infinite_ideal, p4)
      @test valuation(Dlcm, p1) == valuation(Dlcm.finite_ideal, p1)
      @test valuation(Dlcm, p4) == valuation(Dlcm.infinite_ideal, p4)
    end
  end

  @testset "Degree" begin
    function test_degree(I, d)
      D = divisor(I)

      @assert !Hecke.has_support(D)
      @test d == @inferred degree(D)

      Hecke.assure_has_support(D)
      @test d == @inferred degree(D)
    end

    kx, x = rational_function_field(GF(2), :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)

    F, a = function_field(y^3 - x - 1; cached = false)
    Ofin = @inferred finite_maximal_order(F)
    Oinf = @inferred infinite_maximal_order(F)

    I = ideal(Oinf, 1//(x^2+x+1))
    fac = @inferred factor(I)
    @test length(fac) == 1
    P, e = first(fac)   # e = 6, f = 1
    @test e == 6
    test_degree(I, 6)
    test_degree(P, 1)

    I = ideal(Ofin, x^2+x+1)
    fac = @inferred factor(I)
    @test length(fac) == 1
    P, e = first(fac)   # e = 1, f = 3
    @test e == 1
    test_degree(I, 6)
    test_degree(P, 6)
  end

  @testset "Pole/Zero divisors" begin
    kx, x = rational_function_field(GF(5), :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)

    function test_pole_degree(f, d)
      @test degree(pole_divisor(f)) == d

      D = divisor(f)
      @assert !Hecke.has_support(D)
      @test degree(pole_divisor(D)) == d

      Hecke.assure_has_support(D)
      @test degree(pole_divisor(D)) == d
    end

    function test_pole_zero(D_or_f)
      @test degree(pole_divisor(D_or_f)) == degree(zero_divisor(D_or_f))
      @test is_effective(pole_divisor(D_or_f))
      @test is_effective(zero_divisor(D_or_f))
    end

    function test_pole_zero_f(f)
      test_pole_zero(f)

      D = divisor(f)
      @assert !Hecke.has_support(D)
      test_pole_zero(D)

      Hecke.assure_has_support(D)
      test_pole_zero(D)
    end

    # ramification at infinity is 2
    F, a = function_field(y^2 - x^3 - x - 1; cached = false)
    @test genus(F) == 1
    test_pole_degree(F(x), 2)
    test_pole_degree(F(y), 3)
    for f in (F(x), F(y))
      test_pole_zero_f(f)
    end

    # ramification at infinity is 3
    F, a = function_field(y^3 - x^2 - 1; cached = false)
    @test genus(F) == 1
    test_pole_degree(F(x), 3)
    test_pole_degree(F(y), 2)
    for f in (F(x), F(y))
      test_pole_zero_f(f)
    end
  end

  @testset "Not Separable Extension" begin
    k = finite_field(3; cached = false)[1]
    kx, x = rational_function_field(k, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)

    # current implementation of separating_element/canonical_divisor
    #   assumes separable extension

    # purely inseparable
    F, a = function_field(y^3 - x; cached = false)
    @test_throws ArgumentError Hecke.separating_element(F)
    @test_throws ArgumentError Hecke.canonical_divisor(F)
    @test_throws ArgumentError Hecke.genus(F)

    # (not purely) inseparable
    F, a = function_field(y^6 - x*y^3 + x; cached = false)
    @test_throws ArgumentError Hecke.separating_element(F)
    @test_throws ArgumentError Hecke.canonical_divisor(F)
    @test_throws ArgumentError Hecke.genus(F)
  end

  @testset "principal with generator: ellcrv" begin
    function check_principal(D, expected_gen)
      @test is_principal(D)
      ok, f = @inferred is_principal_with_data(D)
      @test ok
      @test divisor(f) == D                         # witness generates D
      @test is_zero(divisor(f * inv(expected_gen))) # witness is equivalent to expected_gen
    end

    function check_not_principal(D)
      @test !is_principal(D)
      ok, f = @inferred is_principal_with_data(D)
      @test !ok
      @test isone(f) # we document the return value, so let's keep it checked
    end

    kx, x = rational_function_field(QQ, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    F, a = function_field(y^2 - x^3 - 1; cached = false)   # E: y^2 = x^3 + 1
    Ofin = finite_maximal_order(F)
    Oinf = infinite_maximal_order(F)

    point_divisor(X, Y) = divisor(ideal(Ofin, x - X, Ofin(a - Y)))
    D1, D2 = point_divisor(0, 1), point_divisor(0, -1)  # order 3
    D3, D4 = point_divisor(2, 3), point_divisor(2, -3)  # order 6
    D5 = point_divisor(-1, 0)                           # order 2

    p_inf, _ = first(factor(ideal(Oinf, base_ring(Oinf)(1//x))))
    D6 = divisor(p_inf)                                 # infinity

    for D in (D1, D2, D3, D4, D5, D6) # single-point divisors are non-principal
      check_not_principal(D)
    end

    # x - 2 = 0 hits E at (2, 3), (2, -3) and twice at infinity.
    D = D3 + D4 - 2*D6
    @test degree(D) == 0
    check_principal(D, F(x - 2))

    # x + 1 = 0 hits E at (-1, 0) with multiplicity 2 and twice at infinity.
    D = 2*D5 - 2*D6
    @test degree(D) == 0
    check_principal(D, F(x + 1))

    # y = x + 1 meets E at (0, 1), (2, 3), (-1, 0)
    D = D1 + D3 + D5 - 3*D6
    @test degree(D) == 0
    check_principal(D, a - F(x) - 1)

    D = D3 - D6
    @test degree(D) == 0
    check_not_principal(D)

    D = D1 + D3 - 2*D6
    @test degree(D) == 0
    check_not_principal(D)
  end

    @testset "Algebraic function field over rationals (1)" begin
      kx, x = rational_function_field(QQ, :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)
      F, a = function_field(y^2 - x^3 - 1; cached = false)
      Ofin = @inferred finite_maximal_order(F)
      Oinf = @inferred infinite_maximal_order(F)

      p1 = @inferred ideal(Ofin, x-2, Ofin(a - 3))
      p2 = @inferred ideal(Ofin, x-2, Ofin(a + 3))
      facs = @inferred factor(ideal(Oinf, base_ring(Oinf)(1//x)))
      p3 = collect(facs)[1][1]

      D1 = divisor(p1)
      D2 = divisor(p2)
      D3 = divisor(p3)
      @test_throws ArgumentError divisor(zero(F))

      @test 0*D1 == 0*D2

      @test trivial_divisor(F) == 0 * D1
      @test degree(trivial_divisor(F)) == 0
      @test 1 == length(@inferred riemann_roch_space(trivial_divisor(F)))
      @test 1 == @inferred dimension(trivial_divisor(F))

      D = 3*D3 - D1
      Do = @inferred divisor(inv(p1), p3^3)

      Dp = D1 + D3
      @test D1 == finite_divisor(Dp)
      @test D3 == infinite_divisor(Dp)

      #Elliptic curve group law
      @test is_principal(D1 + D2 - 2*D3)
      @test 1 == length(@inferred riemann_roch_space(D1 + D2 - 2*D3))
      @test 1 == @inferred dimension(D1 + D2 - 2*D3)

      @test is_zero(D - D)

      @test D == Do
      @test  3 == @inferred valuation(D, p3)
      @test -1 == @inferred valuation(D, p1)
      @test  0 == @inferred valuation(D, p2)

      @test 2 == @inferred degree(D)

      @test 2 == @inferred dimension(D)
      @test 0 == @inferred index_of_speciality(D)

      DD = 3*D
      @test !(DD > D)
      @test (D + D2 > D)

      L = @inferred riemann_roch_space(DD)
      @test 6 == length(L)
      @test 6 == @inferred dimension(DD)

      for f in L
        D = divisor(f) + DD
        @test is_effective(D)

        Hecke.assure_has_support(D)
        @test is_effective(D)
      end

      @test F == function_field(D)
      Dfin, Dinf = ideals(D)
      @test divisor(Dfin) + divisor(Dinf) == D

      Df = different_divisor(F)
      @test degree(Df) == 4
      @test 0 == @inferred dimension(Df - 6*divisor(p3))
      @test 0 == length(@inferred riemann_roch_space(Df - 6*divisor(p3)))
      @test 2 == @inferred index_of_speciality(Df-6*divisor(p3))

      KF = canonical_divisor(F)
      @test 0 == @inferred degree(KF)
      @test 1 == @inferred genus(F)

      let D = divisor(F(x-3))
        D_z = @inferred zero_divisor(F(x-3))
        D_p = @inferred pole_divisor(F(x-3))
        @test is_effective(D_z)
        @test is_effective(D_p)
        @test D == D_z - D_p

        D_z = @inferred zero_divisor(D)
        D_p = @inferred pole_divisor(D)
        @test is_effective(D_z)
        @test is_effective(D_p)
        @test D == D_z - D_p
      end
    end

    @testset "Algebraic function field over rationals (2)" begin
      kx, x = rational_function_field(QQ, :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)
      F, a = function_field(y^4 - 3*y + x^6 +x^2 - 1; cached = false)
      Ofin = @inferred finite_maximal_order(F)
      Oinf = @inferred infinite_maximal_order(F)

      p1 = @inferred ideal(Ofin, x-2)

      facs = @inferred factor(ideal(Oinf, base_ring(Oinf)(1//x)))
      p3 = collect(facs)[1][1]

      D = 3*divisor(p3) - divisor(p1)
      D2 = @inferred divisor(inv(p1), p3^3)

      @test D == D2
      @test 3 == @inferred valuation(D, p3)
      @test -1 == @inferred valuation(D, p1)

      @test degree(D) == 2

      @test 1 == @inferred dimension(D)
      @test 5 == @inferred index_of_speciality(D)

      @test F == function_field(D)
      Dfin, Dinf = ideals(D)
      @test divisor(Dfin) + divisor(Dinf) == D

      Df = different_divisor(F)
      @test 20 == @inferred degree(Df)
      @test 4 == @inferred dimension(Df-6*divisor(p3))
      @test 2 == @inferred index_of_speciality(Df-6*divisor(p3))

      KF = canonical_divisor(F)
      @test 12 == @inferred degree(KF)
      @test 7 == @inferred genus(F)

      L = @inferred basis_of_differentials(F)
      for df in L
        D = divisor(df.f) + KF
        @test is_effective(D)

        Hecke.assure_has_support(D)
        @test is_effective(D)
      end
    end
end
