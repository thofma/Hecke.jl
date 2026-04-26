import Hecke: divisor

@testset "Divisors" begin
  @testset "Basic Operations" begin
    for base_field in [QQ, finite_field(2, 4)[1], finite_field(101)[1]]
      kx, x = rational_function_field(base_field, :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)

      F, a = function_field(y^3 - x^3 - 1; cached = false)
      Ofin = finite_maximal_order(F)
      Oinf = infinite_maximal_order(F)

      p1, _ = first(factor(ideal(Ofin, x-1)))
      p2    = ideal(Ofin, x^2+x+1)
      p3    = ideal(Ofin, x-3, Ofin(a+3))
      p4, _ = first(factor(ideal(Oinf, base_ring(Oinf)(1//x))))

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
    kx, x = rational_function_field(GF(2), :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)

    F, a = function_field(y^3 - x - 1; cached = false)
    Ofin = finite_maximal_order(F)
    Oinf = infinite_maximal_order(F)

    I = ideal(Oinf, 1//(x^2+x+1))
    fac = factor(I)
    @test length(fac) == 1
    P, e = first(fac)   # e = 6, f = 1
    @test e == 6
    @test 6 == @inferred degree(divisor(I))
    @test 1 == @inferred degree(divisor(P))

    I = ideal(Ofin, x^2+x+1)
    fac = factor(I)
    @test length(fac) == 1
    P, e = first(fac)   # e = 1, f = 3
    @test e == 1
    @test 6 == @inferred degree(divisor(I))
    @test 6 == @inferred degree(divisor(P))
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

  @testset "Riemann-Roch" begin
    for base_field in [QQ, finite_field(2, 4)[1], finite_field(5, 2)[1], finite_field(101)[1]]
      kx, x = rational_function_field(base_field, :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)
      for poly in [y^3 - x - 1, y^3 - x^3 - 1, y^3 - x^17 - 1]
        F, a = function_field(poly; cached = false)
        Ofin, Oinf = finite_maximal_order(F), infinite_maximal_order(F)

        g = genus(F)
        CD = canonical_divisor(F)

        p1, _ = @inferred first(factor(ideal(Ofin, x - 13)))
        p2, _ = first(factor(ideal(Oinf, base_ring(Oinf)(1//x))))
        D1, D2 = divisor(p1), divisor(p2)

        # Riemann-Roch: l(D) - l(K-D) = deg(D) - g + 1
        for n in -3:3
          D = n*D1 + D2
          @test dimension(D) - index_of_speciality(D) == degree(D) - g + 1
          D = D1 + n*D2
          @test dimension(D) - index_of_speciality(D) == degree(D) - g + 1
        end

        # 2 * (l(K) - l(0)) = deg(K) - deg(0)
        @test degree(CD) == 2*g - 2
        @test degree(trivial_divisor(F)) == 0
        @test dimension(CD) - dimension(trivial_divisor(F)) == g - 1

        # l(D) = 0 for deg(D) < 0
        @test dimension(-3*D1) == 0
        @test dimension(-D2) == 0
        @test dimension(-D1 - 3*D2) == 0
      end
    end
  end

    @testset "Algebraic function field over rationals (1)" begin
      kx, x = rational_function_field(QQ, :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)
      F, a = function_field(y^2 - x^3 - 1; cached = false)
      Ofin = finite_maximal_order(F)
      Oinf = infinite_maximal_order(F)

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

      D = 3*D3 - D1
      Do = @inferred divisor(inv(p1), p3^3)

      Dp = D1 + D3
      @test D1 == finite_divisor(Dp)
      @test D3 == infinite_divisor(Dp)

      #Elliptic curve group law
      @test is_principal(D1 + D2 - 2*D3)
      @test is_zero(D - D)

      @test D == Do
      @test 3 == @inferred valuation(D, p3)
      @test -1 == @inferred valuation(D, p1)
      @test 0 == @inferred valuation(D, p2)

      @test 2 == @inferred degree(D)

      @test 2 == @inferred dimension(D)
      @test 0 == @inferred index_of_speciality(D)

      DD = 3*D
      @test !(DD > D)
      @test (D + D2 > D)

      L = @inferred riemann_roch_space(DD)
      @test length(L) == 6

      for f in L
        @test is_effective(divisor(f) + DD)
      end

      D_z = zero_divisor(F(x-3))
      D_p = pole_divisor(F(x-3))
      @test is_effective(D_z)
      @test !is_effective(D)
      @test (D_z - D_p) == divisor(F(x-3))

      @test F == function_field(D)
      Dfin, Dinf = ideals(D)
      @test divisor(Dfin) + divisor(Dinf) == D

      Df = different_divisor(F)
      @test degree(Df) == 4
      @test 0 == @inferred dimension(Df - 6*divisor(p3))
      @test 2 == @inferred index_of_speciality(Df-6*divisor(p3))

      KF = canonical_divisor(F)
      @test 0 == @inferred degree(KF)
      @test 1 == @inferred genus(F)
    end

    @testset "Algebraic function field over rationals (2)" begin
      kx, x = rational_function_field(QQ, :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)
      F, a = function_field(y^4 - 3*y + x^6 +x^2 - 1; cached = false)
      Ofin = finite_maximal_order(F)
      Oinf = infinite_maximal_order(F)

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
        @test is_effective(divisor(df.f) + KF)
      end
    end
end
