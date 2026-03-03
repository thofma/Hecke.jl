k = QQ
kx, x = rational_function_field(k, "x")
kt = parent(numerator(x))
ky, y = polynomial_ring(kx, "y")

import Hecke: divisor


@testset "Divisors" begin

    @testset "Algebraic function field over rationals (1)" begin

      F, a = function_field(y^2 - x^3 - 1)
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

      F, a = function_field(y^4 - 3*y + x^6 +x^2 - 1)
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
