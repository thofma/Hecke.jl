
R, x = rational_function_field(QQ, "x")
L = localization(R, degree)

@testset "DegreeLocalization" begin

    @testset "Constructor" begin

      @test parent_type(KInftyElem{QQFieldElem}) == KInftyRing{QQFieldElem}
      @test elem_type(L) == KInftyElem{QQFieldElem}
      @test function_field(L) == R

    end

    @testset "Canonicalisation" begin

      for i in 1:300
        a = rand(L, 0:10, -10:10)
        c = canonical_unit(a)
        @test (iszero(c) && !is_unit(c)) || is_unit(c)
      end
    end

    @testset "Valuation" begin

      @test valuation(L(x//(x^2 + 1))) == 1
      @test valuation(L(5//5)) == 0
      @test valuation(L((x^2 + 1)//(3//5*x^3))) == 1
      @test valuation(L((2//5)//(x^3 + 3x + 1))) == 3

      for i in 1:300
        a = rand(L, 0:10, -10:10)
        while iszero(a)
          a = rand(L, 0:10, -10:10)
        end
        @test valuation(a) >= 0
      end

    end

    @testset "Parent object call overloading" begin

      @test parent(L(3)) == L
      @test parent(L(1//x)) == L
      @test parent(L(ZZRingElem(3))) == L
      @test parent(L(QQFieldElem(3, 2))) == L
      @test parent(L()) == L
      @test L(6//3) == L(2)
      @test L(R(5)) == L(5)
      @test_throws ErrorException L(x)
    end

    @testset "GCDX" begin
      for i in 1:550
        a = rand(L, 0:10, -10:10)
        b = rand(L, 0:10, -10:10)
        (g, u, v) = gcdx(a, b)
        @test g == u*a + v*b
      end
    end

    @testset "GCD" begin
      for i in 1:550
        a = rand(L, 0:10, -10:10)
        b = rand(L, 0:10, -10:10)
        g = gcd(a, b)
        @test divides(a, g)[1] && divides(b, g)[1]
      end
    end

    @testset "Exact division" begin

      @test divides(L(1//x), L(1//x)) == (true, L(1))
      @test_throws DivideError divexact(L(1//(x + 1)), L())

      for i in 1:300
        a = rand(L, 0:10, -10:10)
        b = rand(L, 0:10, -10:10)
        d = divides(a, b)
        if d[1]
          @test a == d[2] * b
        end
      end
    end

    @testset "Inversion" begin

      @test inv(L((x + 1)//(x + 2))) == L((x + 2)//(x + 1))
      @test inv(L(23)) == L(1//23)
      @test_throws NotInvertibleError inv(L())
    end

    @testset "Binary operators" begin

      @test L((-1//3)//(x^2 - 3*x)) + L(-1//(x - 1//2)) == L((-x^2 + 8//3*x + 1//6)//(x^3 - 7//2*x^2 + 3//2*x))
      @test L((-1//3)//(x^2 - 3*x)) - L(-1//(x - 1//2)) == L((x^2 - 10//3*x + 1//6)//(x^3 - 7//2*x^2 + 3//2*x))
      @test L((-1//3)//(x - 3))*L(-1//(x - 1//2)) == (1//3)//(x^2 - 7//2*x + 3//2)


      @test L(18//2) + L(2//1) == L(11)
      @test L(18//3) - L(1) == L(5)
      @test L(32) * L(4) == L(128)
    end

    @testset "Basic manipulation" begin

      @test iszero(L()) == true
      @test iszero(L(0)) == true
      @test isone(L(1//x)) == false
      @test is_unit(L((x + 1)//(x + 2))) == true


      @test iszero(L(4//3)) == false
      @test isone(L(13//13)) == true
      @test is_unit(L()) == false
    end
end
