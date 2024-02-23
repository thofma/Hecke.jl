
Qx,x = FlintQQ["x"]
K,a = number_field(x^6+108)
OK = ring_of_integers(K)
lp = prime_decomposition(OK, 5)
P = lp[1][1]
L = localization(OK, P)

@testset "OrderLocalization" begin

  @testset "Constructor" begin

    @test parent_type(OrdLocElem{AbsSimpleNumFieldElem}) == OrdLoc{AbsSimpleNumFieldElem}

    lp = prime_decomposition(OK, 3)
    P = lp[1][1]
    L = localization(OK, P)

    @test elem_type(L) == OrdLocElem{AbsSimpleNumFieldElem}
    @test Hecke.nf(L) == K
    @test Hecke.nf(L()) == K

end

#=
  @testset "Canonicalisation" begin
  for i in 1:300
    a = rand(L, -10:10)
    c = canonical_unit(a)
    @test is_unit(c)
  end
end

    @testset "Valuation" begin

      @test valuation(L(5)) == 1
      @test valuation(L(5//5)) == 0
      @test valuation(L(5//12)) == 1
      @test valuation(L(500)) == 3

      for i in 1:300
        a = rand(L, -10:10)
        while iszero(a)
          a = rand(L, -10:10)
        end
        @test valuation(a) >= 0
      end

    end
    =#

    @testset "Parent object call overloading" begin

      @test parent(L(3)) == L
      @test L(6//3) == L(2)
      @test L(K(5)) == L(5)
      @test L(OK(5)) == L(5)
      @test_throws ErrorException L(24//90)
    end

    @testset "GCDX" begin
      for i in 1:550
        a = rand(L, -10:10)
        b = rand(L, -10:10)
        (g,u,v) = gcdx(a,b)
        @test g == u*a + v*b
      end
    end

    @testset "GCD" begin
      for i in 1:550
        a = rand(L, -10:10)
        b = rand(L, -10:10)
        g = gcd(a,b)
        @test divides(a,g)[1] && divides(b,g)[1]
      end
    end

    @testset "Exact division" begin

      @test divides(L(15),L(3)) == (true, L(5))
      @test divides(L(15),L(30)) == (true, L(1//2))
      @test divides(L(15),L(25)) == (false, L(0))
      @test_throws ErrorException divexact(L(8),L(10))
      for i in 1:300
        a = rand(L, -10:10)
        b = rand(L, -10:10)
        d = divides(a,b)
        if d[1]
          @test a == d[2] * b
        end
      end
    end

    @testset "Inversion" begin

      @test inv(L(8)) == L(1//8)
      @test inv(L(23)) == L(1//23)
      @test_throws ErrorException inv(L(40))
      @test_throws DivideError inv(L())
    end

    @testset "Binary operators" begin

      @test L(19) + L(1) == L(20)
      @test L(19) - L(1) == L(18)
      @test L(3) * L(4//2) == L(6)


      @test L(18//2) + L(2//1) == L(11)
      @test L(18//3) - L(1) == L(5)
      @test L(32) * L(4) == L(128)
    end

    @testset "Basic manipulation" begin

      @test iszero(L()) == true
      @test iszero(L(0)) == true
      @test isone(L(2//3)) == false
      @test is_unit(L(24)) == true


      @test iszero(L(4//3)) == false
      @test isone(L(13//13)) == true
      @test is_unit(L(50//2)) == false
    end
end
