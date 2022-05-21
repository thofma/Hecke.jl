@testset "Localization" begin

  R = FlintZZ
  Qx,x = FlintQQ["x"]

  @testset "Constructor" begin

    @test parent_type(LocElem{fmpz}) == Loc{fmpz}

    L = Localization(R, 17)
    @test elem_type(L) == LocElem{fmpz}
    @test base_ring(L) == FlintZZ
    @test base_ring(L()) == FlintZZ

    L = Localization(R, [2,R(3)])
    @test elem_type(L) == LocElem{fmpz}
    @test base_ring(L) == FlintZZ
    @test base_ring(L()) == FlintZZ

    @test parent_type(LocElem{fmpq_poly}) == Loc{fmpq_poly}

    L = Localization(Qx, x^2+1)
    @test elem_type(L) == LocElem{fmpq_poly}
    @test base_ring(L) == Qx
    @test base_ring(L()) == Qx

    L = Localization(Qx, 4*x^2+x+1)
    @test elem_type(L) == LocElem{fmpq_poly}
    @test base_ring(L) == Qx
    @test base_ring(L()) == Qx

    L = Localization(Qx, [3*x^4+x+18, x^9+3])
    @test elem_type(L) == LocElem{fmpq_poly}
    @test base_ring(L) == Qx
    @test base_ring(L()) == Qx

    @test_throws ErrorException  Localization(R,Vector{Int64}())
  end

  @testset "Canonicalisation" begin

    L = Localization(R, 23)
    @test canonical_unit(L(23)) == one(L)
    @test canonical_unit(L(230)) == L(10)
    @test canonical_unit(L(230//45)) == L(10//45)

    L = Localization(R, [2,7])
    @test canonical_unit(L(2)) == one(L)
    @test canonical_unit(L(28)) == one(L)
    @test canonical_unit(L(49//55)) == L(1//55)
    @test canonical_unit(L(18//11)) == L(9//11)
    @test canonical_unit(L(49//55)) == L(1//55)

    L = Localization(Qx, 5x^2+3x+2)
    @test canonical_unit(L(5x^2+3x+2)) == L(5)
    @test canonical_unit(L(28)) == L(28)
    @test canonical_unit(L(5*x^4+3*x^3+12*x^2+6*x+4)) == L(5*(x^2+2))

    L = Localization(Qx,[5x^2+3x+2, x^16+x+3])
    @test canonical_unit(L(x^16+x+3)) == one(L)
    @test canonical_unit(L(89)) == L(89)
    @test canonical_unit(L((5*x^4+3*x^3+12*x^2+6*x+4)//(x^3+9))) == inv(L((1//5*x^3+9//5)//(x^2+2)))
  end

    @testset "Parent object call overloading" begin

      L = Localization(R,5)
      @test parent(L(4//7)) == L
      @test_throws ErrorException L(24//50)

      L = Localization(R,[2,3])
      @test_throws ErrorException L(11//2)
      @test_throws ErrorException L(13//6)
      @test_throws ErrorException L(14//18)

      L1 = Localization(Qx, 5x^2+3x+2)
      L2 = Localization(Qx, 7x^3+2)
      @test_throws ErrorException L1(L2(5))
      @test parent(L1(4x//7)) == L1

      L = Localization(Qx,[x^2+2,3x^3+5])
      @test parent(L(3x^2+6)) == L
      @test_throws ErrorException L(15//(3x^2+6))
      @test_throws ErrorException L(17//(9*x^5+18*x^3+15*x^2+30))
      @test_throws ErrorException L(19//(9*x^6+54*x^5+18*x^4+123*x^3+90*x^2+30*x+180))
    end

    @testset "GCDX" begin

      L = Localization(R,19)
      for i in 1:300
        a = rand(L)
        b = rand(L)
        (g,u,v) = gcdx(a,b)
        @test g == u*a + v*b
      end

      L = Localization(R,[3,23])
      for i in 1:300
        a = rand(L)
        b = rand(L)
        (g,u,v) = gcdx(a,b)
        @test g == u*a + v*b
      end

      L = Localization(Qx, x^6+108)
      a = L(x^10+2*x^8+14*x^7+49*x^5+42*x^3+294*x^2+588)
      b = L(x^11+14*x^8+21*x^6+294*x^3+6)
      (g,u,v) = gcdx(a,b)
      @test g == u*a + v*b

      L = Localization(Qx, [x^6+108, x^8+12x^3+3])
      a = L(x^10+2*x^8+14*x^7+49*x^5+42*x^3+294*x^2+588)
      b = L(x^11+14*x^8+21*x^6+294*x^3+6)
      (g,u,v) = gcdx(a,b)
      @test g == u*a + v*b
    end

    @testset "GCD and LCM" begin

      L = Localization(R,23)
      @test gcd(L(0),L(9)) == L(1)
      @test gcd(L(12),L(9)) == L(1)
      @test gcd(L(46//5),L(23)) == L(23)
      for i in 1:300
        a = rand(L)
        b = rand(L)
        g = gcd(a,b)
        @test divides(a,g)[1] && divides(b,g)[1]
      end

      L = Localization(R,[13,17])
      @test gcd(L(10),L(0)) == L(1)
      @test gcd(L(26),L(0)) == L(13)
      @test gcd(L(12),L(11)) == L(1)
      @test gcd(L(26//5),L(221)) == L(13)
      for i in 1:300
        a = rand(L)
        b = rand(L)
        g = gcd(a,b)
        @test divides(a,g)[1] && divides(b,g)[1]
      end

      L = Localization(Qx, x^6+108)
      a = L(x^10+2*x^8+14*x^7+49*x^5+42*x^3+294*x^2+588)
      b = L(x^11+14*x^8+21*x^6+294*x^3+6)
      g = gcd(a,b)
      @test g == L(1)
      a = L(x^16+2*x^14+14*x^13+49*x^11+108*x^10+42*x^9+510*x^8+1512*x^7+588*x^6+5292*x^5+4536*x^3+31752*x^2+63504)
      b = L(x^17+14*x^14+21*x^12+108*x^11+294*x^9+1512*x^8+2274*x^6+31752*x^3+648)
      g = gcd(a,b)
      @test g == L(x^6+108)

      L = Localization(Qx, [x^6+108, x^8+12x^3+3])
      a = L(x^10+2*x^8+14*x^7+49*x^5+42*x^3+294*x^2+588)
      b = L(x^13+2*x^11+14*x^10+49*x^8+42*x^6+294*x^5+588*x^3+6*x^2+12)
      g = gcd(a,b)
      @test g == L(1)

      L = Localization(R,R(3))
      @test lcm(L(15),L(9)) == L(9)
      for i in 1:300
        a = rand(L)
        b = rand(L)
        l = lcm(a,b)
        @test divides(l,a)[1] && divides(l,b)[1]
      end
    end

    @testset "Exact division" begin
      L = Localization(R,R(19))
      @test divides(L(15),L(3)) == (true, L(5))
      @test divides(L(15),L(30)) == (true, L(1//2))
      @test divides(L(15),L(19))[1] == false
      @test_throws ErrorException divexact(L(8),L(38))
      for i in 1:300
        a = rand(L)
        b = rand(L)
        d = divides(a,b)
        if d[1]
          @test a == d[2] * b
        end
      end

      L = Localization(R,[11,13])
      @test_throws ErrorException divexact(L(9),L(22))
      @test divides(L(15),L(3)) == (true, L(5))
      @test divides(L(15),L(30)) == (true, L(1//2))
      @test divides(L(15),L(22))[1] == false
      for i in 1:300
        a = rand(L)
        b = rand(L)
        d = divides(a,b)
        if d[1]
          @test a == d[2] * b
        end
      end

      L = Localization(Qx, x^6+108)
      @test_throws ErrorException divexact(L(9),L(2x^6+216))
      a = L(x^10+2*x^8+14*x^7+49*x^5+42*x^3+294*x^2+588)
      b = L(x^11+14*x^8+21*x^6+294*x^3+6)
      g = divides(a,b)
      @test a == b * g[2]
      @test g[1] == true
      a = L(x^16+2*x^14+14*x^13+49*x^11+108*x^10+42*x^9+510*x^8+1512*x^7+588*x^6+5292*x^5+4536*x^3+31752*x^2+63504)
      b = L(x^17+14*x^14+21*x^12+108*x^11+294*x^9+1512*x^8+2274*x^6+31752*x^3+648)
      @test a == b * g[2]
      @test g[1] == true
    end

    @testset "Inversion" begin
      L = Localization(R,R(19))
      @test inv(L(15)) == L(1//15)
      @test inv(L(20)) == L(1//20)
      @test_throws ErrorException inv(L(38))
      @test_throws ErrorException inv(L())

      L = Localization(R,[11,13])
      @test_throws ErrorException inv(L(11))
      @test inv(L(14)) == L(1//14)

      L = Localization(Qx, x^6+108)
      @test_throws ErrorException inv(L(2x^6+216))
      @test inv(L(x^2+108)) == L(1//(x^2+108))

      L = Localization(Qx, [x^6+3, x^3+5])
      @test_throws ErrorException inv(L(2x^6+6))
      @test inv(L(x^2+108)) == L(1//(x^2+108))
    end

    @testset "Binary operators" begin
      L = Localization(R,19)
      @test L(19) + L(1) == L(20)
      @test L(19) - L(1) == L(18)
      @test L(3) * L(4//2) == L(6)

      L = Localization(R,[11,13])
      @test L(18//2) + L(2//1) == L(11)
      @test L(18//3) - L(1) == L(5)
      @test L(32) * L(4) == L(128)

      L = Localization(Qx, x^6+108)
      @test L(18x//2) + L(2x//1) == L(11x)
      @test L(18x//3) - L(1x) == L(5x)
      @test L(32x) * L(4x) == L(128x^2)

      L = Localization(Qx, [x^6+3, x^3+5])
      @test L(18x//2) + L(2x//1) == L(11x)
      @test L(18x//3) - L(1x) == L(5x)
      @test L(32x) * L(4x) == L(128x^2)
    end

    @testset "Basic manipulation" begin
      L = Localization(R,19)
      @test iszero(L(0)) == true
      @test isone(L(2//3)) == false
      @test is_unit(L(24)) == true

      L = Localization(R,[11,13])
      @test iszero(L(4//5)) == false
      @test isone(L(13//13)) == true
      @test is_unit(L(26//2)) == false

      L = Localization(Qx, x^6+108)
      @test iszero(L(x^2 + x)) == false
      @test isone(L(x^2//x^2)) == true
      @test is_unit(L(x)) == true

      L = Localization(Qx, [x^6+3, x^3+5])
      @test iszero(L(x-x)) == true
      @test isone(L(x^2+3x)) == false
      @test is_unit(L((x^3+5)//(x^3+5)))
    end
end
