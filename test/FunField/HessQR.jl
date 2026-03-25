#HessQR is inside module, and the HessQRModule does not export HessQRElem
using Hecke.HessQRModule
import Hecke.HessQRModule: HessQRElem

@testset "HessQR" begin
  R, t = rational_function_field(QQ, :t; cached=false)
  Zx, x = polynomial_ring(ZZ, :x; cached=false)
  Qy, y = polynomial_ring(QQ, :y; cached=false)
  S = HessQR(Zx, R)

  @testset "Constructor" begin
    s = HessQRElem(S, ZZ(33), zero(Zx), x^2+x+1)
    @test (s.c, s.f, s.g) == (zero(ZZ), one(Zx), one(Zx))

    s = S(0)
    @test (s.c, s.f, s.g) == (zero(ZZ), one(Zx), one(Zx))

    s = S(3)
    @test (s.c, s.f, s.g) == (ZZ(3), one(Zx), one(Zx))

    s = S(3*x^2+6)
    @test (s.c, s.f, s.g) == (ZZ(3), x^2+2, one(Zx))

    s = HessQRElem(S, ZZ(3), 3*x^2 + 6*x + 12, -x^2 + x + 1)
    @test (s.c, s.f, s.g) == (ZZ(-9), x^2 + 2*x + 4, x^2 - x - 1)

    s = HessQRElem(S, (t^2+1) // (t//2 + 1//4))
    @test (s.c, s.f, s.g) == (ZZ(4), x^2 + 1, 2*x + 1)

    s = HessQRElem(S, y^2+1, 1//2*y + 1//4)
    @test (s.c, s.f, s.g) == (ZZ(4), x^2 + 1, 2*x + 1)

    @test_throws ErrorException HessQRElem(S, (t//2 + 1//4))
    @test_throws ErrorException HessQRElem(S, (1//2*y + 1//4))
  end

  @testset "Euclidean Division" begin
    s1 = HessQRElem(S, ZZ(7), x^2 + 1, x + 1)
    s2 = HessQRElem(S, ZZ(210), x + 1, x^4 + 1)
    s3 = HessQRElem(S, ZZ(42), x^2 + 2, x^5)
    u1 = HessQRElem(S, ZZ(1), x^3 + 1, x^2 + 1)

    # division by zero
    @test divrem(S(0), s1) == (S(0), S(0))
    @test rem(S(0), s1) == S(0)
    @test_throws DivideError divrem(s1, S(0))
    @test_throws DivideError divexact(s1, S(0))
    @test_throws DivideError div(s1, S(0))

    # remainder modulo units
    for u in [S(1), S(-1), u1]
      @test rem(s1, u) == S(0)
      @test rem(s2, u) == S(0)
    end

    # divrem
    # rem(s1, s2) currently results in assert in gcd_sircana
    # rem(s1, S(84)) currently results in crash in gcd_sircana
    # for a in [s1, s2, u1, S(0), S(-5), S(7)], b in [s1, s2, u1, S(-35), S(84)]
    for a in [s1, s2, s3, u1, S(0), S(-5), S(175)], b in [s1, u1, S(-35)]
      q, r = divrem(a, b)
      @test q*b + r == a
      @test iszero(r) || abs(r.c) < abs(b.c)
    end

    # divexact
    @test divexact(S(6), S(3)) == S(2)
    @test divexact(s1*S(3), S(3)) == s1
    @test divexact(s1*s2, s1) == s2
    @test_throws ErrorException divexact(S(7), S(3); check = true)
  end

  @testset "GCD/LCM" begin
    ss = [ HessQRElem(S, ZZ(7), x^2 + 1, x + 1),
           HessQRElem(S, ZZ(210), x + 1, x^4 + 1),
           HessQRElem(S, ZZ(42), x^2 + 2, x^5),
           S(0), S(3), S(-175) ]

    for a in ss, b in ss
      d, u, v = gcdx(a, b)
      @test d == u*a + v*b

      d, l = gcd(a, b), lcm(a, b)
      @test iszero(rem(l, a))
      @test iszero(rem(l, b))
      @test iszero(rem(a, d))
      @test iszero(rem(b, d))
    end
  end
end
