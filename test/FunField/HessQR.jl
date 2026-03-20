#HessQR is inside module, and the HessQRModule does not export HessQRElem
using Hecke.HessQRModule
import Hecke.HessQRModule: HessQRElem

@testset "HessQR" begin
  R, t = rational_function_field(QQ, :t; cached=false)
  Zx, x = polynomial_ring(ZZ, :x; cached=false)
  Qy, y = polynomial_ring(QQ, :y; cached=false)

  @testset "Constructor" begin
    S = HessQR(Zx, R)

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
end
