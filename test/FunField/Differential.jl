import Hecke: divisor

@testset "Differentials" begin
  @testset "Differential basic operations" begin
    for base_field in [QQ, finite_field(2, 4)[1], finite_field(5, 2)[1], finite_field(101)[1]]
      kx, x = rational_function_field(base_field, :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)
      for poly in [y^3 - x - 1, y^3 - x^3 - 1, y^3 - x^17 - 1]
        F, a = function_field(poly; cached = false)
        @test is_zero(differential(one(F)))

        dx = @inferred differential(F(x))
        dy = @inferred differential(a)
        @test dx != dy
        @test is_one(dx.f)
        @test !is_zero(divisor(dx))
        @test !is_zero(divisor(dy))

        @test differential(F(x) + a)    == @inferred(dx + dy)
        @test differential(F(x) - a)    == @inferred(dx - dy)
        @test differential(F(x) * a)    == @inferred(a*dx + F(x)*dy)
        @test differential(F(x) // a)   == @inferred((a*dx - F(x)*dy) // a^2)
        @test differential(F(x)^3) // 3 == @inferred((F(x)^2)*dx)
        @test differential(F(x)^3)      == @inferred(3*(F(x)^2)*dx)
      end
    end
  end

  @testset "EllCrv Invariant Differential" begin
    B, t = finite_field(2, 4)
    kx, x = rational_function_field(B, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)

    # ordinary characteristic 2: w = dx/x
    F, a = function_field(y^2 + x*y + x^3 + x^2 + t^2+1; cached = false)

    dx = differential(F(x))
    @test !is_zero(divisor(dx))
    w = dx // F(x)
    @test is_zero(divisor(w))

    # supersingular characteristic 2: w = dx/a_3
    F, a = function_field(y^2 + (t^3+1)*y + x^3 + x + 1; cached = false)

    dx = differential(F(x))
    @test is_zero(divisor(dx))
    w = dx // F(t^3+1)
    @test is_zero(divisor(w))

    # characteristic 3: w = dx/(-y) = - dy/(a_2*x - a_4)
    B, t = finite_field(3, 2)
    kx, x = rational_function_field(B, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    F, a = function_field(y^2 - x^3 - t*x^2 - t^2*x - 1; cached = false)

    dx = differential(F(x))
    @test !is_zero(divisor(dx))
    dy = differential(a)
    @test !is_zero(divisor(dy))

    w = dx // (-a)
    @test is_zero(divisor(w))
    w = - dy // (F(t*x) - F(t^2))
    @test is_zero(divisor(w))

    # characteristic > 3: w = dx/(2*y) = dy/(3*x^2 + A)
    B, t = finite_field(7, 2)
    kx, x = rational_function_field(B, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    F, a = function_field(y^2 - x^3 - t^4*x - 1; cached = false)

    dx = differential(F(x))
    @test !is_zero(divisor(dx))
    dy = differential(a)
    @test !is_zero(divisor(dy))

    w = dx // (2*a)
    @test is_zero(divisor(w))
    w = dy // (3*F(x)^2 + F(t^4))
    @test is_zero(divisor(w))

    # characteristic = 0: w = dx/(2*y) = dy/(3*x^2 + A)
    kx, x = rational_function_field(QQ, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    F, a = function_field(y^2 - x^3 - 3*x - 1; cached = false)

    dx = differential(F(x))
    @test !is_zero(divisor(dx))
    dy = differential(a)
    @test !is_zero(divisor(dy))

    w = dx // (2*a)
    @test is_zero(divisor(w))
    w = dy // (3*F(x)^2 + 3)
    @test is_zero(divisor(w))
  end
end
