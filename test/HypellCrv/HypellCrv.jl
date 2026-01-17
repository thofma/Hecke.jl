@testset "Generic hyperelliptic curve" begin

  @testset "Constructors" begin
    Qx, x = polynomial_ring(QQ, "x")


    f1 = x^6+3*x+5
    h1 = x+2
    C = @inferred hyperelliptic_curve(f1, h1)
    @test C == hyperelliptic_curve(f1, h1)
    @test hash(C) == hash(hyperelliptic_curve(f1, h1))
    f2, h2 = @inferred hyperelliptic_polynomials(C)
    @test f1 == f2 && h1 == h2
    @test @inferred genus(C) == 2
    @test @inferred base_field(C) == QQ
    @test @inferred discriminant(C) == -91424898432

    Qxy, (x, y) = polynomial_ring(QQ, ["x", "y"])
    @test @inferred equation(C) == -x^6 + x*y - 3*x + y^2 + 2*y - 5
    Qxyz, (x, y, z) = polynomial_ring(QQ, ["x", "y", "z"])
    @test @inferred homogeneous_equation(C) == -x^6 + x*y*z^2 - 3*x*z^5 + y^2 + 2*y*z^3 - 5*z^6
    @test C == C

    Fx, x = polynomial_ring(GF(37), "x")

    f1 = x^9+8*x^7-5*x^6+3*x^2+7
    h1 = zero(Fx)
    C = @inferred hyperelliptic_curve(f1)
    f2, h2 = @inferred hyperelliptic_polynomials(C)
    @test f1 == f2 && h1 == h2
    @test @inferred genus(C) == 4
    @test @inferred base_field(C) == GF(37)
    @test @inferred discriminant(C) == 29

    F = GF(37, 3)
    C = base_change(F, C)
    @test @inferred base_field(C) == F

  end

  @testset "Points" begin
    Qx, x = polynomial_ring(QQ, "x")

    f = x^6+3*x+5
    C = @inferred hyperelliptic_curve(f)
    P = @inferred points_with_x_coordinate(C, 1)
    @test C([1, -3, 1]) in P && C([1, 3, 1]) in P

    @test C([-5*20, 125*20^3 , 3*20]) == C([-5, 125, 3])
    infpoints = @inferred points_at_infinity(C)
    @test C([1, 1, 0]) in infpoints && C([1,-1,0]) in infpoints
    @test @inferred is_infinite(infpoints[1])

    f = x^6 -2*x^5 -x^3 + x^2 +5*x+1
    C = @inferred hyperelliptic_curve(f)
    pts = @inferred find_points(C, 1000)
    @test length(pts) == 8

    F = GF(37)
    Fx, x = polynomial_ring(F, "x")

    f = x^6+3*x+5
    C = @inferred hyperelliptic_curve(f)
    P = @inferred points_with_x_coordinate(C, 8)
    @test C([F(8), F(19), F(1)]) in P && C([F(8), F(18), F(1)]) in P

    @test C([F(8), F(19), F(1)]) == C([F(8)*5, F(19)*5^3, F(1)*5])

    P1 = C([F(8), F(19), F(1)])
    P2 = C([F(8), F(19), F(1)])
    P3 = C([F(8), F(18), F(1)])
    @test P1 == P2
    @test P1 != P3
    @test hash(P1) == hash(P2)



  end
  @testset "Reduction" begin
    Qx, x = polynomial_ring(QQ, "x")
    f = 19*x^8 - 262*x^7 + 1507*x^6 - 4784*x^5 + 9202*x^4 -10962*x^3 + 7844*x^2 - 3040*x +475
    f_red = -x^8 - 2*x^7 + 7*x^6 + 16*x^5 + 2*x^4 - 2*x^3 + 4*x^2 - 5
    g = @inferred reduce_binary_form(f)
    @test f_red == g

    Qst, (s,t) = polynomial_ring(QQ, ["s", "t"])
    f = s^6 + 30*s^5*t + 371*s^4*t^2 + 2422*s^3*t^3 + 8813*s^2*t^4 + 16968*s*t^5+ 13524*t^6
    f_red = s^6 + 6*s^5*t + 11*s^4*t^2 + 6*s^3*t^3 + 5*s^2*t^4 + 4*t^6
    g, gamma = @inferred reduce_binary_form(f)
    @test f_red == g

    w = gamma * [s,t]
    @test f(w[1],w[2]) == g

    f = f * (s + 3*t)
    g, gamma2 = @inferred reduce_binary_form(f)
    @test gamma == gamma2

  end

end
