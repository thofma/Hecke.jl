@testset "Generic hyperelliptic curve" begin

  @testset "Constructors" begin
    Qx, x = polynomial_ring(QQ, "x")
   
    
    f1 = x^6+3*x+5
    h1 = x+2
    C = @inferred HyperellipticCurve(f1, h1)
    @test C == HyperellipticCurve(f1, h1)
    @test hash(C) == hash(HyperellipticCurve(f1, h1))
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
    C = @inferred HyperellipticCurve(f1)
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
    C = @inferred HyperellipticCurve(f)
    P = @inferred points_with_x_coordinate(C, 1)
    @test C([1, -3, 1]) in P && C([1, 3, 1]) in P
  
    @test C([-5*20, 125*20^3 , 3*20]) == C([-5, 125, 3])
    infpoints = @inferred points_at_infinity(C)
    @test C([1, 1, 0]) in infpoints && C([1,-1,0]) in infpoints
    @test @inferred is_infinite(infpoints[1]) 
    
    F = GF(37)
    Fx, x = polynomial_ring(F, "x")
   
    f = x^6+3*x+5
    C = @inferred HyperellipticCurve(f)
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
end
