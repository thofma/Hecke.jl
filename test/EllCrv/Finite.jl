#using Random
#using RandomExtensions
#
#const rng = MersenneTwister()
#const rand_seed = rand(UInt128)

@testset "Elliptic curves over finite fields" begin

  R1 = GF(23)
  R2, a2 = FlintFiniteField(23, 1, "a")
  R3, a3 = FlintFiniteField(ZZRingElem(23), 1, "a")
  R4, a4 = FlintFiniteField(23, 2, "a")

  E1 = EllipticCurve(R1, [2, 3])
  E2 = EllipticCurve(R2, [2, 3])
  E3 = EllipticCurve(R3, [2, 3])
  E4 = EllipticCurve(R4, [2, 3])
  E5 = EllipticCurve(R4, [1, 2, 3, 0, 6])

  @testset "Random point construction" begin
    @inferred rand(E1)
    @inferred rand(E2)
    @inferred rand(E3)
    @inferred rand(E4)
    @inferred rand(E5)

    T = EllCrvPt{fpFieldElem}
    @test rand(rng, E1) isa T
    @test rand(rng, E1, 3) isa Vector{T}

    Random.seed!(rng, rand_seed)
    a = rand(rng, E1)
    Random.seed!(rng, rand_seed)
    @test a == rand(rng, E1)
  end

  @testset "Order computation (Exhaustive_search)" begin
    @test 24 == @inferred order_via_exhaustive_search(E1)
  end


  @testset "Order computation (Legendre)" begin
    @test 24 == @inferred order_via_legendre(E1)
  end

  @testset "Order computation (BSGS)" begin
    @test 24 in @inferred order_via_bsgs(E1)
    @test 24 in @inferred order_via_bsgs(E2)
    @test 24 in @inferred order_via_bsgs(E3)
    @test 576 in @inferred order_via_bsgs(E4)
  end

  @testset "Hasse interval" begin
    l = @inferred hasse_interval(E1)
    @test l[1] <= 24 && 24 <= l[2]
    l = @inferred hasse_interval(E2)
    @test l[1] <= 24 && 24 <= l[2]
    l = @inferred hasse_interval(E3)
    @test l[1] <= 24 && 24 <= l[2]
    l = @inferred hasse_interval(E4)
    @test l[1] <= 576 && 576 <= l[2]
  end

  @testset "Trace of Frobenius" begin
   E = EllipticCurve(GF(7,2), [1, 2, 3, 4, 5])
   @test -13 == @inferred trace_of_frobenius(E)
   @test 71 == @inferred trace_of_frobenius(E,2)
   @test -286 == @inferred trace_of_frobenius(E,3)
   E = elliptic_curve_from_j_invariant(GF(2, 4)(0))
   @test trace_of_frobenius(E, 2) == 32
   @test trace_of_frobenius(E, 3) == 128
   
   R,x = polynomial_ring(GF(59))
   E = EllipticCurve(x^3+54*x+31,x)
   @test trace_of_frobenius(E) == 15
  end

  @testset "Schoofs algorithm" begin
    @test 24 == @inferred order_via_schoof(E1)
    @test 24 == @inferred order_via_schoof(E2)
    @test 24 == @inferred order_via_schoof(E3)
    @test 576 == @inferred order_via_schoof(E4)
  end

  @testset "Point counting" begin
    RR = GF(2)
    E = EllipticCurve(RR,[1, 1, 0, 0, 1])
    @test 2 == @inferred order(E)
    RR = GF(3)
    E = EllipticCurve(RR, [1, 1])
    @test 4 == @inferred order(E)

    RR = GF(3,6)
    E = EllipticCurve(RR, [1,2,0,1,1])
    @test 784 == @inferred order(E)

    @test 24 == @inferred order(E1)
    @test 24 == @inferred order(E2)
    @test 24 == @inferred order(E3)
    @test 576 == @inferred order(E4)
  end
  
  @testset "Supersingular" begin 
    g = @inferred supersingular_polynomial(2)
    R = parent(g)
    J = gen(R)
    g == J
  
    g = @inferred supersingular_polynomial(193)
    R = parent(g)
    J = gen(R)
    f = J^16 + 60*J^15 + 22*J^14 + 101*J^13 + 126*J^12 + 173*J^11 + 72*J^10 + 49*J^9 + 132*J^8 + 44*J^7 + 124*J^6 + 141*J^5 + 108*J^4 + 15*J^3 + 26*J^2 + 48*J + 23
    @test g == f
    
    for K in [GF(193), GF(ZZ(193)), GF(193, 1),
              GF(193, 1), GF(ZZ(193), 1), GF(193, 4), GF(ZZ(193), 3),
              GF(193, 3), GF(ZZ(193), 3)]

      E = elliptic_curve_from_j_invariant(K(169))
      @test @inferred is_supersingular(E) == true
      @inferred is_probable_supersingular(E)
      
      E = elliptic_curve_from_j_invariant(K(170))
      @test @inferred is_ordinary(E) == true
    end
    
    K = GF(193, 3)
    a = gen(K)
    E = elliptic_curve_from_j_invariant(a)
    @test @inferred is_supersingular(E) == false
    @inferred is_probable_supersingular(E)
  end
  
end
