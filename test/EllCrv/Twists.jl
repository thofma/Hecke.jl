@testset "Twists of elliptic curves" begin
  K = GF(2,2)
  a = gen(K)
  E = elliptic_curve_from_j_invariant(K(0))
  L = @inferred twists(E)
  twistlist = [EllipticCurve(K, [0, 0, 1, 0, 0 ]),
               EllipticCurve(K, [0, 0, 1, a, 0 ]),
               EllipticCurve(K, [0, 0, 1, 0, a ]),
               EllipticCurve(K, [0, 0, a, 0, 0 ]),
               EllipticCurve(K, [0, 0, a^2, 0, 0 ]),
               EllipticCurve(K, [0, 0, a, 0, 1 ]),
               EllipticCurve(K, [0, 0, a^2, 0, a^2])]
  @test L == twistlist
  for tw in L
    @test @inferred is_twist(E, tw)
  end
  
  E = elliptic_curve_from_j_invariant(K(a+1))
  F = @inferred quadratic_twist(E)
  @test is_twist(E, F)
  
  K = GF(3,2)
  a = gen(K)
  E = elliptic_curve_from_j_invariant(K(0))
  L = @inferred twists(E)
  
  twistlist = [EllipticCurve(K, [ 0, 0, 0, 2, 0 ]),
               EllipticCurve(K, [ 0, 0, 0, a^5, 0 ]),
               EllipticCurve(K, [ 0, 0, 0, a^6, 0 ]),
               EllipticCurve(K, [ 0, 0, 0, a^7, 0 ]),
               EllipticCurve(K, [ 0, 0, 0, 2, 1 ]),
               EllipticCurve(K, [ 0, 0, 0, a^6, a^3 ])]
  @test L == twistlist
  
  E = elliptic_curve_from_j_invariant(K(a+1))
  F = @inferred quadratic_twist(E)
  @test is_twist(E, F)
  
  K = GF(7,2)
  a = gen(K)
  E = elliptic_curve_from_j_invariant(K(0))
  L = @inferred twists(E)
  
  twistlist = [EllipticCurve(K, [ 0, 0, 0, 0, 2 ]),
               EllipticCurve(K, [ 0, 0, 0, 0, a^17 ]),
               EllipticCurve(K, [ 0, 0, 0, 0, a^18 ]),
               EllipticCurve(K, [ 0, 0, 0, 0, a^19 ]),
               EllipticCurve(K, [ 0, 0, 0, 0, a^20 ]),
               EllipticCurve(K, [ 0, 0, 0, 0, a^21 ])]
  @test L == twistlist
  

  E = elliptic_curve_from_j_invariant(K(1728))
  L = @inferred twists(E)
  
  twistlist = [EllipticCurve(K, [ 0, 0, 0, 1, 0]),
               EllipticCurve(K, [ 0, 0, 0, a, 0]),
               EllipticCurve(K, [ 0, 0, 0, a^2,0]),
               EllipticCurve(K, [ 0, 0, 0, a^3, 0])]
  @test L == twistlist
  
  E = EllipticCurve([1,2,3,4,5])
  F = @inferred quadratic_twist(E, 5)
  @test !is_isomorphic(E, F)
  @test is_twist(E, F)
  
  
end

