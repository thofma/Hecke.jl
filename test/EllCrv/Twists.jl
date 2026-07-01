@testset "Twists of elliptic curves" begin
  function test_twist_deg1(E::EllipticCurve{T}, d::T) where T <: FieldElem
    F = @inferred quadratic_twist(E, d)
    @test is_isomorphic(E, F)
    @test is_twist(E, F)
  end

  function test_twist_deg2(E::EllipticCurve{T}, d::T) where T <: FieldElem
    F = @inferred quadratic_twist(E, d)
    @test !is_isomorphic(E, F)
    @test is_twist(E, F)
  end

  function test_unique_twist(E::EllipticCurve{T}) where T <: FieldElem
    F = @inferred quadratic_twist(E)
    @test !is_isomorphic(E, F)
    @test is_twist(E, F)
  end

  K, a = finite_field(2, 2; cached = false)

  E = elliptic_curve_from_j_invariant(zero(K))
  L = @inferred twists(E)
  twistlist = [elliptic_curve(K, [0, 0, 1, 0, 0 ]),
               elliptic_curve(K, [0, 0, 1, a, 0 ]),
               elliptic_curve(K, [0, 0, 1, 0, a ]),
               elliptic_curve(K, [0, 0, a, 0, 0 ]),
               elliptic_curve(K, [0, 0, a^2, 0, 0 ]),
               elliptic_curve(K, [0, 0, a, 0, 1 ]),
               elliptic_curve(K, [0, 0, a^2, 0, a^2])]
  @test L == twistlist
  for tw in L
    @test @inferred is_twist(E, tw)
  end
  @test 1 == count(F -> is_isomorphic(E, F), L)

  test_unique_twist(E)
  test_twist_deg1(E, one(K))  # Tr(1) = 0, so the twist has degree 1
  test_twist_deg2(E, a)       # Tr(a) = 1, so the twist has degree 2

  E = elliptic_curve_from_j_invariant(a+1)
  test_unique_twist(E)
  test_twist_deg1(E, one(K))  # Tr(1) = 0, so the twist has degree 1
  test_twist_deg2(E, a)       # Tr(a) = 1, so the twist has degree 2

  E = elliptic_curve(K, [1, 0, 1, 0, 1])
  test_unique_twist(E)
  test_twist_deg1(E, one(K))  # Tr(1) = 0, so the twist has degree 1
  test_twist_deg2(E, a)       # Tr(a) = 1, so the twist has degree 2

  K, a = finite_field(3, 2; cached = false)

  E = elliptic_curve_from_j_invariant(zero(K))
  L = @inferred twists(E)
  twistlist = [elliptic_curve(K, [ 0, 0, 0, 2, 0 ]),
               elliptic_curve(K, [ 0, 0, 0, a^5, 0 ]),
               elliptic_curve(K, [ 0, 0, 0, a^6, 0 ]),
               elliptic_curve(K, [ 0, 0, 0, a^7, 0 ]),
               elliptic_curve(K, [ 0, 0, 0, 2, 1 ]),
               elliptic_curve(K, [ 0, 0, 0, a^6, a^3 ])]
  @test L == twistlist
  for tw in L
    @test @inferred is_twist(E, tw)
  end
  @test 1 == count(F -> is_isomorphic(E, F), L)

  test_unique_twist(E)
  test_twist_deg1(E, one(K))  # 1 is square, so the twist has degree 1
  test_twist_deg2(E, a)       # a is not a square, so the twist has degree 2

  E = elliptic_curve_from_j_invariant(a+1)
  test_unique_twist(E)
  test_twist_deg1(E, one(K))  # 1 is square, so the twist has degree 1
  test_twist_deg2(E, a)       # a is not a square, so the twist has degree 2

  K, a = finite_field(7, 2; cached = false)

  E = elliptic_curve_from_j_invariant(K(0))
  L = @inferred twists(E)
  twistlist = [elliptic_curve(K, [ 0, 0, 0, 0, 2 ]),
               elliptic_curve(K, [ 0, 0, 0, 0, a^17 ]),
               elliptic_curve(K, [ 0, 0, 0, 0, a^18 ]),
               elliptic_curve(K, [ 0, 0, 0, 0, a^19 ]),
               elliptic_curve(K, [ 0, 0, 0, 0, a^20 ]),
               elliptic_curve(K, [ 0, 0, 0, 0, a^21 ])]
  @test L == twistlist
  for tw in L
    @test @inferred is_twist(E, tw)
  end
  @test 1 == count(F -> is_isomorphic(E, F), L)

  E = elliptic_curve_from_j_invariant(K(1728))
  L = @inferred twists(E)
  twistlist = [elliptic_curve(K, [ 0, 0, 0, 1, 0]),
               elliptic_curve(K, [ 0, 0, 0, a, 0]),
               elliptic_curve(K, [ 0, 0, 0, a^2,0]),
               elliptic_curve(K, [ 0, 0, 0, a^3, 0])]
  @test L == twistlist
  for tw in L
    @test @inferred is_twist(E, tw)
  end
  @test 1 == count(F -> is_isomorphic(E, F), L)

  E = elliptic_curve([1,2,3,4,5])
  test_twist_deg1(E, QQFieldElem(4))
  test_twist_deg2(E, QQFieldElem(5))

  for K in [GF(13), GF(13, 1), GF(ZZRingElem(13)), GF(ZZRingElem(13), 1)]
    E = elliptic_curve_from_j_invariant(K(0))
    test_unique_twist(E)
  end

  for K in [GF(2, 3), GF(ZZRingElem(2), 3)]
    E = elliptic_curve_from_j_invariant(K(1))
    test_unique_twist(E)
  end
end
