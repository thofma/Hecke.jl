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

  @testset "quadratic_twist in characteristic 2: different base field types" begin
    k, _ = finite_field(2, 2, :a; cached = false)
    kx, x = polynomial_ring(k, :x; cached = false)
    for K in [finite_field(2, 4, :a; cached = false)[1],
              finite_field(ZZ(2), 4, :a; cached = false)[1],
              Native.finite_field(2, 4, :a; cached = false)[1],
              Native.finite_field(ZZ(2), 4, :a; cached = false)[1],
              GF(2, 4; cached = false),
              GF(ZZ(2), 4; cached = false),
              Native.GF(2, 4; cached = false),
              Native.GF(ZZ(2), 4; cached = false),
              finite_field(x^3 + x + 1, :b; cached = false)[1]]   # relative of absolute degree 6
      E = elliptic_curve(K, [1, 0, 0, 0, gen(K)])
      @test order(E) + order(quadratic_twist(E)) == 2*order(K) + 2
      test_unique_twist(E)
    end
  end

  @testset "twists: one curve per isomorphism class, the same every call" begin
    # n is the number of classes over K of curves with the j-invariant of E,
    # |H^1(G, Aut(E))| (Silverman, AEC, X.5.3): for p >= 5, |K^*/(K^*)^m| =
    # gcd(m, |K| - 1) with m = 2, 4, 6 for j generic, 1728, 0 (X.5.4); 2 for
    # j != 0 in characteristic 2 and 3; for j = 0 there, the classes of
    # Aut(E), of order 24 (12) (A.1.2, Exercise A.1), under conjugation
    # twisted by Frobenius: 3 (4) in odd absolute degree, and 7 (6), the
    # conjugacy classes, in even degree, where Frobenius acts trivially.
    function test_twists(E, n)
      T = @inferred twists(E)
      @test length(T) == n
      @test all(F -> base_field(F) === base_field(E), T)
      @test all(F -> j_invariant(F) == j_invariant(E), T)
      @test all(!is_isomorphic(T[i], T[k]) for i in eachindex(T) for k in 1:i-1)
      @test a_invariants.(twists(E)) == a_invariants.(T)
      @test a_invariants(quadratic_twist(E)) == a_invariants(quadratic_twist(E))
    end
    generic_j(K) = first(a for a in K if !iszero(a) && a != K(1728))

    # prime fields, where gen(K) is 0 or 1
    for K in [GF(5), GF(7), GF(13), GF(ZZ(13)), Native.GF(13),
              Native.GF(ZZ(13))]
      q = order(K)
      test_twists(elliptic_curve_from_j_invariant(K(0)), gcd(6, q - 1))
      test_twists(elliptic_curve_from_j_invariant(K(1728)), gcd(4, q - 1))
      test_twists(elliptic_curve_from_j_invariant(generic_j(K)), 2)
    end

    # defining polynomials that are not primitive: gen(K) is a power
    R7, t = polynomial_ring(GF(7), :t; cached = false)
    K, = finite_field(t^2 + 1, :i; cached = false)
    test_twists(elliptic_curve_from_j_invariant(K(0)), 6)
    test_twists(elliptic_curve_from_j_invariant(K(1728)), 4)
    test_twists(elliptic_curve_from_j_invariant(generic_j(K)), 2)
    R3, t = polynomial_ring(GF(3), :t; cached = false)
    K, = finite_field(t^2 + 1, :i; cached = false)
    test_twists(elliptic_curve_from_j_invariant(K(0)), 6)
    R2, t = polynomial_ring(GF(2), :t; cached = false)
    K, = finite_field(t^4 + t^3 + t^2 + t + 1, :t; cached = false)
    test_twists(elliptic_curve_from_j_invariant(K(0)), 7)

    # characteristic 2 and 3, odd and even degree
    for (K, n) in [(GF(2, 3), 3), (GF(2, 4), 7), (GF(3, 3), 4), (GF(3, 2), 6)]
      test_twists(elliptic_curve_from_j_invariant(K(0)), n)
      test_twists(elliptic_curve_from_j_invariant(generic_j(K)), 2)
    end

    # relative extensions of odd relative and even absolute degree
    k, = finite_field(2, 2, :a; cached = false)
    kx, x = polynomial_ring(k, :x; cached = false)
    K, = finite_field(x^3 + x + 1, :b; cached = false)
    test_twists(elliptic_curve_from_j_invariant(K(0)), 7)
    test_twists(elliptic_curve_from_j_invariant(generic_j(K)), 2)
    k, = finite_field(3, 2, :a; cached = false)
    kx, x = polynomial_ring(k, :x; cached = false)
    K, = finite_field(x^3 - x - 1, :b; cached = false)
    test_twists(elliptic_curve_from_j_invariant(K(0)), 6)
    test_twists(elliptic_curve_from_j_invariant(generic_j(K)), 2)

    # gen(K) + k is a power for every k: the elements come from absolute_basis
    R3, t = polynomial_ring(GF(3), :t; cached = false)
    K, = finite_field(t^3 + 2t + 2, :a; cached = false)
    @test all(k -> is_square(gen(K) + k), 0:2)
    @test !is_square(Hecke._twisting_element(K, 2))
    test_twists(elliptic_curve_from_j_invariant(K(1)), 2)
    R2, t = polynomial_ring(GF(2), :t; cached = false)
    K, = finite_field(t^8 + t^6 + t^5 + t^4 + t^3 + t + 1, :a; cached = false)
    @test all(k -> isone((gen(K) + k)^85), 0:1)
    @test !isone(Hecke._twisting_element(K, 3)^85)
    test_twists(elliptic_curve_from_j_invariant(K(0)), 7)

    # the elements depend only on the defining polynomial, not on the type of
    # the field or its iteration order
    coordinates(a) = [lift(ZZ, c) for c in absolute_coordinates(a)]
    for (p, f) in [(3, [2, 2, 0, 1]), (7, [1, 0, 1]), (2, [1, 1, 0, 1, 1, 1, 1, 0, 1])]
      Fy, y = polynomial_ring(GF(p), :y; cached = false)
      Fny, yn = polynomial_ring(Native.GF(p), :y; cached = false)
      K1, = finite_field(Fy(f), :a; cached = false)
      K2, = Native.finite_field(Fny(f), "a"; cached = false)
      for n in [2, 3, 4, 6]
        divides(order(K1) - 1, ZZ(n))[1] || continue
        @test coordinates(Hecke._twisting_element(K1, n)) ==
              coordinates(Hecke._twisting_element(K2, n))
      end
      @test coordinates(Hecke._nonzero_trace_element(K1)) ==
            coordinates(Hecke._nonzero_trace_element(K2))
    end
  end
end
