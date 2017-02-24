@testset "Rational elliptic curves" begin

  curves_to_test_tor_short = [
  ([1, 2], 4),
  ([2, 3], 2),
  ([0, 1], 6),
  ([1, 0], 2),
  ([1, 1], 1)
  ]

  curves_to_test_tor_struc =
  [
  ([0, -1, 1, -7820, -263580], [1]),
  ([1, 0, 1, -2731, -55146], [2]),
  ([0, 1, 1, -9, -15], [3]),
  ([1, 1, 1, -80, 242], [4]),
  ([0, -1, 1, -10, -20], [5]),
  ([1, 0, 1, -36, -70], [6]),
  ([1, -1, 1, -3, 3], [7]),
  ([1, 1, 1, 35, -28], [8]),
  ([1, -1, 1, -14, 29], [9]),
  ([1, 0, 0, -45, 81], [10]),
  ([1, -1, 1, -122, 1721], [12]),
  ([1, 1, 1, -135, -660], [2, 2]),
  ([1, 1, 1, -10, -10], [2, 4]),
  ([1, 0, 1, -19, 26], [2, 6]),
  ([1, 0, 0, -1070, 7812], [2, 8]),
  ]

  @testset "Point order computation" begin
    E = EllipticCurve([0, -1, 1, -7820, -263580])
    @test 1 == @inferred order(infinity(E))

    E = EllipticCurve([1, 0, 1, -2731, -55146])
    @test 2 == @inferred order(E([fmpq(-121, 4), fmpq(117, 8)]))

    E = EllipticCurve([0, 1, 1, -9, -15])
    @test 3 == @inferred order(E([5, 9]))

    E = EllipticCurve([1, 1, 1, -80, 242])
    @test 4 == @inferred order(E([5, -2]))

    E = EllipticCurve([0, -1, 1, -10, -20])
    @test 5 == @inferred order(E([5, 5]))

    E = EllipticCurve([1, 0, 1, -36, -70])
    @test 6 == @inferred order(E([-4, 5]))

    E = EllipticCurve([1, -1, 1, -3, 3])
    @test 7 == @inferred order(E([1, 0]))

    E = EllipticCurve([1, 1, 1, 35, -28])
    @test 8 == @inferred order(E([2, 6]))

    E = EllipticCurve([1, -1, 1, -14, 29])
    @test 9 == @inferred order(E([-3, 7]))

    E = EllipticCurve([1, 0, 0, -45, 81])
    @test 10 == @inferred order(E([0, 9]))

    E = EllipticCurve([1, -1, 1, -122, 1721])
    @test 12 == @inferred order(E([-9, 49]))
  end

  @testset "Torsion test" begin
    E = EllipticCurve([1, -1, 1, -19353, 958713])
    @test @inferred istorsion_point(E([103,172]))
    @test @inferred !istorsion_point(E([-121,1292]))
  end

  @testset "Torsion points (Lutz-Nagell)" begin
    for c in curves_to_test_tor_short
      E = EllipticCurve(c[1])
      T = @inferred torsion_points_lutz_nagell(E)
      @test c[2] == length(T)
    end
  end

  @testset "Torsion points (division polynomials" begin
    for c in curves_to_test_tor_short
      E = EllipticCurve(c[1])
      T = @inferred torsion_points_division_poly(E)
      @test c[2] == length(T)
    end

    for c in curves_to_test_tor_struc
      E = EllipticCurve(c[1])
      T = @inferred torsion_points_division_poly(E)
      @test prod(c[2]) == length(T)
    end
  end

  @testset "Torsion points" begin
    for c in curves_to_test_tor_short
      E = EllipticCurve(c[1])
      T = @inferred torsion_points(E)
      @test c[2] == length(T)
      # test the caching
      T = @inferred torsion_points(E)
      @test c[2] == length(T)
    end

    for c in curves_to_test_tor_struc
      E = EllipticCurve(c[1])
      T = @inferred torsion_points(E)
      @test prod(c[2]) == length(T)
      # test the caching
      T = @inferred torsion_points(E)
      @test prod(c[2]) == length(T)
    end
  end

  @testset "Torsion point structure" begin
    for c in curves_to_test_tor_struc
      E = EllipticCurve(c[1])
      T = @inferred torsion_structure(E)
      @test T[1] == c[2]
      @test order(T[2][1]) == T[1][1]
      if length(T[1]) == 2
        @test order(T[2][2]) == T[1][2]
      end
      # test the caching
      T = @inferred torsion_structure(E)
      @test T[1] == c[2]
      @test order(T[2][1]) == T[1][1]
      if length(T[1]) == 2
        @test order(T[2][2]) == T[1][2]
      end
    end
  end

  @testset "Minimal model (Laska-Kraus-Connell" begin
    E = EllipticCurve([1,2,3,4,5])
    EE = @inferred laska_kraus_connell(E)
    @test EE.coeff == [1, -1, 0, 4, 3]

    E = EllipticCurve([625, -15625, 19531250, -2929687500, -34332275390625])
    EE = @inferred laska_kraus_connell(E)
    @test EE.coeff == [1, -1, 0, 4, 3]
  end

  @testset "Tates algorithm" begin
    E = EllipticCurve([625, -15625, 19531250, -2929687500, -34332275390625])
    EE = @inferred tates_algorithm_global(E)
    @test EE.coeff == [1, -1, 0, 4, 3]

    E = EllipticCurve([1,2,3,4,5])
    EE = @inferred tates_algorithm_global(E)
    @test EE.coeff == [1, -1, 0, 4, 3]

    #  25350.a1
    E = EllipticCurve([1, 1, 0, 40050, 7557750])
    Ep, K, f, c = tates_algorithm_local(E, 2)
    @test tidy_model(Ep).coeff == E.coeff
    @test K == "I1"
    @test f == 1
    @test c == 1

    Ep, K, f, c = tates_algorithm_local(E, 3)
    @test tidy_model(Ep).coeff == E.coeff
    @test K == "I2"
    @test f == 1
    @test c == 2

    Ep, K, f, c = tates_algorithm_local(E, 5)
    @test tidy_model(Ep).coeff == E.coeff
    @test K == "III*"
    @test f == 2
    @test c == 2

    Ep, K, f, c = tates_algorithm_local(E, 13)
    @test tidy_model(Ep).coeff == E.coeff
    @test K == "IV*"
    @test f == 2
    @test c == 1

    # 150.a1
    E = EllipticCurve([1, 1, 0, -20700, 1134000])
    Ep, K, f, c = tates_algorithm_local(E, 2)
    @test tidy_model(Ep).coeff == E.coeff
    @test K == "I5"
    @test f == 1
    @test c == 1

    Ep, K, f, c = tates_algorithm_local(E, 3)
    @test tidy_model(Ep).coeff == E.coeff
    @test K == "I10"
    @test f == 1
    @test c == 2

    Ep, K, f, c = tates_algorithm_local(E, 5)
    @test tidy_model(Ep).coeff == E.coeff
    @test K == "III*"
    @test f == 2
    @test c == 2
  end
end
