@testset "Torsion points" begin


  E43_a1 = @inferred elliptic_curve([0, 1, 1, 0, 0])

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

  Rx, x = polynomial_ring(QQ, "x")
  K1, a = number_field(x^2 - x - 1)
  K2, a = number_field(x^2 +2)
  K3, a = number_field(x^2+1)
  K4, a = cyclotomic_field(15)


  curves_to_test_tor_struc_nf =
   [(map(K1, [1, 1, 1, -3, 1]), [15]),
    (map(K2, [1, 0, 0, 115, 561]), [10, 2]),
    (map(K3, [1, 1, 1, -10, -10]), [4, 4]),
    (map(K4, [1, 1, 1, -5, 2]), [16, 2])
   ]



  @testset "Point order computation" begin
    E = elliptic_curve([0, -1, 1, -7820, -263580])
    @test 1 == @inferred order(infinity(E))

    E = elliptic_curve([1, 0, 1, -2731, -55146])
    @test 2 == @inferred order(E([QQFieldElem(-121, 4), QQFieldElem(117, 8)]))

    E = elliptic_curve([0, 1, 1, -9, -15])
    @test 3 == @inferred order(E([5, 9]))

    E = elliptic_curve([1, 1, 1, -80, 242])
    @test 4 == @inferred order(E([5, -2]))

    E = elliptic_curve([0, -1, 1, -10, -20])
    @test 5 == @inferred order(E([5, 5]))

    E = elliptic_curve([1, 0, 1, -36, -70])
    @test 6 == @inferred order(E([-4, 5]))

    E = elliptic_curve([1, -1, 1, -3, 3])
    @test 7 == @inferred order(E([1, 0]))

    E = elliptic_curve([1, 1, 1, 35, -28])
    @test 8 == @inferred order(E([2, 6]))

    E = elliptic_curve([1, -1, 1, -14, 29])
    @test 9 == @inferred order(E([-3, 7]))

    E = elliptic_curve([1, 0, 0, -45, 81])
    @test 10 == @inferred order(E([0, 9]))

    E = elliptic_curve([1, -1, 1, -122, 1721])
    @test 12 == @inferred order(E([-9, 49]))
  end

  @testset "Torsion test" begin
    E = elliptic_curve([1, -1, 1, -19353, 958713])
    @test @inferred is_torsion_point(E([103,172]))
    @test @inferred !is_torsion_point(E([-121,1292]))
  end

  @testset "Torsion points (Lutz-Nagell)" begin
    for c in curves_to_test_tor_short
      E = elliptic_curve(c[1])
      T = @inferred torsion_points_lutz_nagell(E)
      @test c[2] == length(T)
    end
  end

  @testset "Torsion points (division polynomials" begin
    for c in curves_to_test_tor_short
      E = elliptic_curve(c[1])
      T = @inferred torsion_points_division_poly(E)
      @test c[2] == length(T)
    end

    for c in curves_to_test_tor_struc
      E = elliptic_curve(c[1])
      T = @inferred torsion_points_division_poly(E)
      @test prod(c[2]) == length(T)
    end
  end

  @testset "Torsion points" begin
    for c in curves_to_test_tor_short
      E = elliptic_curve(c[1])
      T = @inferred torsion_points(E)
      @test c[2] == length(T)
      # test the caching
      T = @inferred torsion_points(E)
      @test c[2] == length(T)
    end

    for c in curves_to_test_tor_struc
      E = elliptic_curve(c[1])
      T = @inferred torsion_points(E)
      @test prod(c[2]) == length(T)
      # test the caching
      T = @inferred torsion_points(E)
      @test prod(c[2]) == length(T)
    end
  end

  @testset "Torsion point structure" begin
    for c in curves_to_test_tor_struc
      E = elliptic_curve(c[1])
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


  @testset "Torsion point structure number fields" begin
    for c in curves_to_test_tor_struc_nf
      E = elliptic_curve(c[1])
      T = @inferred torsion_structure(E)
      @test T[1] == c[2]
      P = T[2][1]
      @test is_torsion_point(P)
      @test order(P) == T[1][1]
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

  @testset "Division polynomial" begin

    Kx, x = polynomial_ring(base_field(E43_a1), "x")
    Kxy, y = polynomial_ring(Kx, "y")
    f = @inferred division_polynomial(E43_a1, 4, x, y)
    @test  f == (4*x^6 + 8*x^5 + 20*x^3 + 20*x^2 + 8*x - 2)*y + 2*x^6 + 4*x^5 + 10*x^3 + 10*x^2 + 4*x - 1

  end
end
