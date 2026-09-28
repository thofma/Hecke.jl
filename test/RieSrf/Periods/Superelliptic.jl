@testset "Superelliptic" begin
  @testset "Superelliptic families" begin
    for (m, n) in [(3, 4), (3, 5), (4, 5)]
      for (name, f) in superelliptic_family(m, n)
        @testset "$name" begin
          test_sanity(_rs(f, 100))
        end
      end
    end
  end

  @testset "Superelliptic algorithm (Molin–Neurohr)" begin
    Qt, t = polynomial_ring(QQ, :t)
    # (name, curve, compare with the general algorithm via Hom(J1, J2))
    cases = [
      ("y^2 = quintic",        y^2 - (x^5 + x^4 + x^3 - x + 4),          true),   # g = 2
      ("y^2 = sextic",         y^2 - (x^6 - 3*x^4 + x + 2),              true),   # g = 2, two points at infinity
      ("y^3 = quartic",        y^3 - (x^4 + 2*x + 1),                    true),   # g = 3
      ("y^3 = quintic",        y^3 - (x^5 - x + 1),                      true),   # g = 4
      ("y^4 = cubic",          y^4 - (x^3 + x + 1),                      true),   # g = 3
      ("y^4 = sextic",         y^4 - (x^6 + x^2 + 2*x - 1),              false),  # g = 7, gcd(m, n) = 2
      ("y^5 = quartic",        y^5 - (x^4 + 1),                          false),  # g = 6
      ("swapped: x^3 = ...",   x^3 - (y^4 + 2*y + 1),                    true),   # g = 3
      ("leading coefficient", -3*y^2 + 2*x^5 - x + 7,                    true),   # g = 2
    ]
    for (name, f, compare) in cases
      @testset "$name" begin
        RSs = _rs(f, 200; model = :superelliptic)
        C = RSM.computational_model(RSs)
        @test C isa RSM.SuperellipticModel
        RSg = _rs(f, 200; model = :original)
        @test RSM.genus(RSs) == RSM.genus(RSg)
        tau = RSM.small_period_matrix(RSs)
        @test _is_symmetric(tau)
        @test _is_positive_definite(imag(tau))
        if compare
          @test _jacobians_isomorphic(RSM.big_period_matrix(RSs), RSM.big_period_matrix(RSg))
        end
      end
    end

    @testset "precision retry and accuracy" begin
      f = y^3 - (x^5 - x + 1)
      for acc in (:small, :big, :both)
        RS = _rs(f, 150; model = :superelliptic, accuracy = acc)
        C = RSM.computational_model(RS)
        P = RSM.big_period_matrix(RS)
        @test C.precision_retries in (0, 1)
        acc === :small || @test RSM._claimed_bits(P) >= 150
        acc === :big || @test RSM._claimed_bits(RSM.small_period_matrix(RS)) >= 150
      end
      # a forced retry (min_target_precision set in advance) gives the same periods
      RS1 = _rs(f, 150; model = :superelliptic)
      RS2 = _rs(f, 150; model = :superelliptic, precision_retry = false)
      C2 = RSM.computational_model(RS2)
      C2.min_target_precision = 400
      @test RSM.computational_model(RS1) isa RSM.SuperellipticModel
      @test all(overlaps(a, b) for (a, b) in zip(collect(RSM.big_period_matrix(RS1)), collect(RSM.big_period_matrix(RS2))))
      @test C2.target_precision == 400
    end

    @testset "Abel–Jacobi map: $name" for (name, f) in [
        ("y^2 = quintic", y^2 - (x^5 + x^4 + x^3 - x + 4)),     # one point at infinity
        ("y^2 = sextic",  y^2 - (x^6 - 3*x^4 + x + 2)),         # two
        ("y^3 = quartic", y^3 - (x^4 + 2*x + 1)),
        ("y^4 = sextic",  y^4 - (x^6 + x^2 + 2*x - 1)),          # two
        ("swapped",       x^3 - (y^4 + 2*y + 1))]
      RS = _rs(f, 128; superelliptic = true)
      C = RSM.computational_model(RS)
      @test C isa RSM.SuperellipticModel
      RSM.big_period_matrix(RS)
      # div((x - x1)/(x - x2)) and div((y - y1)/(y - y2)): generic finite points
      test_abel_jacobi_principal(RS; ntests = 1)
      # divisors with the branch points and the points at infinity:
      # div(y) = sum_i P_i - (n/delta) D_inf, div(x - x_1) = m P_1 - (m/delta) D_inf
      # (in the coordinates of the superelliptic model)
      CC = RSM.complex_field(RS)
      tol = ArbField(precision(CC))(2)^(-div(precision(RS), 2))
      swapped = !isone(C.transform)
      point(z) = swapped ? RS([zero(CC), CC(z)]) : RS([CC(z), zero(CC)])
      Ps = [point(z) for z in C.branch_points]
      Infs = RSM.infinite_points(RS)
      delta = gcd(C.m, C.n)
      @test length(Infs) == delta
      D1 = RSM.divisor(vcat(Ps, Infs), vcat(fill(1, C.n), fill(-div(C.n, delta), delta)))
      D2 = RSM.divisor(vcat([Ps[2]], Infs), vcat([C.m], fill(-div(C.m, delta), delta)))
      for D in (D1, D2)
        @test all(_is_small(v, tol) for v in RSM.abel_jacobi_map(D, "swap", "complex"))
      end
      # the base point is a branch point: m (P0 - P0) = 0 and AJ(P0) = 0
      P0 = RSM.base_point(RS)
      @test all(_is_small(v, tol) for v in RSM.abel_jacobi_map(RSM.divisor([P0], [1]), "swap", "none"))
      # the points were created by the superelliptic model: no fundamental
      # group / monodromy of the general code was computed
      @test !isdefined(RSM.original_model(RS), :fundamental_group_of_P1)
      @test length(RSM.ramification_points(RS)) == C.n + (delta < C.m ? delta : 0)
    end

    # A single point at infinity (gcd(m, n) = 2): h = y - (x^3 - 3x/2) on
    # y^2 = x^6 - 3x^4 + x + 2 has div(h) = P1 + P2 + oo_+ - 3 oo_- (y ~ +x^3 at
    # oo_+), P1, P2 the points with x^2 - 4x/9 - 8/9 = 0, y = x^3 - 3x/2.
    # Exactly one labelling of the two points at infinity gives a principal
    # divisor. For the superelliptic model the k-th point at infinity is where
    # y ~ zeta_m^(k-1) lc^(1/m) x^(n/m), so oo_+ is the first one; the general
    # code labels them by sheets (either order).
    @testset "Abel–Jacobi map: single points at infinity" begin
      f = y^2 - (x^6 - 3*x^4 + x + 2)
      for se in (true, false)
        RS = _rs(f, 128; superelliptic = se)
        CC = RSM.complex_field(RS)
        tol = ArbField(precision(CC))(2)^(-div(precision(RS), 2))
        d = sqrt(CC(16//81) + 4*CC(8//9))
        xs = [(CC(4//9) + d)/2, (CC(4//9) - d)/2]
        Ps = [RS([x0, x0^3 - 3*x0/2]) for x0 in xs]
        Infs = RSM.infinite_points(RS)
        @test length(Infs) == 2
        pattern = Bool[]
        for (a, b) in ((1, 2), (2, 1))
          D = RSM.divisor(vcat(Ps, [Infs[a], Infs[b]]), [1, 1, 1, -3])
          push!(pattern, all(_is_small(v, tol) for v in RSM.abel_jacobi_map(D, "swap", "complex")))
        end
        @test count(pattern) == 1
        se && @test pattern == [true, false]
      end
    end

    @testset "Constructor, parameters and refusals" begin
      f = y^2 - (x^5 + x^4 + x^3 - x + 4)
      RS1 = RSM.riemann_surface(t^5 + t^4 + t^3 - t + 4, 2, 128)
      @test RSM.computational_model(RS1) isa RSM.SuperellipticModel
      RS2 = _rs(f, 128; superelliptic = true)          # model = :auto
      @test RSM.computational_model(RS2) isa RSM.SuperellipticModel
      @test _overlap(RSM.big_period_matrix(RS1), RSM.big_period_matrix(RS2))
      @test RSM.computational_model(RSM.riemann_surface(f, 128)) isa RSM.SuperellipticModel  # the default
      @test RSM.computational_model(_rs(f, 128)) isa RSM.RiemannSurfaceModel  # superelliptic = false
      # Chebyshev and double exponential integration: same bases
      RS3 = _rs(f, 128; model = :superelliptic, int_style = "DE")
      @test _overlap(RSM.big_period_matrix(RS1), RSM.big_period_matrix(RS3))
      @test length(RSM.basis_of_differentials(RS1)) == 2
      @test_throws ArgumentError RSM.computational_model(_rs(x^3*y + y^3 + x, 100; model = :superelliptic))
      @test_throws ArgumentError RSM.computational_model(_rs(y^2 - (x^2 - 1)^2*(x - 2), 100; model = :superelliptic))  # not separable
      @test RSM.computational_model(_rs(y^2 - (x^2 - 1)^2*(x - 2), 100; superelliptic = true)) isa RSM.RiemannSurfaceModel
    end

    @testset "Over a number field" begin
      F, r = number_field(t^2 - 5, :r)
      S, (X, Y) = polynomial_ring(F, [:x, :y])
      f = X^5 + r*X^3 + X - Y^2
      v = infinite_places(F)[2]
      RSs = RSM.riemann_surface(f, v, 200; model = :superelliptic, integration_method = "heuristic")
      RSg = RSM.riemann_surface(f, v, 200; model = :original, integration_method = "heuristic")
      tau = RSM.small_period_matrix(RSs)
      @test _is_symmetric(tau)
      @test _jacobians_isomorphic(RSM.big_period_matrix(RSs), RSM.big_period_matrix(RSg))
    end
  end
end
