@testset "PeriodMatrix" begin
  @testset "Sanity checks: $name" for (name, f, g) in FAST_CURVES
    RS = _computed(_rs(f, 100))
    test_sanity(RS; expected_genus = g)
  end

  @testset "Same bases, different integration" begin
    for (name, f, g) in FAST_CURVES[[5, 11, 14]]        # f2, q1, f30
      @testset "$name: GL vs Mixed" begin
        test_same_result(_rs(f, 100; int_style = "Mixed"), _rs(f, 100; int_style = "GL"))
      end
      @testset "$name: midpoint precision on/off" begin
        test_same_result(_rs(f, 200; midpoint_precision = 0), _rs(f, 200; midpoint_precision = 100))
      end
    end
  end

  @testset "Precision 100 vs 200" begin
    for (name, f, g) in FAST_CURVES[[6, 10, 14]]        # g2, g15, f30
      @testset "$name" begin
        # same model at both precisions (model = :auto could choose differently)
        @test _overlap(RSM.small_period_matrix(_rs(f, 100; model = :original)),
                       RSM.small_period_matrix(_rs(f, 200; model = :original)))
      end
    end
  end

  @testset "Neurohr's failing curves: $name" for (name, f) in NEUROHR_FAIL_CURVES
    for model in (:original, :swapped)
      RS1 = _computed(_rs(f, 100; model = model))
      test_sanity(RS1)
      # the period matrix does not depend on the precision (same bases)
      RS2 = _rs(f, 200; model = model)
      @test _overlap(RSM.small_period_matrix(RS1), RSM.small_period_matrix(RS2))
    end
    test_abel_jacobi_principal(_rs(f, 100); ntests = 1)
  end

  @long_test begin
    @testset "Long: $name" for (name, f, g) in LONG_CURVES
      RS = _computed(_rs(f, 200; midpoint_precision = 0))
      test_sanity(RS; expected_genus = g)
      test_same_result(RS, _rs(f, 200; midpoint_precision = 100))
    end

    @testset "Long: DE vs Mixed" begin
      for (name, f, g) in FAST_CURVES[[5, 11]]
        @testset "$name" begin
          test_same_result(_rs(f, 100; int_style = "Mixed"), _rs(f, 100; int_style = "DE"))
        end
      end
    end


    @testset "Long: random curves" begin
      rng = MersenneTwister(20260924)
      for _ in 1:10
        dx, dy = rand(rng, 2:4), rand(rng, 3:4)
        f = sum(rand(rng, -9:9) * x^i * y^j for i in 0:dx for j in 0:dy)
        fac = factor(f)
        (length(fac) == 1 && all(e == 1 for (_, e) in fac) && degree(f, 2) >= 3) || continue
        @testset "$f" begin
          test_sanity(_rs(f, 100))
        end
      end
    end

    @testset "Very long: $name" for (name, f, g) in VERY_LONG_CURVES
      RS = _computed(_rs(f, 200))
      test_sanity(RS; expected_genus = g)
    end
  end
end
