@testset "AnalyticContinuation" begin
  @testset "Stress: nearly coinciding branch points" begin
    ks = riesrf_long_tests() ? (2, 5, 10, 20, 30, 40) : (2, 5, 10)
    for (fam, family) in STRESS_FAMILIES
      for k in ks
        (fam, k) in LIMIT_CASES && continue
        eps = QQ(1, ZZ(10)^k)
        prec = max(200, 4k + 100)
        @testset "$fam, eps = 1e-$k" begin
          RS = _computed(_rs(family(eps), prec))
          test_sanity(RS)
          test_same_result(RS, _rs(family(eps), prec; midpoint_precision = 100))
        end
      end
    end
  end

  @long_test begin
    # Beyond the precision limit: the computation may succeed (then it must be
    # correct) or refuse, but only with a clean error about precision or root
    # isolation, never with NaNs, bounds errors etc.
    @testset "Precision limits: $fam, eps = 1e-$k" for (fam, k) in LIMIT_CASES
      family = Dict(STRESS_FAMILIES)[fam]
      eps = QQ(1, ZZ(10)^k)
      prec = max(200, 4k + 100)
      res = try _computed(_rs(family(eps), prec)) catch e; e end
      if res isa Exception
        msg = _root_message(res)
        @info "$fam, eps = 1e-$k: refused" msg
        @test _is_clean_refusal(msg)
      else
        test_sanity(res)
      end
    end
  end
end
