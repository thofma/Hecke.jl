@testset "Conformance tests" begin
  K, x = laurent_series_field(GF(101), 30, "x", cached = false)
  R = @inferred valuation_ring(K)
  @test is_domain_type(elem_type(R))
  @test !is_exact_type(elem_type(R))
  ConformanceTests.test_Ring_interface(R)
  #ConformanceTests.test_EuclideanRing_interface(R) # doesn't do anything for a non-exact ring
end

@testset "Ring to field" begin
  K, x = laurent_series_field(GF(101), 30, "x")
  R = @inferred valuation_ring(K)
  p = uniformizer(R)
  a = p + p^3 + 4*p^5
  b = x + x^3 + 4*x^5
  @test K(a) == b
  @test R(b) == a

  L, _ = laurent_series_field(GF(3), 10, "x")
  @test_throws ErrorException L(a)

  @test_throws AssertionError R(gen(L))
  @test_throws ArgumentError R(x^-1)
end

@testset "Euclidean functionality" begin
  K, x = laurent_series_field(GF(101), 30, "x")
  R = @inferred valuation_ring(K)
  p = uniformizer(R)

  for a in [zero(R), p, p + 1, p^2]
    for b in [p, p + 1, p^2]
      q, r = divrem(a, b)
      @test a == q*b + r
      if !is_zero(r)
        @test valuation(r) < valuation(b)
      end
      q = div(a, b)
      if !is_zero(a - q*b)
        @test valuation(a - q*b) < valuation(b)
      end
    end
  end

  for a in [zero(R), p, p + 1, p^2]
    for b in [zero(R), p, p + 1, p^2]
      g, u, v = gcdx(a, b)

      @test u*a + v*b == g
      if !is_zero(a) && !is_zero(b)
        @test valuation(g) == min(valuation(a), valuation(b))
      end
    end
  end
end

@testset "Construction" begin
  # Test type stability for different field types
  for F in [GF(3), Native.GF(3), Native.GF(ZZ(3)), Native.GF(3, 2), Native.GF(ZZ(3), 2)]
    K, _ = laurent_series_field(F, 10, "x")
    @inferred valuation_ring(K)
  end
end
