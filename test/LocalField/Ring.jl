@testset "Conformance tests" begin
  # PadicField
  K = padic_field(17)
  R = valuation_ring(K)
  @test is_domain_type(elem_type(R))
  @test !is_exact_type(elem_type(R))
  ConformanceTests.test_Ring_interface(R)
  test_divexact_by_zero(R)
  #ConformanceTests.test_EuclideanRing_interface(R) # doesn't do anything for a non-exact ring

  # QadicField
  K, a = qadic_field(17, 2)
  R = valuation_ring(K)
  @test is_domain_type(elem_type(R))
  @test !is_exact_type(elem_type(R))
  ConformanceTests.test_Ring_interface(R)
  test_divexact_by_zero(R)
  #ConformanceTests.test_EuclideanRing_interface(R) # doesn't do anything for a non-exact ring

  # LocalField
  F, _ = cyclotomic_field(20)
  OF = maximal_order(F)
  P = prime_decomposition(OF, 2)[1][1]
  K, toK = completion(F, P)
  R = valuation_ring(K)
  @test is_domain_type(elem_type(R))
  @test !is_exact_type(elem_type(R))
  ConformanceTests.test_Ring_interface(R)
  test_divexact_by_zero(R)
  #ConformanceTests.test_EuclideanRing_interface(R) # doesn't do anything for a non-exact ring
end

@testset "Content of matrices" begin
  # the content is a power of the uniformizer, also in ramified extensions
  K = padic_field(3, precision = 10)
  Kx, x = polynomial_ring(K, "x")
  E, = eisenstein_extension(x^2 - 3, "a")
  Q9, = qadic_field(3, 2, precision = 10)
  for F in [K, E, Q9]
    R = valuation_ring(F)
    a = R(uniformizer(F))
    @test content(matrix(R, 2, 2, [a^2, a^3, 0, a^5])) == a^2
    @test isone(content(matrix(R, 2, 2, [a^4, a^3 + 1, 0, a])))
    @test iszero(content(zero_matrix(R, 2, 2)))
  end
end
