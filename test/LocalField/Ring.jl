@testset "Conformance tests" begin
  # PadicField
  K = padic_field(17)
  R = valuation_ring(K)
  @test is_domain_type(elem_type(R))
  @test !is_exact_type(elem_type(R))
  ConformanceTests.test_Ring_interface(R)
  #ConformanceTests.test_EuclideanRing_interface(R) # doesn't do anything for a non-exact ring

  # QadicField
  K, a = qadic_field(17, 2)
  R = valuation_ring(K)
  @test is_domain_type(elem_type(R))
  @test !is_exact_type(elem_type(R))
  ConformanceTests.test_Ring_interface(R)
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
  #ConformanceTests.test_EuclideanRing_interface(R) # doesn't do anything for a non-exact ring
end
