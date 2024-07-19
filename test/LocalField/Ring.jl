function _integral_test_elem(R::PadicField)
  p = prime(R)
  prec = rand(1:R.prec_max)
  r = ZZRingElem(0):p-1
  return R(sum(rand(r)*p^i for i in 0:prec))
end

function _integral_test_elem(R::NonArchLocalField)
  d = degree(R)
  a = gen(R)
  x = R()
  for i in 0:d - 1
    x += _integral_test_elem(base_field(R))*a^i
  end
  return x
end

function test_elem(R::Hecke.LocalFieldValuationRing)
  return R(_integral_test_elem(Hecke._field(R)))
end

function Base.isapprox(a::Hecke.LocalFieldValuationRingElem{S, T}, b::Hecke.LocalFieldValuationRingElem{S, T}) where {S, T}
  return a == b
end

@testset "Conformance tests" begin
  # PadicField
  K = padic_field(17)
  R = valuation_ring(K)
  @test is_domain_type(elem_type(R))
  @test !is_exact_type(elem_type(R))
  test_Ring_interface(R)
  #test_EuclideanRing_interface(R) # doesn't do anything for a non-exact ring

  # QadicField
  K, a = qadic_field(17, 2)
  R = valuation_ring(K)
  @test is_domain_type(elem_type(R))
  @test !is_exact_type(elem_type(R))
  test_Ring_interface(R)
  #test_EuclideanRing_interface(R) # doesn't do anything for a non-exact ring

  # LocalField
  F, _ = cyclotomic_field(20)
  OF = maximal_order(F)
  P = prime_decomposition(OF, 2)[1][1]
  K, toK = completion(F, P)
  R = valuation_ring(K)
  @test is_domain_type(elem_type(R))
  @test !is_exact_type(elem_type(R))
  test_Ring_interface(R)
  #test_EuclideanRing_interface(R) # doesn't do anything for a non-exact ring
end
