function test_elem(R::Hecke.LaurentSeriesFieldValuationRing)
  return R(rand(data(R), 0:Int(characteristic(R)) - 1))
end

function Base.isapprox(a::T, b::T) where {T <: Hecke.LaurentSeriesFieldValuationRingElem}
  return a == b
end

@testset "Conformance tests" begin
  K, x = laurent_series_field(GF(101), 30, "x", cached = false)
  R = valuation_ring(K)
  @test is_domain_type(elem_type(R))
  @test !is_exact_type(elem_type(R))
  test_Ring_interface(R)
  #test_EuclideanRing_interface(R) # doesn't do anything for a non-exact ring
end
