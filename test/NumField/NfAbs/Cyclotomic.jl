@testset "Cyclotomic" begin
  K, a = CyclotomicRealSubfield(7)
  v = cyclotomic_units_totally_real(K)
  @test length(v) == degree(K) # = unit rank + 1
  # Class number of Q(zeta_7)^+ is one, so the cyclotomic units are the units
  @test overlaps(regulator(maximal_order(K)), regulator(v[2:end]))
end
