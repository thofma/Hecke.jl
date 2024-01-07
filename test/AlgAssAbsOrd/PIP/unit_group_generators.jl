begin
  G = small_group(10, 1) # D_5
  QG = QQ[G]
  ZG = integral_group_ring(QG)
  Hecke._assert_has_refined_wedderburn_decomposition(QG)
  @test Hecke._unit_group_generators(ZG) isa Vector
end
