@testset "Grouping" begin
  RR = ArbField(128)
  rs = [RR(r) for r in (1.05, 1.1, 1.5, 2.0, 2.1, 3.0, 4.5)]
  groups = RSM._gl_group_rs(rs, RR(2)^-100)
  @test 1 <= length(groups) <= length(rs)
  @test issorted(groups, lt = (a, b) -> a < b)
  # every subpath gets a scheme with a smaller parameter than its own
  @test all(r -> groups[RSM._scheme_index(r, groups)] < r, rs)
  # double exponential: one scheme if all parameters are close
  @test length(RSM._de_group_rs([RR(0.5), RR(0.52)])) == 1
  de_groups = RSM._de_group_rs([RR(0.2), RR(0.5), RR(0.9), RR(1.2)])
  @test length(de_groups) == 3 && de_groups[1] < RR(0.2)
end
