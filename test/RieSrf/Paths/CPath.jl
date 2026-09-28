@testset "CPath" begin
  @testset "Arc parametrization" begin
    CC = AcbField(100)
    for o in (1, -1), (a, b) in ((CC(1), CC(0, 1)), (CC(0, 1), CC(-1)))
      γ = RSM.c_arc(a, b, CC(0), orientation = o)
      @test overlaps(RSM.evaluate(γ, CC(-1)), RSM.start_point(γ))
      @test overlaps(RSM.evaluate(γ, CC(1)),  RSM.end_point(γ))
      δ = reverse(γ)
      @test overlaps(RSM.evaluate(δ, CC(-1)), RSM.end_point(γ))
    end
  end
end
