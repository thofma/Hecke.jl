@testset "CPath" begin
  @testset "Arc parametrization" begin
    CC = AcbField(100)
    for o in (1, -1), (a, b) in ((CC(1), CC(0, 1)), (CC(0, 1), CC(-1)))
      γ = RSM.arc_path(a, b, CC(0), orientation = o)
      @test overlaps(RSM.evaluate(γ, CC(-1)), RSM.start_point(γ))
      @test overlaps(RSM.evaluate(γ, CC(1)),  RSM.end_point(γ))
      δ = reverse(γ)
      @test overlaps(RSM.evaluate(δ, CC(-1)), RSM.end_point(γ))
    end
  end

  @testset "Derivatives, reverse paths, chains" begin
    CC = AcbField(100)
    h = CC(1//10^12)
    paths = [RSM.line_path(CC(1), CC(2, 3)),
             RSM.arc_path(CC(1), CC(0, 1), CC(0)),
             RSM.circle_path(CC(2), CC(1); orientation = -1),
             RSM.line_to_infinity(CC(1, 1))]
    for path in paths
      # derivative against a central difference at t = 1/3
      t = CC(1//3)
      difference = (RSM.evaluate(path, t + h) - RSM.evaluate(path, t - h)) / (2*h)
      @test abs(difference - RSM.evaluate_derivative(path, t)) < ArbField(100)(1//10^10)
    end
    for path in paths[1:3]
      reversed = reverse(path)
      @test reverse(reversed) === path
      @test overlaps(RSM.evaluate(reversed, CC(1//3)), RSM.evaluate(path, CC(-1//3)))
    end
    @test RSM.is_line(paths[1]) && RSM.is_arc(paths[2]) && RSM.is_circle(paths[3])

    # a closed chain (circle) and its powers
    loop = RSM.CChain([paths[3]])
    @test RSM.is_closed(loop)
    @test length(loop^3) == 3
    @test length(loop^0) == 1 && RSM.path_type((loop^0).paths[1]) === :point
    @test (loop^-2).paths[1] === reverse(paths[3])
    @test_throws ArgumentError RSM.CChain([paths[1]])^2       # not closed
  end
end
