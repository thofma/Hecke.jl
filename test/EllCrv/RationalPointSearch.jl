@testset "Rational point search" begin
  # Some tests for the negativity
  Qx, x = QQ["x"]
  f = x^3 - 2*x^2 + 1 # rational root
  a, b, c = Hecke.negative_intervals(f)
  @test length(a) == 1
  @test length(b) == 1
  @test length(c) == 0
  @test b[1][1] <= 3//2 <= b[1][2]

  f = (x^3 - 2*x^2 + 1)*(x + 3)
  a, b, c = Hecke.negative_intervals(f)
  @test length(a) == 0
  @test length(b) == 2
  @test length(c) == 0
  @test b[1][1] <= -2 <= b[1][2]
  @test b[2][1] <= 3//2 <= b[2][2]
end
