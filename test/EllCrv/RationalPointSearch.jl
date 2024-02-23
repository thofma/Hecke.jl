@testset "Rational point search" begin
  coefficients = ZZRingElem[10, -7, 0, 1]
  bounds = [25, 250, 2500, 25000, 250000]
  cts = [29, 49, 79, 105, 125]
  for (b, c) in zip(bounds, cts)
    pts = @inferred Hecke.find_points(coefficients, b)
    @test length(pts) == c
  end

  E = elliptic_curve([-7, 10])
  for (b, c) in zip(bounds, cts)
    pts = @inferred Hecke.find_points(E, b)
    @test length(pts) == c
  end

  coefficients = ZZRingElem[2, 1, -3, 1]
  bounds = [10, 100, 1000, 10000]
  cts = [4, 4, 4, 4]
  for (b, c) in zip(bounds, cts)
    pts = @inferred Hecke.find_points(coefficients, b)
    @test length(pts) == c
  end

  coefficients = ZZRingElem[10, -1, 0, 1]
  bounds = [10, 100, 1000, 10000]
  cts = [9, 9, 19, 23]
  for (b, c) in zip(bounds, cts)
    pts = @inferred Hecke.find_points(coefficients, b)
    @test length(pts) == c
  end

  coefficients = ZZRingElem[1, 0, -1, 10]
  bounds = [10, 100, 1000, 10000]
  cts = [11, 17, 21, 33]
  for (b, c) in zip(bounds, cts)
    pts = @inferred Hecke.find_points(coefficients, b)
    @test length(pts) == c
  end

  coefficients = ZZRingElem[3, -2, 0, -1, 10]
  bounds = [10, 100, 1000, 10000]
  cts = [4, 4, 4, 8]
  for (b, c) in zip(bounds, cts)
    pts = @inferred Hecke.find_points(coefficients, b)
    @test length(pts) == c
  end

  coefficients = ZZRingElem[1, -2, 0, -1, 1, 5, 1]
  bounds = [10, 100, 1000, 10000]
  cts = [6, 8, 8, 8]
  for (b, c) in zip(bounds, cts)
    pts = @inferred Hecke.find_points(coefficients, b)
    @test length(pts) == c
  end

  coefficients = ZZRingElem[4, -2, 0,  1, 3, 1]
  bounds = [10000]
  cts = [9]
  for (b, c) in zip(bounds, cts)
    pts = @inferred Hecke.find_points(coefficients, b)
    @test length(pts) == c
  end

  @testset "Negativity" begin
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

    f = x^3 - 3*x^2 + x + 2
    a, b, c = Hecke.negative_intervals(f)
    @test length(a) == 1
    @test length(b) == 1
    @test length(c) == 0
    @test -1 < a[1]
    @test b[1][1] < 1.8 < b[1][2]

    f = x^4 - 2*x^3 + x^2 + x + 1
    a, b, c = Hecke.negative_intervals(f)
    @test length(a) == 0
    @test length(b) == 0
    @test length(c) == 0
  end
end
