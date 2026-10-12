@testset "Constructors" begin
  M = matrix(QQ, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, -1])
  C = conic_curve(M)
  @test conic_curve(QQ, M) == C
  @test conic_curve(QQ, [1, 1, -1]) == C

  K, = quadratic_field(-1)
  C = conic_curve(K, M)
  @test base_field(C) === K
  @test coefficients(C) == Tuple(K.([1, 1, -1, 0, 0, 0]))
  @test all(z -> parent(z) === K, coefficients(C))
  @test conic_curve(K, QQ.([1, 1, -1])) == C
end

@testset "Constructors with a specified field" begin
  F5, F7, F25 = GF(5), GF(7), GF(5, 2)
  @test elem_type(F5) === elem_type(F7)
  @test elem_type(F5) === elem_type(F25)

  M = diagonal_matrix(F5.([1, 1, -1]))
  for F in (F5, F25)
    expected = Tuple(F.([1, 1, -1, 0, 0, 0]))
    for C in (conic_curve(F, M), conic_curve(F, F5.([1, 1, -1])),
              conic_curve(F, F5.([1, 1, -1, 0, 0, 0])))
      @test base_field(C) === F
      @test all(z -> parent(z) === F, coefficients(C))
      @test coefficients(C) == expected
    end
  end

  # Check every coefficient's parent, including when the first is already in F25.
  C = conic_curve(F25, [F25(1), F5(1), F5(-1)])
  @test base_field(C) === F25
  @test all(z -> parent(z) === F25, coefficients(C))
  @test coefficients(C) == Tuple(F25.([1, 1, -1, 0, 0, 0]))

  # There is no field embedding between different characteristics.
  @test_throws ErrorException conic_curve(F7, M)
  @test_throws ErrorException conic_curve(F7, F5.([1, 1, -1]))
  @test_throws ErrorException conic_curve(F7, F5.([1, 1, -1, 0, 0, 0]))
end
