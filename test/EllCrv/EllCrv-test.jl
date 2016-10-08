function test_EllCrv()
  println("test_EllCrv() ... ")
  print("  Constructors ... ")

  @test_throws ErrorException EllipticCurve([1]) 
  @test_throws ErrorException EllipticCurve([1, 2, 3]) 
  @test_throws ErrorException EllipticCurve([1, 2, 3, 4, 5, 6]) 
  @test_throws ErrorException EllipticCurve([0, 0])
  @test_throws ErrorException EllipticCurve([0, 0, 0, 0, 0])

  E = @inferred EllipticCurve([1, 2], false)
  @test typeof(E) == EllCrv{fmpq}

  E = @inferred EllipticCurve([1, 2, 3, 4, 5])
  @test typeof(E) == EllCrv{fmpq}

  # this is Cremona: 11a2, lmfdb: 11.a1
  E = @inferred EllipticCurve([0, -1, 1, -7820, -263580], false)

  println("done")

end
