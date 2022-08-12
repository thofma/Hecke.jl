@testset "PosInf basics" begin

  @test inf === PosInf()

  @test zero(inf) === 0
  @test one(inf) === 1

end

@testset "PosInf arithmetic" begin

  @test inf + inf === inf
  @test inf + 1 === inf
  @test inf - 1 === inf
  @test 1 + inf === inf

end

@testset "PosInf comparisons" begin

  @test max(inf, inf) === inf
  @test max(inf, 1) === inf
  @test max(1, inf) === inf

  @test 1 < inf
  @test !(inf < 1)

  @test ZZ(1) < inf
  @test !(inf < ZZ(1))

  @test 1//2 < inf
  @test !(inf < 1//2)

  @test QQ(1//2) < inf
  @test !(inf < QQ(1//2))


  # one positive infinity is not less than infinity (though that does
  # not necessarily mean that they are equal either)
  @test !(inf < inf)

  @test !(inf < 1//0)
  @test !(1//0 < inf)

end

@testset "PosInf predicates" begin

  @test !isone(inf)
  @test !isfinite(inf)
  @test !iszero(inf)

  @test isinf(inf)
  @test is_infinite(inf)
  @test is_positive(inf)

end

@testset "is_infinite for other kinds of infinity" begin

  @test !is_infinite(0)
  @test !is_infinite(0.0)

  @test is_infinite(Inf)
  @test is_infinite(-Inf)

  @test is_infinite(1//0)
  @test is_infinite(-1//0)

  @test is_infinite(big(1)//0)
  @test is_infinite(big(-1)//0)

end
