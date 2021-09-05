@testset "NumField/QQ" begin

  I = 2*ZZ
  @test I == ZZ(2)*ZZ

  @test I == ideal(ZZ, 2)
  @test I == ideal(ZZ, [2])
  @test I == ideal(ZZ, [8, 26])

  @test I == ideal(ZZ, ZZ(2))
  @test I == ideal(ZZ, fmpz[2])
  @test I == ideal(ZZ, fmpz[8, 26])

  QQ(1, 2)*ZZ

  @test maximal_order(QQ)==ZZ
  @test isreal(inf)

  @test sign(ZZ(2), inf)==1
  @test ispositive(ZZ(1), inf)
  @test number_field(inf)==QQ
  @test 2*ZZ + 3*ZZ == 1*ZZ
end
