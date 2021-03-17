@testset "NumField/QQ" begin

  2*ZZ
  ZZ(2)*ZZ
  QQ(1, 2)*ZZ

  @test maximal_order(QQ)==ZZ
  @test isreal(inf)

  @test sign(ZZ(2), inf)==1
  @test ispositive(ZZ(1), inf)
  @test number_field(inf)==QQ
  @test 2*ZZ + 3*ZZ == 1*ZZ
end
