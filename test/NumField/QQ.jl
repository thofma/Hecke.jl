@testset "NumField/QQ" begin
  @test Hecke.ideal_type(ZZ) == Hecke.ZZIdl
  @test Hecke.ideal_type(Hecke.FlintIntegerRing) == Hecke.ZZIdl
  @test Hecke.fractional_ideal_type(QQ) == Hecke.ZZFracIdl
  @test_throws MethodError Hecke.ideal_type(QQ)

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
  @test is_positive(ZZ(1), inf)
  @test number_field(inf)==QQ
  @test 2*ZZ + 3*ZZ == 1*ZZ
end
