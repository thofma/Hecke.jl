@testset "NumField/QQ" begin
  @test Hecke.ideal_type(ZZ) == Hecke.ZZIdl
  @test Hecke.ideal_type(Hecke.ZZRing) == Hecke.ZZIdl
  @test Hecke.fractional_ideal_type(QQ) == Hecke.ZZFracIdl
  @test_throws MethodError Hecke.ideal_type(QQ)

  I = 2*ZZ
  @test I == ZZ(2)*ZZ

  @test I == ideal(ZZ, 2)
  @test I == ideal(ZZ, [2])
  @test I == ideal(ZZ, [8, 26])

  @test I == ideal(ZZ, ZZ(2))
  @test I == ideal(ZZ, ZZRingElem[2])
  @test I == ideal(ZZ, ZZRingElem[8, 26])

  J = 4*ZZ

  @test I + J == 2 * ZZ
  @test gcd(I, J) == 2 * ZZ
  @test intersect(I, J) == 4 * ZZ
  @test lcm(I, J) == 4 * ZZ

  I = QQ(1, 2)*ZZ
  @test I ==  ZZ * QQ(1, 2)
  J = 1//4 * ZZ
  @test J == ZZ * 1//4
  @test I + J == 1//4 * ZZ
  @test gcd(I, J) == 1//4 * ZZ
  @test intersect(I, J) == 1//2 * ZZ
  @test lcm(I, J) == 1//2 * ZZ


  @test maximal_order(QQ)==ZZ
  @test isreal(inf)

  @test sign(ZZ(2), inf)==1
  @test is_positive(ZZ(1), inf)
  @test number_field(inf)==QQ
  @test 2*ZZ + 3*ZZ == 1*ZZ

  I = ideal(ZZ,2)
  @test quo(ZZ, I)[1] == quo(ZZ,ZZ(2))[1]
  @test coordinates(4, I) == [ZZRingElem(2)]
  @test 4 in I
  @test ZZRingElem(4) in I
  @test !(1 in I)
  @test Hecke.lifted_numerator(ZZ(1))==ZZ(1)
  @test Hecke.lifted_denominator(ZZ(2))==ZZ(1)
end
