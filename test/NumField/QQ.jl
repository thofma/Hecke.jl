function check_primary_decomposition(J::Any)
  @testset "Testing primary decomposition for $J" begin
    d = primary_decomposition(J)
    @test all(is_primary(Q) for (Q,P) in d)
    @test all(is_prime(P) for (Q,P) in d)
    @test all(is_subset(P,Q) for (Q,P) in d)
    if isempty(d)
      @test isone(J)
      @test J == radical(J)
    else
      @test intersect([Q for (Q,P) in d]...) == J
      @test prod([P for (Q,P) in d]) == radical(J)
    end
  end
end

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

  @test !is_zero(I)
  @test !is_one(I)
  @test is_maximal(I)
  @test is_prime(I)
  @test is_primary(I)
  check_primary_decomposition(I)

  J = 4*ZZ

  @test I + J == 2 * ZZ
  @test gcd(I, J) == 2 * ZZ
  @test intersect(I, J) == 4 * ZZ
  @test lcm(I, J) == 4 * ZZ

  @test !is_zero(J)
  @test !is_one(J)
  @test !is_maximal(J)
  @test !is_prime(J)
  @test is_primary(J)
  check_primary_decomposition(J)

  J = 0*ZZ
  @test is_zero(J)
  @test !is_one(J)
  @test !is_maximal(J)
  @test is_prime(J)
  @test is_primary(J)
  check_primary_decomposition(J)

  J = 1*ZZ
  @test !is_zero(J)
  @test is_one(J)
  @test !is_maximal(J)
  @test !is_prime(J)
  @test !is_primary(J)
  check_primary_decomposition(J)

  J = 36*ZZ
  @test !is_zero(J)
  @test !is_one(J)
  @test !is_maximal(J)
  @test !is_prime(J)
  @test !is_primary(J)
  @test radical(J) == 6*ZZ
  check_primary_decomposition(J)

  check_primary_decomposition((2*3*5)^2*ZZ)

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

  @test residue_ring(ZZ, ZZ(5))[1] == residue_ring(ZZ, ideal(ZZ, 5))[1]
  @test residue_field(ZZ, ZZ(5))[1] == residue_field(ZZ, ideal(ZZ, 5))[1]
end
