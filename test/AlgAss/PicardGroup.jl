function test_disc_log_picard(P, mP, O::Hecke.AlgAssAbsOrd)
  for i = 1:5
    I = ideal(O, rand(O, 10))
    while !isinvertible(I)[1]
      I = ideal(O, rand(O, 10))
    end
    if !iszero(mP\I)
      return false
    end
  end

  if ngens(P) == 0
    return true
  end

  for i = 1:3
    c = rand(1:10, ngens(P))
    p = P(c)
    I1 = mP(p)
    I2 = mP(P[1])^c[1]
    for j = 2:ngens(P)
      I2 *= mP(P[j])^c[j]
    end
    if mP\I1 != mP\I2 || mP\I1 != p
      return false
    end
  end
  return true
end

@testset "Picard group of maximal orders of algebras" begin

  Qx, x = FlintQQ["x"]
  f = x^3 - 10x^2 - 3x - 2
  g = x^2 - 9x + 1
  A = AlgAss(f*g)
  O = maximal_order(A)
  P, mP = picard_group(O)
  @test issnf(P)
  @test P.snf == fmpz[ 2 ]
  @test test_disc_log_picard(P, mP, O)
  I = mP(P[1])
  @test_throws ErrorException Hecke.principal_gen(I)
  I2 = I^2
  a = Hecke.principal_gen(I2)
  @test I2 == ideal(O, a)

end

@testset "Picard group of non maximal orders of algebras" begin

  G = DiagonalGroup([2, 3])
  A = AlgGrp(FlintQQ, G)
  O = Order(A, basis(A))
  P, mP = picard_group(O)
  @test issnf(P)
  @test ngens(P) == 0
  @test mP\ideal(O, one(O)) in P

  # To make sure it also works with AlgAss
  B, mB = AlgAss(A)
  O = Order(B, basis(B))
  P, mP = picard_group(O)
  @test issnf(P)
  @test ngens(P) == 0
  @test mP\ideal(O, one(O)) in P

  G = DiagonalGroup([3, 3])
  A = AlgGrp(FlintQQ, G)
  O = Order(A, basis(A))
  P, mP = picard_group(O)
  @test issnf(P)
  @test P.snf == fmpz[ 3 ]
  @test test_disc_log_picard(P, mP, O)

  Qx, x = FlintQQ["x"]
  f = x^3 - 10x^2 - 3x - 2
  g = x^2 - 9x + 1
  A = AlgAss(f*g)
  O = Order(A, basis(A))
  P, mP = picard_group(O, true)
  @test issnf(P)
  @test P.snf == fmpz[ 2 ]
  @test test_disc_log_picard(P, mP, O)
  # Test the refined discrete logarithm
  @test isdefined(mP, :betas)
  I = mP(P[1])
  @test_throws ErrorException Hecke.principal_gen(I)
  I2 = I^2
  a = Hecke.principal_gen(I2)
  @test I2 == ideal(O, a)
  I = ideal(O, 7*one(O)) # not coprime to the conductor of O in the maximal order
  a = Hecke.principal_gen(I)
  @test I == ideal(O, a)
end
