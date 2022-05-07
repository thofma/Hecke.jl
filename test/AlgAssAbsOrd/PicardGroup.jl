function test_disc_log_picard(P::GrpAbFinGen, mP::Hecke.MapPicardGrp, O::Hecke.AlgAssAbsOrd)
  for i = 1:5
    I = ideal(O, rand(O, 10))
    while !is_invertible(I)[1]
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
  @test is_snf(P)
  @test P.snf == fmpz[ 2 ]
  @test test_disc_log_picard(P, mP, O)
  I = mP(P[1])
  @test_throws ErrorException Hecke.principal_generator(I)
  I2 = I^2
  a = Hecke.principal_generator(I2)
  @test I2 == ideal(O, a)

end

@testset "Picard group of non maximal orders of algebras" begin

  G = abelian_group([2, 3])
  A = AlgGrp(FlintQQ, G)
  O = Order(A, basis(A))
  P, mP = picard_group(O)
  @test is_snf(P)
  @test ngens(P) == 0
  @test mP\ideal(O, one(O)) in P

  # To make sure it also works with AlgAss
  B, mB = AlgAss(A)
  O = Order(B, basis(B))
  P, mP = picard_group(O)
  @test is_snf(P)
  @test ngens(P) == 0
  @test mP\ideal(O, one(O)) in P

  G = abelian_group([3, 3])
  A = AlgGrp(FlintQQ, G)
  O = Order(A, basis(A))
  P, mP = picard_group(O)
  @test is_snf(P)
  @test P.snf == fmpz[ 3 ]
  @test test_disc_log_picard(P, mP, O)

  Qx, x = FlintQQ["x"]
  f = x^3 - 10x^2 - 3x - 2
  g = x^2 - 9x + 1
  A = AlgAss(f*g)
  O = Order(A, basis(A))
  P, mP = picard_group(O, true)
  @test is_snf(P)
  @test P.snf == fmpz[ 2 ]
  @test test_disc_log_picard(P, mP, O)
  I = mP(P[1])
  @test_throws ErrorException principal_generator(I)
  I2 = I^2
  a = principal_generator(I2)
  @test I2 == ideal(O, a)
  I = ideal(O, 7*one(O)) # not coprime to the conductor of O in the maximal order
  a = principal_generator(I)
  @test I == ideal(O, a)
  # Test the refined discrete logarithm
  @test isdefined(mP, :betas)
  I = rand(O, -5:5)*mP(P[1])
  r, p = Hecke.refined_disc_log_picard_group(I, mP)
  @test evaluate(r)*mP(P[1]) == I
  @test p == P[1]
end

@testset "Unit groups of orders of algebras" begin

  Qx, x = FlintQQ["x"]
  f = x^3 - 12*x^2 - 6324*x + 459510
  K, a = number_field(f, "a", cached = false)
  OK = equation_order(K)
  UK, mUK = unit_group(OK)

  A = AlgAss(f)
  OA = Order(A, basis(A))
  UA, mUA = unit_group(OA)
  @test is_snf(UA)
  @test UA.snf == fmpz[ 2, 0 ]
  G, GtoUK = sub(UK, [ mUK\OK(K(coefficients(elem_in_algebra(mUA(UA[i]), copy = false), copy = false))) for i = 1:ngens(UA) ])
  for i = 1:ngens(UK)
    @test haspreimage(GtoUK, UK[i])[1]
  end

end
