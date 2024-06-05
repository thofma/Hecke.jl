function test_disc_log_picard(P::FinGenAbGroup, mP::Hecke.MapPicardGrp, O::Hecke.AlgAssAbsOrd)
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
  A = StructureConstantAlgebra(f*g)
  O = maximal_order(A)
  P, mP = picard_group(O)
  @test is_snf(P)
  @test P.snf == ZZRingElem[ 2 ]
  @test test_disc_log_picard(P, mP, O)
  I = mP(P[1])
  @test_throws ErrorException principal_generator(I)
  I2 = I^2
  a = Hecke.principal_generator(I2)
  @test I2 == ideal(O, a)

end

@testset "Picard group of non maximal orders of algebras" begin

  G = abelian_group([2, 3])
  A = GroupAlgebra(FlintQQ, G)
  O = Order(A, basis(A))
  P, mP = picard_group(O)
  @test is_snf(P)
  @test ngens(P) == 0
  @test mP\ideal(O, one(O)) in P

  # To make sure it also works with StructureConstantAlgebra
  B, mB = StructureConstantAlgebra(A)
  O = Order(B, basis(B))
  P, mP = picard_group(O)
  @test is_snf(P)
  @test ngens(P) == 0
  @test mP\ideal(O, one(O)) in P

  G = abelian_group([3, 3])
  A = GroupAlgebra(FlintQQ, G)
  O = Order(A, basis(A))
  P, mP = picard_group(O)
  @test is_snf(P)
  @test P.snf == ZZRingElem[ 3 ]
  @test test_disc_log_picard(P, mP, O)

  Qx, x = FlintQQ["x"]
  f = x^3 - 10x^2 - 3x - 2
  g = x^2 - 9x + 1
  A = StructureConstantAlgebra(f*g)
  O = Order(A, basis(A))
  P, mP = picard_group(O, true)
  @test is_snf(P)
  @test P.snf == ZZRingElem[ 2 ]
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

  A = StructureConstantAlgebra(f)
  OA = Order(A, basis(A))
  UA, mUA = unit_group(OA)
  @test is_snf(UA)
  @test UA.snf == ZZRingElem[ 2, 0 ]
  G, GtoUK = sub(UK, [ mUK\OK(K(coefficients(elem_in_algebra(mUA(UA[i]), copy = false), copy = false))) for i = 1:ngens(UA) ])
  for i = 1:ngens(UK)
    @test has_preimage_with_preimage(GtoUK, UK[i])[1]
  end

  A = StructureConstantAlgebra(x * (x^2 - 113000))
  O = Order(A, basis(A), cached = false)
  U, mU = unit_group(O)
  UU, mUU = unit_group_fac_elem(O)
  u = mUU(UU[2])
  @test abs(norm(evaluate(u))) == 1
  @test evaluate(u) in O
  @test is_trivial(quo(U, [mU\(O(evaluate(mUU(u)))) for u in gens(UU)])[1])
end
