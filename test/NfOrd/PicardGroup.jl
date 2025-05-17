function test_disc_log_picard(P, mP, O::AbsSimpleNumFieldOrder)
  # principal ideals should always be invertible
  i = 1
  while i <= 5
    I = O(i)*O
    if !iszero(mP\I)
      return false
    end
    i += 1
  end
  for i = 1:5
    a = rand(O, 10)
    while iszero(a)
      a = rand(O, 10)
    end
    I = a*O
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

function test_disc_log_units(U, mU, O::AbsSimpleNumFieldOrder)
  if !iszero(mU\O(1))
    return false
  end

  for i = 1:3
    c = rand(-1:1, ngens(U))
    u = U(c)
    a1 = mU(u)
    a2 = mU(U[1])^c[1]
    for j = 2:ngens(U)
      a2 *= mU(U[j])^c[j]
    end
    if mU\a1 != mU\a2 || mU\a1 != u
      return false
    end
  end
  return true
end

@testset "Picard group and unit group of non maximal orders" begin
  Qx, x = QQ["x"]
  AF = ArbField(20)

  f = x^3 - 2
  K, a = number_field(f, "a", cached = false)
  O = order(K, [ K(1), 10*a, 100*a^2 ])
  P, mP = @inferred picard_group(O)
  @test is_snf(P)
  @test P.snf == ZZRingElem[ 24 ]
  @test test_disc_log_picard(P, mP, O)

  U, mU = Hecke.unit_group_non_maximal(O)
  @test is_snf(U)
  @test U.snf == ZZRingElem[ 2, 0 ]
  @test contains(AF(53.89509393317), Hecke.regulator([ K(mU(U[2])) ], 1))
  @test test_disc_log_units(U, mU, O)

  f = x^3 - 12*x^2 - 6324*x + 459510
  K, a = number_field(f, "a", cached = false)
  O = equation_order(K)
  P, mP = picard_group(O)
  @test is_snf(P)
  @test P.snf == ZZRingElem[ 3, 6, 6, 18 ]
  @test test_disc_log_picard(P, mP, O)

  U, mU = Hecke.unit_group_non_maximal(O)
  @test is_snf(U)
  @test U.snf == ZZRingElem[ 2, 0 ]
  @test contains(AF(169.7695458895), Hecke.regulator([ K(mU(U[2])) ], 1))
  @test test_disc_log_units(U, mU, O)

  f = x^3-9270*x^2-6226*x-2617
  K, a = number_field(f, "a", cached = false)
  O = equation_order(K)
  P, mP = picard_group(O)
  @test is_snf(P)
  @test P.snf == ZZRingElem[ 2, 6, 24 ]
  @test test_disc_log_picard(P, mP, O)

  U, mU = Hecke.unit_group_non_maximal(O)
  @test is_snf(U)
  @test U.snf == ZZRingElem[ 2, 0 ]
  @test contains(AF(31293.8558289993733), Hecke.regulator([ K(mU(U[2])) ], 1))
  @test test_disc_log_units(U, mU, O)

  f = x^4-3072*x^3+7926*x^2-3920*x-9063
  K, a = number_field(f, "a", cached = false)
  O = equation_order(K)
  P, mP = picard_group(O)
  @test is_snf(P)
  @test P.snf == ZZRingElem[ 2, 2, 2, 2, 4 ]
  @test test_disc_log_picard(P, mP, O)

  U, mU = @inferred Hecke.unit_group_non_maximal(O)
  @test is_snf(U)
  @test U.snf == ZZRingElem[ 2, 0, 0 ]
  @test contains(AF(455982050.1598537651), Hecke.regulator(map( x -> K(mU(x)), [ U[2], U[3] ]), 1))
  @test test_disc_log_units(U, mU, O)
  U, mU = @inferred unit_group_fac_elem(O)
  @test contains(AF(455982050.1598537651), Hecke.regulator(map( x -> mU(x), [ U[2], U[3] ]), 1))
  @test all(x -> evaluate(mU(x)) in O, [U[2], U[3]])

  f = x^3+4064*x^2-1608*x-2816
  K, a = number_field(f, "a", cached = false)
  O = equation_order(K)
  P, mP = @inferred picard_group(O)
  @test is_snf(P)
  @test P.snf == ZZRingElem[ 3, 12 ]
  @test test_disc_log_picard(P, mP, O)

  U, mU = Hecke.unit_group_non_maximal(O)
  @test is_snf(U)
  @test U.snf == ZZRingElem[ 2, 0, 0 ]
  @test contains(AF(124666.2260696), Hecke.regulator(map( x -> K(mU(x)), [ U[2], U[3] ]), 1))
  @test test_disc_log_units(U, mU, O)
  U, mU = unit_group_fac_elem(O)
  @test contains(AF(124666.2260696), Hecke.regulator(map( x -> mU(x), [ U[2], U[3] ]), 1))
  @test all(x -> evaluate(mU(x)) in O, [U[2], U[3]])
end
