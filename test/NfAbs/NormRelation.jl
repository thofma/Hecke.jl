@testset "NormRel" begin
  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x^8 - x^4 + 1
  K, a = number_field(f, "a", cached = false)
  S = prime_ideals_up_to(maximal_order(K), 1000)
  class_group(maximal_order(K))
  C, mC = Hecke.sunit_group_fac_elem(S)
  Q, mQ = quo(C, 3)
  CC, mCC = Hecke.NormRel._sunit_group_fac_elem_quo_via_brauer(K, S, 3)
  elts = FinGenAbGroupElem[]
  for i in 1:ngens(CC)
    u = mCC(CC[i])
    push!(elts, mQ(mC\u))
  end
  V = sub(Q, elts)[1]
  @test order(V) == order(Q)
  S = prime_ideals_up_to(maximal_order(K), Hecke.factor_base_bound_grh(maximal_order(K)))
  c, U = Hecke.NormRel._sunit_group_fac_elem_quo_via_brauer(K, S, 2)

  # Test a non-normal group

  Qx, x = polynomial_ring(FlintQQ, "x");
  K, a = number_field(x^4-2*x^2+9);
  OK = maximal_order(K);
  lP = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]
  push!(lP, ideal(OK, 43, OK(a^2 - 12)));
  push!(lP, ideal(OK, 47, OK(a^2 - 14*a + 3)));
  push!(lP, ideal(OK, 53, OK(a^2 - 7*a - 3)));
  push!(lP, ideal(OK, 5, OK(a^2 - 1*a + 2)));
  push!(lP, ideal(OK, 2, OK(1//12*a^3 + 1//4*a^2 + 7//12*a + 7//4)));
  push!(lP, ideal(OK, 3, OK(a^2 + 1)));
  push!(lP, ideal(OK, 3, OK(8*a^3 + 4*a^2 + 2*a + 6)));
  push!(lP, ideal(OK, 37, OK(a^2 + 12*a - 3)));
  push!(lP, ideal(OK, 41, OK(a-15)));
  push!(lP, ideal(OK, 5, OK(a^2 + 1*a + 2)))
  U, mU = Hecke.NormRel._sunit_group_fac_elem_quo_via_brauer(K, lP, 8)
  S, mS = Hecke.sunit_group_fac_elem(lP)
  Q, mQ = quo(S, 8)
  V = quo(Q, [mQ(mS\(mU(U[i]))) for i in 1:ngens(U)])
  @test order(V[1]) == 1

  # Test a non-normal number field (with a C2 x C2 subgroup of automorphisms)
  # We do not test the non-quotient S-unit group, since the saturation is
  # killing us (because of assertions to full level)
  f = x^8 - 8*x^6 + 80*x^4 + 512*x^2 + 1024
  K, a = number_field(f)
  OK = lll(maximal_order(K))
  # S invariant
  lP = prime_ideals_up_to(OK, 50)
  U, mU = Hecke.NormRel._sunit_group_fac_elem_via_brauer(K, lP)
  S, mS = Hecke.sunit_group_fac_elem(lP)
  V = quo(S, [(mS\(mU(U[i]))) for i in 1:ngens(U)])
  @test order(V[1]) == 1
end
