@testset "NormRelation" begin
  Qx, x = PolynomialRing(FlintQQ, "x")
  f = x^8 - x^4 + 1
  K, a = NumberField(f, "a", cached = false)
  S = prime_ideals_up_to(maximal_order(K), 1000)
  class_group(maximal_order(K))
  C, mC = Hecke.sunit_group_fac_elem(S)
  Q, mQ = quo(C, 3)
  CC, mCC = Hecke.sunit_group_fac_elem_quo_via_brauer(K, S, 3)
  elts = GrpAbFinGenElem[]
  for i in 1:ngens(CC)
    u = mCC(CC[i])
    push!(elts, mQ(mC\u))
  end
  V = sub(Q, elts)[1]
  @test order(V) == order(Q)
  S = prime_ideals_up_to(OK, Hecke.factor_base_bound_grh(OK))
  c, U = Hecke.sunit_group_fac_elem_quo_via_brauer(K, S, 2)
  while Hecke.saturate!(c, U, 2)
  end
end
