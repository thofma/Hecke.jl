@testset "NormRel" begin
  @testset "GRH keyword" begin
    for GRH in (false, true)
      K, _ = cyclotomic_field(12; cached = false)
      S = prime_ideals_over(maximal_order(K), 2)
      U, mU = Hecke.NormRel._sunit_group_fac_elem_via_brauer(K, S; GRH)
      C, mC = Hecke.sunit_group_fac_elem(S; GRH)
      Q, _ = quo(C, [mC\mU(U[i]) for i in 1:ngens(U)])
      @test order(Q) == 1
    end
  end

  Qx, x = polynomial_ring(QQ, "x")
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

  N = Hecke.NormRel._norm_relation_setup_generic(K; small_degree = true, pure = true)
  h = Hecke.NormRel._class_number_via_brauer(maximal_order(K), N; GRH = false)
  @test h == 1
  h = Hecke.NormRel._class_number_via_brauer(maximal_order(K), N; GRH = true)
  @test h == 1
  # Test a non-normal group

  Qx, x = polynomial_ring(QQ, "x");
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

  @testset "No Brauer relation" begin
    K, = cyclotomic_field(5; cached = false)
    # the error path prints the group
    @test_throws ErrorException redirect_stdout(devnull) do
      Hecke.NormRel._norm_relation_setup_generic(K)
    end
    @test Hecke.NormRel.has_useful_generalized_norm_relation(small_group(24, 3))
    @test !Hecke.NormRel.has_useful_generalized_norm_relation(small_group(8, 4))
  end

  @testset "Induced action" begin
    K, = number_field(x^4 - 10*x^2 + 1; cached = false)
    @test length(Hecke.NormRel._norm_relation_for_sunits(K)) == 3

    N = Hecke.NormRel._norm_relation_setup_generic(K; pure = true)
    c = Hecke.class_group_ctx(maximal_order(K))
    FB = c.FB.ideals
    for i in 1:length(N)
      k, = Hecke.NormRel.subfield(N, i)
      degree(k) == 1 && continue
      n = divexact(degree(K), degree(k))
      zk = lll(maximal_order(k))
      lp = [P for p in unique!(minimum.(FB)) for (P, _) in prime_decomposition(zk, p)]
      z = redirect_stdout(devnull) do
        Hecke.NormRel.induce_action(N, i, 1, lp, c.FB, Vector{Tuple{Int, ZZRingElem}}[])
      end
      zz = Hecke.NormRel.induce_action_from_subfield(N, i, lp, c.FB, Vector{Tuple{Int, ZZRingElem}}[])
      @test length(zz) == degree(K)
      for y in push!(zz, z)
        @test all(norm(prod(FB[j]^Int(e) for (j, e) in y[l])) == norm(lp[l])^n for l in 1:length(lp))
      end
    end
  end
end
