@testset "NumFieldOrder" begin
  x = polynomial_ring(QQ, "x", cached = false)[2]
  K, a = number_field(x^2+1, check = false, cached = false)
  Kns, gKns = number_field([x^2+1], check = false, cached = false)
  Kt, t = polynomial_ring(K, "t", cached = false)
  L, b = number_field(t^2+3, "b", cached = false, check = false)
  Lns, gLns = number_field([t^2+3], cached = false, check = false)

  OK = maximal_order(K)
  @inferred Hecke.nf(OK)
  @test is_simple(OK)
  @test is_commutative(OK)
  @test @inferred is_equation_order(OK)
  @test @inferred is_maximal(OK)
  @test @inferred degree(OK) == 2
  @test @inferred absolute_degree(OK) == 2
  BOK = absolute_basis(OK)
  @test @inferred discriminant(BOK) == @inferred discriminant(OK)
  @test @inferred signature(OK) == (0, 1)
  @test @inferred discriminant(OK, QQ) == discriminant(OK)

  OKns = maximal_order(Kns)
  @inferred Hecke.nf(OKns)
  @test !is_simple(OKns)
  @test is_commutative(OKns)
  @test @inferred !is_equation_order(OKns)
  @test @inferred is_maximal(OKns)
  @test @inferred degree(OKns) == 2
  @test @inferred absolute_degree(OKns) == 2
  BOKns = absolute_basis(OKns)
  @test @inferred discriminant(BOKns) == @inferred discriminant(OKns)
  @test @inferred signature(OKns) == (0, 1)
  @test @inferred discriminant(OKns, QQ) == discriminant(OKns)

  OL = maximal_order(L)
  @inferred Hecke.nf(OL)
  @test is_simple(OL)
  @test is_commutative(OL)
  @test @inferred !is_equation_order(OL)
  @test @inferred is_maximal(OL)
  @test @inferred degree(OL) == 2
  @test @inferred absolute_degree(OL) == 4
  BOL = absolute_basis(OL)
  @test numerator(det(trace_matrix(map(elem_in_nf, BOL)))) == @inferred absolute_discriminant(OL)
  @test @inferred signature(OL) == (0, 2)
  @test @inferred discriminant(OL, QQ) == absolute_discriminant(OL)

  OLns = maximal_order(Lns)
  @inferred Hecke.nf(OLns)
  @test !is_simple(OLns)
  @test is_commutative(OLns)
  @test @inferred !is_equation_order(OLns)
  @test @inferred is_maximal(OLns)
  @test @inferred degree(OLns) == 2
  @test @inferred absolute_degree(OLns) == 4
  BOLns = absolute_basis(OLns)
  @test numerator(det(trace_matrix(map(elem_in_nf, BOLns)))) == @inferred absolute_discriminant(OLns)
  @test @inferred signature(OLns) == (0, 2)
  @test @inferred discriminant(OLns, QQ) == absolute_discriminant(OLns)

end

@testset "RelResidueField" begin
  Qs, s = QQ["s"]
  K,a = number_field(s^4+s+1, "a")
  Kt, t = K["t"]
  E, b = number_field(t^2-a*t+1,"b")
  Eu, u = E["u"]
  L, c = number_field(u^3-7, "c")
  OK = maximal_order(K)
  OE = maximal_order(E)
  OL = maximal_order(L)
  p = prime_decomposition(OK, 11)[1][1]
  P = prime_decomposition(OE,p)[1][1]
  PP = prime_decomposition(OL, P)[1][1]
  FL, projL = relative_residue_field(OL, PP)
  mL = extend(projL, L)

  e,f = PP.splitting_type
  @test degree(defining_polynomial(FL)) == f
  e,f = P.splitting_type
  @test degree(defining_polynomial(base_field(FL))) == f
  e, f = p.splitting_type
  @test degree(defining_polynomial(base_field(base_field(FL)))) == f

  @test domain(projL.map_subfield) === OE
  @test mL(gen(L)//2) == gen(FL)//2
  @test absolute_degree(FL) == 6
  @test characteristic(Hecke.prime_field(FL)) == 11

  K,a = rationals_as_number_field()
  Kt, t = K["t"]
  E,b = number_field(t^4-5*t^3-6*t^2+5*t+1,"b")
  OK = maximal_order(K)
  OE = maximal_order(E)
  p = prime_decomposition(OK, 2)[1][1]
  P = prime_decomposition(OE, p)[1][1]
  @test is_index_divisor(OE, p)
  FE, projE = relative_residue_field(OE, P)
  _, f = P.splitting_type
  @test degree(defining_polynomial(FE)) == f
  mE = extend(projE, E)
  @test !iszero(mE(gen(E)))
  @test get_attribute(P, :rel_residue_field_map) !== nothing

end

@testset "Order" begin
  # extension
  k, _ = wildanger_field(3, 13)
  k, _ = normal_closure(k)
  G, mG = automorphism_group(k)
  gs = [mG(x)(gen(k)) for x = gens(G)]
  o = extend(equation_order(k), gs)
  @test discriminant(o) == -210517451702272
  push!(gs, gen(k))
  oo = order(gs)
  @test o == oo

  Qx, x = QQ["x"]
  K, a = quadratic_field(5)
  R = order(K, [10*a])
  @test extend(R, [a]) == equation_order(K)
  @test extend(R, []) == R
  @test extend(R, [1//2 + a//2]) == maximal_order(K)
  @test extend(maximal_order(R), [a]) == maximal_order(R)

  K, a = number_field(x, "a")
  @test order(K, [1]) == equation_order(K)
  @test order(K, []) == equation_order(K)

  K, a = number_field(x^4 - 10*x^2 + 1, "a")
  x = 1//2*a^3 - 9//2*a # sqrt(2)
  y = 1//2*a^3 - 11//2*a # sqrt(3)
  O = order(K, [x, y, x*y])
  @test O == order(K, [x, y])
  @test O == order(K, [x, y], check = false)
  z = 1//4*a^3 + 1//4*a^2 + 3//4*a + 3//4
  OO = Hecke._order(K, [z], extends = O)
  @test is_maximal(OO)
  @test_throws ErrorException order(K, [x])
end


@testset "Order - Misc" begin
  k, a = cyclotomic_field(11)
  zk = maximal_order(k)
  lp = prime_ideals_over(zk, 23)
  p1 = lp[1]
  p2 = lp[2]
  p1.gen_two *= zk(a+1)
  p2.gen_two *= zk(a+1)

  @test p1 != p2
end



