@testset "NumFieldOrd" begin
  x = PolynomialRing(FlintQQ, "x", cached = false)[2]
  K, a = number_field(x^2+1, check = false, cached = false)
  Kns, gKns = number_field([x^2+1], check = false, cached = false)
  Kt, t = PolynomialRing(K, "t", cached = false)
  L, b = number_field(t^2+3, "b", cached = false, check = false)
  Lns, gLns = number_field([t^2+3], cached = false, check = false)

  OK = maximal_order(K)
  @inferred nf(OK)
  @test is_simple(OK)
  @test is_commutative(OK)
  @test @inferred is_equation_order(OK)
  @test @inferred is_maximal(OK)
  @test @inferred degree(OK) == 2
  @test @inferred absolute_degree(OK) == 2
  BOK = absolute_basis(OK)
  @test @inferred discriminant(BOK) == @inferred discriminant(OK)
  @test @inferred signature(OK) == (0, 1)
  @test @inferred discriminant(OK, FlintQQ) == discriminant(OK)

  OKns = maximal_order(Kns)
  @inferred nf(OKns)
  @test !is_simple(OKns)
  @test is_commutative(OKns)
  @test @inferred !is_equation_order(OKns)
  @test @inferred is_maximal(OKns)
  @test @inferred degree(OKns) == 2
  @test @inferred absolute_degree(OKns) == 2
  BOKns = absolute_basis(OKns)
  @test @inferred discriminant(BOKns) == @inferred discriminant(OKns)
  @test @inferred signature(OKns) == (0, 1)
  @test @inferred discriminant(OKns, FlintQQ) == discriminant(OKns)

  OL = maximal_order(L)
  @inferred nf(OL)
  @test is_simple(OL)
  @test is_commutative(OL)
  @test @inferred !is_equation_order(OL)
  @test @inferred is_maximal(OL)
  @test @inferred degree(OL) == 2
  @test @inferred absolute_degree(OL) == 4
  BOL = absolute_basis(OL)
  @test numerator(det(trace_matrix(map(elem_in_nf, BOL)))) == @inferred absolute_discriminant(OL)
  @test @inferred signature(OL) == (0, 2)
  @test @inferred discriminant(OL, FlintQQ) == absolute_discriminant(OL)

  OLns = maximal_order(Lns)
  @inferred nf(OLns)
  @test !is_simple(OLns)
  @test is_commutative(OLns)
  @test @inferred !is_equation_order(OLns)
  @test @inferred is_maximal(OLns)
  @test @inferred degree(OLns) == 2
  @test @inferred absolute_degree(OLns) == 4
  BOLns = absolute_basis(OLns)
  @test numerator(det(trace_matrix(map(elem_in_nf, BOLns)))) == @inferred absolute_discriminant(OLns)
  @test @inferred signature(OLns) == (0, 2)
  @test @inferred discriminant(OLns, FlintQQ) == absolute_discriminant(OLns)

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
  @test degree(Hecke.absolute_field(FL)[1]) == 6
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

