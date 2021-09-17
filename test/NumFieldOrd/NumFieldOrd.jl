@testset "NumFieldOrd" begin
  x = PolynomialRing(FlintQQ, "x", cached = false)[2]
  K, a = number_field(x^2+1, check = false, cached = false)
  Kns, gKns = number_field([x^2+1], check = false, cached = false)
  Kt, t = PolynomialRing(K, "t", cached = false)
  L, b = number_field(t^2+3, "b", cached = false, check = false)
  Lns, gLns = number_field([t^2+3], cached = false, check = false)

  OK = maximal_order(K)
  @inferred nf(OK)
  @test issimple(OK)
  @test iscommutative(OK)
  @test @inferred isequation_order(OK)
  @test @inferred ismaximal(OK)
  @test @inferred degree(OK) == 2
  @test @inferred absolute_degree(OK) == 2
  BOK = absolute_basis(OK)
  @test @inferred discriminant(BOK) == @inferred discriminant(OK)
  @test @inferred signature(OK) == (0, 1)
  @test @inferred discriminant(OK, FlintQQ) == discriminant(OK)

  OKns = maximal_order(Kns)
  @inferred nf(OKns)
  @test !issimple(OKns)
  @test iscommutative(OKns)
  @test @inferred !isequation_order(OKns)
  @test @inferred ismaximal(OKns)
  @test @inferred degree(OKns) == 2
  @test @inferred absolute_degree(OKns) == 2
  BOKns = absolute_basis(OKns)
  @test @inferred discriminant(BOKns) == @inferred discriminant(OKns)
  @test @inferred signature(OKns) == (0, 1)
  @test @inferred discriminant(OKns, FlintQQ) == discriminant(OKns)

  OL = maximal_order(L)
  @inferred nf(OL)
  @test issimple(OL)
  @test iscommutative(OL)
  @test @inferred !isequation_order(OL)
  @test @inferred ismaximal(OL)
  @test @inferred degree(OL) == 2
  @test @inferred absolute_degree(OL) == 4
  BOL = absolute_basis(OL)
  @test numerator(det(trace_matrix(map(elem_in_nf, BOL)))) == @inferred absolute_discriminant(OL)
  @test @inferred signature(OL) == (0, 2)
  @test @inferred discriminant(OL, FlintQQ) == absolute_discriminant(OL)

  OLns = maximal_order(Lns)
  @inferred nf(OLns)
  @test !issimple(OLns)
  @test iscommutative(OLns)
  @test @inferred !isequation_order(OLns)
  @test @inferred ismaximal(OLns)
  @test @inferred degree(OLns) == 2
  @test @inferred absolute_degree(OLns) == 4
  BOLns = absolute_basis(OLns)
  @test numerator(det(trace_matrix(map(elem_in_nf, BOLns)))) == @inferred absolute_discriminant(OLns)
  @test @inferred signature(OLns) == (0, 2)
  @test @inferred discriminant(OLns, FlintQQ) == absolute_discriminant(OLns)



end