@testset "Relative residue maps with polynomial representations" begin
  K, _ = rationals_as_number_field()
  Kt, t = polynomial_ring(K, "t")
  E, _ = number_field(t^2 - 20, "b")
  OK = maximal_order(K)
  OE = maximal_order(E)
  p = first(prime_ideals_over(OK, 2))
  P = first(prime_decomposition(OE, p))[1]

  # Scaling the generators by 2 makes both extensions have index divisors
  # above 2. Their residue degrees are 2 and 3, respectively.
  @test is_index_divisor(OE, p)
  mK = Hecke.NfOrdToFqMor(OK, p)
  mE = Hecke.NfRelOrdToRelFinFieldMor{typeof(OE), elem_type(codomain(mK))}(OE, P, mK)
  FE = codomain(mE)
  @test degree(FE) == 2
  @test base_field(FE) === codomain(mK)
  @test mE.map_subfield === mK

  Eu, u = polynomial_ring(E, "u")
  L, _ = number_field(u^3 + 4*u + 8, "c")
  OL = maximal_order(L)
  PP = first(prime_decomposition(OL, P))[1]
  @test is_index_divisor(OL, P)
  mL = Hecke.NfRelOrdToRelFinFieldMor{typeof(OL), elem_type(FE)}(OL, PP, mE)
  FL = codomain(mL)
  @test degree(FL) == 3
  @test absolute_degree(FL) == 6
  @test base_field(FL) === FE
  @test mL.map_subfield === mE
  for b in absolute_basis(OE)
    @test mL(OL(L(elem_in_nf(b)))) == FL(mE(b))
  end

  for (O, prime, projection) in ((OE, P, mE), (OL, PP, mL))
    F = codomain(projection)
    extended = extend(projection, Hecke.nf(O))
    @test domain(extended) === Hecke.nf(O)
    @test codomain(extended) === F
    for b in absolute_basis(O)
      @test preimage(projection, projection(b)) - b in prime
      @test extended(elem_in_nf(b)) == projection(b)
      @test extended(elem_in_nf(b)/3) == projection(b)/F(3)
    end
    for b in absolute_basis(O), c in absolute_basis(O)
      @test projection(b*c) == projection(b)*projection(c)
    end
    for coefficients in Iterators.product(ntuple(_ -> collect(base_field(F)), degree(F))...)
      y = F(parent(defining_polynomial(F))(collect(coefficients)))
      @test projection(preimage(projection, y)) == y
      @test extended(preimage(extended, y)) == y
    end
  end
end
