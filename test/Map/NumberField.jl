@testset "Test composition order" begin
  Qx, x = FlintQQ["x"]
  K, a = NumberField(x^6 + 108, "a")
  A = automorphisms(K)
  for f in A
    for g in A
      @test g(f(a)) == compose(f, g)(a)
      @test g(f(a)) == (f * g)(a)
    end
  end
end

@testset "Induce image" begin
  Qx, x = FlintQQ["x"]
  K, a = NumberField(x^6 + 108, "a")
  A = automorphisms(K)
  OK = maximal_order(K)
  lP = prime_decomposition(OK, 7)
  lP1 = [x[1] for x in lP]
  for i = 1:length(lP)
    I_new = A[2](lP1[1])
    id = findfirst(isequal(I_new), lP1)
    @test id != nothing 
  end
  f = hom(K, K, a^4//12+a//2)
  E = EquationOrder(K)
  I = ideal(E, E(a))
  @test_throws ErrorException Hecke.induce_image(f, I) 

end


@testset "Automorphisms" begin
  Qx, x = FlintQQ["x"]
  f = x^32 - 217*x^28 + 42321*x^24 - 999502*x^20 + 18913054*x^16 - 80959662*x^12 + 277668081*x^8 - 115322697*x^4 + 43046721
  K, a = number_field(f, cached = false, check = false)
  auts = Hecke._automorphisms(K, isabelian = true)
  auts1 = Hecke._automorphisms(K)
  @test Set(auts) == Set(auts1)

  f = x^4 + 4*x^2 + 2
  K, a = number_field(f, cached = false, check = false)
  G, mG = automorphism_group(K)
  @test order(G) == 4
  fl, tau = Hecke.iscm_field(K)
  @test fl
end

@testset "CM" begin
  Qx, x = FlintQQ["x"]
  f = x^20 + 6*x^19 + 33*x^18 + 109*x^17 + 332*x^16 + 706*x^15 + 1299*x^14 + 1910*x^13 + 3303*x^12 + 7116*x^11 + 14445*x^10 + 24009*x^9 + 30102*x^8 + 37094*x^7 + 54187*x^6 + 82991*x^5 + 119418*x^4 + 148247*x^3 + 185442*x^2 + 184250*x + 112225
x^20 + 6*x^19 + 33*x^18 + 109*x^17 + 332*x^16 + 706*x^15 + 1299*x^14 + 1910*x^13 + 3303*x^12 + 7116*x^11 + 14445*x^10 + 24009*x^9 + 30102*x^8 + 37094*x^7 + 54187*x^6 + 82991*x^5 + 119418*x^4 + 148247*x^3 + 185442*x^2 + 184250*x + 112225
  K, a = NumberField(f, "a", cached = false)
  G, mG = automorphism_group(K)
  @test order(center(G)[1]) == 2
  fl, tau = Hecke.iscm_field(K)
  @test fl
end
