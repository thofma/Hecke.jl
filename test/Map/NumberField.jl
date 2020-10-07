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
end
