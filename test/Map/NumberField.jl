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

