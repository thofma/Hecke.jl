@testset "Native finite-field embeddings" begin
  for (F, K) in ((Native.finite_field(3, 2)[1], Native.finite_field(3, 4)[1]),
                 (Native.finite_field(ZZ(3), 2)[1], Native.finite_field(ZZ(3), 4)[1]))
    a = first(roots(K, defining_polynomial(F)))
    m = hom(F, K, a)

    for x in F
      @test preimage(m, m(x)) == x
      @test m(x + one(F)) == m(x) + one(K)
      @test m(x * gen(F)) == m(x) * a
    end
    @test m(gen(F)) == a
    @test_throws ErrorException preimage(m, gen(K))
    @test_throws AssertionError hom(F, K, zero(K))
  end
end
