@testset "Ideals under maps" begin
  Qx, x = polynomial_ring(QQ, "x")

  @testset "Minimum" begin
    k, = number_field(x^2 - 2);
    K, = number_field(x^4 - 144 * x^2 - 7938);
    f = hom(k, K, 1//81 * gen(K)^2 - 8//9);
    P = prime_decomposition(maximal_order(K), 7)[1][1]
    mP = minimum(f, P)
    @test norm(mP) == 7
  end
end
