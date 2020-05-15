@testset "NumField/Elem" begin
  k = wildanger_field(3, 13)[1]
  c = cyclotomic_field(3)[1]
  q = quadratic_field(17)[1]

  @testset for K in [k, c, q]
    R, x = PolynomialRing(K, 3)

    f = sum(x)^2
    g = sum(x) * sum(t+2 for t = x)
    h = sum(x)

    @test gcd(f,g) == h

    @test isone(gcd(f+1,g))

  end
end


