@testset "NumField/Elem" begin
  k = wildanger_field(3, 13)[1]
  c = cyclotomic_field(3)[1]
  q = quadratic_field(17)[1]

  @testset for K in [k, c, q]
    R, x = polynomial_ring(K, 3)

    f = sum(x)^2
    g = sum(x) * sum(t+2 for t = x)
    h = sum(x)

    @test gcd(f,g) == h

    @test isone(gcd(f+1,g))

  end

  # test non-integral defining equation
  Qx, x = QQ["x"]
  K, a = number_field(x^2 - 1//3*x + 1);
  R, (u, v) = polynomial_ring(K, ["u", "v"])
  @test gcd(a*u, a*u) == u
  @test is_one(gcd(a*u, a^2*v))
end
