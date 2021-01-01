@testset "Spaces" begin
  k = FlintQQ

  Qx, x = PolynomialRing(FlintQQ, "x")
  K1, a1 = NumberField(x^2 - 2, "a1")
  K2, a2 = NumberField(x^3 - 2, "a2")

  K1t, t = PolynomialRing(K1, "t")

  L, b = NumberField(t^2 + a1)

  for K in [k, K1, K2, L]
    V = @inferred quadratic_space(K, 2)
    @test_throws ArgumentError quadratic_space(K, -1)

    V = @inferred quadratic_space(K, identity_matrix(FlintZZ, 2))
    @test (@inferred gram_matrix(V)) == identity_matrix(K, 2)
    @test (@inferred dim(V)) == 2
    @test (@inferred rank(V)) == 2
    @test @inferred isregular(V)
    @test (@inferred involution(V)) === identity

    V = @inferred quadratic_space(K, zero_matrix(K, 2, 2))
    @test (@inferred gram_matrix(V)) == zero_matrix(K, 2, 2)
    @test (@inferred gram_matrix(V)) isa dense_matrix_type(K)
    @test (@inferred dim(V)) == 2
    @test (@inferred rank(V)) == 0
    @test @inferred isquadratic(V)
    @test @inferred !ishermitian(V)
    @test (@inferred fixed_field(V)) === K

    @test_throws ArgumentError quadratic_space(K, zero_matrix(K, 1, 2))

    M = identity_matrix(K, 2)
    M[1, 2] = 2
    M[2, 1] = 1
    @test_throws ArgumentError quadratic_space(K, M)
  end

end
