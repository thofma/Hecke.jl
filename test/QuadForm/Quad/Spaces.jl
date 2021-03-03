@testset "Spaces" begin
  k = FlintQQ

  Qx, x = PolynomialRing(FlintQQ, "x")
  K1, a1 = NumberField(x^2 - 2, "a1")
  K2, a2 = NumberField(x^3 - 2, "a2")

  K1t, t = PolynomialRing(K1, "t")
  F = GF(3)

  Hecke.change_base_ring(::FlintRationalField, ::Hecke.gfp_mat) = error("asd")
  @test_throws ErrorException quadratic_space(FlintQQ, F[1 2; 2 1])

  Hecke.change_base_ring(::FlintRationalField, x::Hecke.gfp_mat) = x
  @test_throws ErrorException quadratic_space(FlintQQ, F[1 2; 2 1])

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

    # Determinant & discrimimant

    V = quadratic_space(K, 2)
    @test (@inferred discriminant(V)) == -1
    @test (@inferred det(V)) == 1

    V = quadratic_space(K, 4)
    @test (@inferred discriminant(V)) == 1
    @test (@inferred det(V)) == 1

    M = identity_matrix(K, 2)
    M[1, 2] = 2
    M[2, 1] = 2
    V = quadratic_space(K, M)
    @test (@inferred discriminant(V)) == 3
    @test (@inferred det(V)) == -3

    # Gram matrix

    M = identity_matrix(K, 2)
    M[1, 2] = 2
    M[2, 1] = 2
    V = @inferred quadratic_space(K, M)
    N = zero_matrix(K, 4, 2)
    @test (@inferred gram_matrix(V, N)) == zero_matrix(K, 4, 4)

    N = identity_matrix(QQ, 2)
    @test (@inferred gram_matrix(V, N)) == M

    N = zero_matrix(K, 4, 4)
    @test_throws ArgumentError gram_matrix(V, N)

    v = [[1, 0], [0, 1]]
    @test (@inferred gram_matrix(V, v) == M)

    v = [[1, 0, 0], [0, 1]]
    @test_throws ErrorException gram_matrix(V, v)

    B = @inferred orthogonal_basis(V)
    @test isdiagonal(gram_matrix(V, B))

    D = @inferred diagonal(V)
    @test length(D) == 2
    @test issetequal(D, map(K, [1, -3]))

    M = rand(MatrixSpace(K, 4, 4), -10:10)
    M = M + transpose(M)
    while iszero(det(M))
      M = rand(MatrixSpace(K, 4, 4), -10:10)
      M = M + transpose(M)
    end

    V = quadratic_space(K, M)

    F, S = @inferred Hecke._gram_schmidt(M, identity)
    @test gram_matrix(V, S) == F

    M[1, 1] = 0
    M[1, 2] = 0
    M[1, 3] = 0
    M[1, 4] = 0
    M[2, 1] = 0
    M[3, 1] = 0
    M[4, 1] = 0

    V = quadratic_space(K, M)

    @test_throws ErrorException Hecke._gram_schmidt(M, identity)
    F, S = @inferred Hecke._gram_schmidt(M, identity, false)
    @test gram_matrix(V, S) == F
  end

  fl, T =  Hecke.isequivalent_with_isometry(quadratic_space(QQ, matrix(QQ, 2, 2, [4, 0, 0, 1])),
                                            quadratic_space(QQ, matrix(QQ, 2, 2, [1, 0, 0, 1])))
  @test fl
end
