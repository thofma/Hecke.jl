@testset "polynomial PID" begin
  K, x = rational_function_field(QQ, "x")
  R = parent(numerator(x))
  M = Hecke.embedded_module(R, K, K[x 0; 0 1])

  @test rank(M) == 2
  @test typeof(x)[x, x + 1] in M
  @test !(typeof(x)[K(1), K(0)] in M)
  @test !(typeof(x)[x, inv(x)] in M)

  N = Hecke.embedded_module(R, K, identity_matrix(K, 2))
  @test M + N == N
  @test intersect(M, N) == M
end

@testset "degree localization" begin
  K, x = rational_function_field(QQ, "x")
  R = localization(K, degree)
  M = Hecke.embedded_module(R, K, K[1//x 0; 0 1])

  @test Hecke.ring(M) === R
  @test Hecke.overring(M) === K
  @test basis_matrix(M) == K[1//x 0; 0 1]
  @test typeof(x)[inv(x), (x + 1)//x] in M
  @test typeof(x)[inv(x)^2, K(0)] in M
  @test !(typeof(x)[K(1), K(0)] in M)
  @test !(typeof(x)[inv(x), x] in M)

  N = Hecke.embedded_module(R, K, identity_matrix(K, 2))
  @test M + N == N
  @test intersect(M, N) == M
end
