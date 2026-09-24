@testset "generators and rank" begin
  M = Hecke.embedded_module(ZZ, QQ, QQ[1//2 0; 0 3; 3//2 0])

  @test rank(M) == 2
  @test basis_matrix(M) == QQ[1//2 0; 0 3]
  @test QQFieldElem[5//2, -6] in M
  @test !(QQFieldElem[1//4, 0] in M)

  N = Hecke.embedded_module(ZZ, QQ, QQ[2 0 0; 0 3 0])
  @test rank(N) == 2
  @test Hecke.ambient_rank(N) == 3
  @test !Hecke.has_full_rank(N)
  @test QQFieldElem[4, 6, 0] in N
  @test !(QQFieldElem[4, 6, 1] in N)
  @test !(QQFieldElem[1, 3, 0] in N)

  P = Hecke.embedded_module(ZZ, QQ, QQ[4 0 0; 0 6 0])
  @test issubset(P, N)
  @test Hecke.index(P, N) == 4
  @test N + P == N
  @test intersect(N, P) == P
end

@testset "cached data and coordinates" begin
  B = QQ[2 0; 0 3]
  Binv = QQ[1//2 0; 0 1//3]
  M = Hecke.embedded_module(ZZ, QQ, B; is_basis_matrix = true, inverse = Binv)

  @test basis_matrix(M) === B
  @test basis_matrix_inverse(M) === Binv
  @test Hecke.basis_matrix_numerator(M) == ZZ[2 0; 0 3]
  @test Hecke.index_multiple(M) == 6

  fl, c = Hecke._in(QQFieldElem[2, 3], M, Val(true))
  @test fl
  @test c == ZZRingElem[1, 1]

  N = Hecke.embedded_module(ZZ, QQ, QQ[2 0; 0 3])
  fl, c = Hecke._in(QQFieldElem[1, 0], N, Val(true))
  @test !fl
  @test c == ZZRingElem[1, 0]

  P = Hecke.embedded_module(ZZ, QQ, QQ[2 0 0; 0 3 0])
  fl, c = Hecke._in(QQFieldElem[0, 0, 1], P, Val(true))
  @test !fl
  @test c == ZZRingElem[0, 0, 0]

  fl, C = Hecke._in(QQ[0 0 1], P, Val(true))
  @test !fl
  @test C == zero_matrix(ZZ, 1, 2)
  @test !Hecke._in(QQ[0 0 1], P)

  fl, C = Hecke._in(QQ[4 0; 0 6], M, Val(true))
  @test fl
  @test C == ZZ[2 0; 0 2]

  T = Hecke._tmp_mat_overring(M, 3)
  @test size(T) == (3, 2)
  @test size(Hecke._tmp_mat_overring(M, 2)) == (2, 2)

  H = Hecke.embedded_module(ZZ, QQ, QQ[4 0; 0 6; 8 0])
  H.index_multiple = ZZ(24)
  @test Hecke.basis_matrix_numerator(H) == ZZ[4 0; 0 6]
end

@testset "zero module" begin
  M = Hecke.zero_embedded_module(ZZ, QQ, 3)

  @test rank(M) == 0
  @test Hecke.ambient_rank(M) == 3
  @test !Hecke.has_full_rank(M)
  @test basis_matrix(M) == zero_matrix(QQ, 0, 3)
  @test QQFieldElem[0, 0, 0] in M
  @test !(QQFieldElem[0, 1, 0] in M)

  ambient = Ref(:ambient)
  Z = Hecke.embedded_module(ZZ, QQ, zero_matrix(QQ, 0, 2);
                            overstructure = ambient, is_basis_matrix = true)
  N = Hecke.embedded_module(ZZ, QQ, QQ[1 0]; overstructure = ambient)

  @test intersect(Z, N) == Z

  M1 = Hecke.embedded_module(ZZ, QQ, QQ[1 0]; overstructure = ambient)
  M2 = Hecke.embedded_module(ZZ, QQ, QQ[0 1]; overstructure = ambient)
  @test intersect(M1, M2) == Z
end
