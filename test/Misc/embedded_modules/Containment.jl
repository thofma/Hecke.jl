@testset "ZZ-modules in QQ^n" begin
  ambient = Ref(:ambient)
  M = Hecke.embedded_module(ZZ, QQ, ZZ[2 0; 0 3]; overstructure = ambient)

  @test Hecke.ring(M) === ZZ
  @test Hecke.overring(M) === QQ
  @test Hecke.overstructure(M) === ambient
  @test Hecke.ambient_rank(M) == 2
  @test base_ring(Hecke.generator_matrix(M)) === QQ
  @test rank(M) == 2
  @test Hecke.has_full_rank(M)
  @test basis_matrix(M) == QQ[2 0; 0 3]
  @test Hecke.basis_matrix_components(M) == (ZZ[2 0; 0 3], ZZ(1))

  @test QQFieldElem[2, 3] in M
  @test QQFieldElem[4, -6] in M
  @test !(QQFieldElem[1, 3] in M)
  @test !(QQFieldElem[2, 1] in M)

  # Exercise the membership path using a cached inverse as well.
  @test basis_matrix_inverse(M) == QQ[1//2 0; 0 1//3]
  @test QQFieldElem[2, 3] in M
  @test !(QQFieldElem[1, 3] in M)

  N = Hecke.embedded_module(ZZ, QQ, QQ[4 0; 0 6]; overstructure = ambient)
  @test issubset(N, M)
  @test Hecke.index(N, M) == 4

  P = Hecke.embedded_module(ZZ, QQ, QQ[1 0; 0 3]; overstructure = ambient)
  @test !issubset(P, M)

  Q = Hecke.embedded_module(ZZ, QQ, QQ[4 0; 0 6];
                            overstructure = ambient, is_basis_matrix = true)
  @test issubset(Q, M)

  L = Hecke.embedded_module(ZZ, QQ, QQ[1 0; 0 6]; overstructure = ambient)
  @test Hecke.is_compatible(M, L)
  @test M + L == Hecke.embedded_module(ZZ, QQ, QQ[1 0; 0 3]; overstructure = ambient)
  @test intersect(M, L) == Hecke.embedded_module(ZZ, QQ, QQ[2 0; 0 6]; overstructure = ambient)
  @test hash(intersect(M, L)) == hash(Hecke.embedded_module(ZZ, QQ, QQ[2 0; 0 6]; overstructure = ambient))

  N_incompatible = Hecke.embedded_module(ZZ, QQ, QQ[4 0; 0 6])
  @test !Hecke.is_compatible(M, N_incompatible)
  @test_throws ArgumentError M + N_incompatible
  @test_throws ArgumentError issubset(N_incompatible, M)
end
