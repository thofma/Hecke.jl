@testset "ZZ-modules in QQ^n" begin
  ambient = nothing
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
  @test module_index(N, M) == ideal(ZZ, 4)

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

  N_incompatible = Hecke.embedded_module(ZZ, QQ, QQ[4 0 0; 0 6 0])
  @test !Hecke.is_compatible(M, N_incompatible)
  @test_throws ArgumentError M + N_incompatible
  @test_throws ArgumentError issubset(N_incompatible, M)
end

@testset "PID hashing independent of the basis" begin
  F, t = rational_function_field(GF(7), "t")
  Rinf = localization(F, degree)
  for (R, K, u, a) in ((ZZ, QQ, ZZ(-1), QQ(1//2)),
                        (parent(numerator(t)), F, parent(numerator(t))(3), inv(t)),
                        (Rinf, F, Rinf(t/(t + 1)), t))
    for B in (matrix(K, 1, 1, [a]), K[a 0; 0 3],
              K[a 1 0; 0 3 1], zero_matrix(K, 0, 3))
      U = identity_matrix(R, nrows(B))
      if nrows(B) > 0
        U[1, 1] = u
      end
      if nrows(B) > 1
        U[1, 2] = one(R)
      end
      C = change_base_ring(K, U)*B
      original_B, original_C = deepcopy(B), deepcopy(C)
      M = Hecke.embedded_module(R, K, B; is_basis_matrix = true)
      N = Hecke.embedded_module(R, K, C; is_basis_matrix = true)
      P = Hecke.embedded_module(R, K, deepcopy(B))
      @test M == N == P
      @test (@inferred module_index(N, M)) == ideal(R, one(R))
      @test gen(module_index(N, M)) == one(R)
      @test (@inferred hash(M)) == hash(N) == hash(P)
      @test hash(M, UInt(42)) == hash(N, UInt(42))
      @test length(Set([M, N, P])) == 1
      @test Dict(M => 1)[N] == 1
      @test basis_matrix(M) == original_B
      @test basis_matrix(N) == original_C
      @test hash(M) == hash(N)
    end
  end
end
