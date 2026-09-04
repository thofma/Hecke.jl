@testset "Plain lattice isometry backtracking" begin
  G = ZZ[2 1 0; 1 2 1; 0 1 3]
  L = integer_lattice(gram = G)

  generators = automorphism_group_generators(
    L; ambient_representation = false, algorithm = :backtrack_vanilla,
  )
  @test all(g -> g * gram_matrix(L) * transpose(g) == gram_matrix(L), generators)

  L_for_order = integer_lattice(gram = G)
  expected_order = automorphism_group_order(integer_lattice(gram = G))
  @test automorphism_group_order(L_for_order; algorithm = :backtrack_vanilla) ==
        expected_order

  X = ZZ[1 1 0; 0 1 1; 0 0 1]
  M = integer_lattice(gram = X * G * transpose(X))
  isometric, T = is_isometric_with_isometry(L, M; algorithm = :backtrack_vanilla)
  @test isometric
  @test T * gram_matrix(M) * transpose(T) == gram_matrix(L)

  L1 = integer_lattice(gram = QQ[126 16; 16 4])
  L2 = integer_lattice(gram = QQ[14 2; 2 18])
  @test !is_isometric(L1, L2; algorithm = :backtrack_vanilla)

  A2 = root_lattice(:A, 2)
  A2negative = rescale(root_lattice(:A, 2), -1)
  @test automorphism_group_order(A2; algorithm = :backtrack_vanilla) == 12
  @test automorphism_group_order(A2negative; algorithm = :backtrack_vanilla) == 12

  A2optimized = root_lattice(:A, 2)
  @test automorphism_group_order(A2optimized; algorithm = :backtrack) == 12

  N = ZZ(2)^70
  large_gram = matrix(ZZ, 2, 2, [N, 1, 1, N + 1])
  large_lattice = integer_lattice(gram = large_gram)
  @test automorphism_group_order(large_lattice; algorithm = :backtrack_vanilla) == 2
end
