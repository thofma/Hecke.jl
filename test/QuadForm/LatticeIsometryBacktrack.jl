@testset "Vanilla partition lattice isometry backtracking" begin
  G = ZZ[2 1 0; 1 2 1; 0 1 3]
  L = integer_lattice(gram = G)
  C = Hecke.LatticeIsometryBacktrackCtx(
    Matrix{Int}(G), maximum(Int(G[i, i]) for i in 1:3),
  )
  @test eltype(first(C.vectors)) === Int
  @test eltype(first(C.gram_products)[1]) === Int
  @test eltype(C.norms) === Vector{Int}

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

  N = ZZ(2)^50
  large_gram = matrix(ZZ, 2, 2, [N, 1, 1, N + 1])
  large_lattice = integer_lattice(gram = large_gram)
  @test automorphism_group_order(large_lattice; algorithm = :backtrack_vanilla) == 2
end

@testset "Simultaneous vanilla partition backtracking" begin
  I3 = [1 0 0; 0 1 0; 0 0 1]
  D = [1 0 0; 0 2 0; 0 0 3]
  E12 = [0 1 0; 1 0 0; 0 0 0]
  E23 = [0 0 0; 0 0 1; 0 1 0]
  E13 = [0 0 1; 0 0 0; 1 0 0]
  grams = [I3, D, E12, E23]
  X = [1 1 0; 0 1 1; 0 0 1]

  # Successive forms first distinguish coordinates, then constrain their signs.
  # In particular, the third and fourth forms must not be ignored.
  for (k, expected_order) in enumerate([48, 8, 4, 2])
    G = grams[1:k]
    # The context and partition types do not depend on the number of forms.
    C = Hecke.LatticeIsometryBacktrackCtx(G, 1)
    @test typeof(C) === Hecke.LatticeIsometryBacktrackCtx
    @test eltype(C.norms) === Vector{Int}
    @test all(norm -> length(norm) == k, C.norms)
    fingerprint = Hecke._lattice_backtrack_fingerprint(C)
    @test typeof(fingerprint) === Hecke.LatticeBacktrackFingerprint
    @test eltype(fingerprint.refinements) === Hecke.LatticeBacktrackRefinement
    generators, group_order = Hecke._lattice_backtrack_automorphism_group(G)
    @test group_order == expected_order
    @test all(M -> all(g -> M * g * transpose(M) == g, G), generators)
    H = [X * g * transpose(X) for g in G]
    for (source, target) in ((G, H), (H, G))
      M = Hecke._lattice_backtrack_isometry(source, target)
      @test M !== nothing
      if M !== nothing
        @test abs(det(matrix(ZZ, M))) == 1
        @test all(i -> M * target[i] * transpose(M) == source[i], 1:k)
      end
    end
  end

  # All additional forms are singular and indefinite, with zero diagonal.
  # Norms alone cannot detect the incompatible sign on the final pairing.
  G = [I3, E12, E23, E13]
  H = [I3, E12, E23, -E13]
  generators, group_order = Hecke._lattice_backtrack_automorphism_group(G)
  @test group_order == 2
  @test all(M -> all(g -> M * g * transpose(M) == g, G), generators)
  @test Hecke._lattice_backtrack_isometry(G, H) === nothing
  @test Hecke._lattice_backtrack_isometry([I3, E13], [I3, -E13]) !== nothing

  C = Hecke.LatticeIsometryBacktrackCtx(G, 2)
  @test eltype(first(C.vectors)) === Int
  @test eltype(C.norms) === Vector{Int}
  @test all(wGs -> all(wG -> eltype(wG) === Int, wGs), C.gram_products)
  @test all(C.norms[i] == [transpose(C.vectors[i]) * g * C.vectors[i] for g in G]
            for i in eachindex(C.vectors))
  @test all(Hecke._lattice_backtrack_pairing(C, i, j) ==
            [transpose(C.vectors[i]) * g * C.vectors[j] for g in G]
            for i in eachindex(C.vectors), j in eachindex(C.vectors))
  target = Hecke.LatticeIsometryBacktrackCtx(H, 2)
  @test Hecke._lattice_backtrack_histogram(C) == Hecke._lattice_backtrack_histogram(target)

  # Forms are preserved in order, not up to a permutation or individual signs.
  @test Hecke._lattice_backtrack_isometry([I3, D, -D], [I3, -D, D]) === nothing
  @test Hecke._lattice_backtrack_isometry([I3, zeros(Int, 3, 3)], [I3, E12]) === nothing
  @test Hecke._lattice_backtrack_automorphism_group([I3, zeros(Int, 3, 3)])[2] == 48
  @test Hecke._lattice_backtrack_isometry([I3], [2 * I3]) === nothing
  @test Hecke._lattice_backtrack_isometry([I3], [I3, D]) === nothing
  @test Hecke._lattice_backtrack_isometry([I3], [ones(Int, 1, 1)]) === nothing

  # A proper finite-index inclusion can preserve the entire short-vector set.
  # Here adjoining half the sum of the five basis vectors adds no vectors of
  # norm <= 4.  The determinant check must rule out a non-unimodular solution.
  S = 4 * Matrix{Int}(identity_matrix(ZZ, 5))
  T = copy(S)
  T[1, :] .= 2
  T[:, 1] .= 2
  T[1, 1] = 5
  source = Hecke.LatticeIsometryBacktrackCtx([S, S], 4)
  target = Hecke.LatticeIsometryBacktrackCtx([T, T], 4)
  @test Hecke._lattice_backtrack_histogram(source) == Hecke._lattice_backtrack_histogram(target)
  @test Hecke._lattice_backtrack_isometry([S, S], [T, T]) === nothing

  @test_throws ArgumentError Hecke._lattice_backtrack_automorphism_group(Matrix{Int}[])
  @test_throws ArgumentError Hecke._lattice_backtrack_isometry(Matrix{Int}[], Matrix{Int}[])
  @test_throws ArgumentError Hecke._lattice_backtrack_automorphism_group([I3, zeros(Int, 2, 2)])
  @test_throws ArgumentError Hecke._lattice_backtrack_automorphism_group([ones(Int, 2, 3)])
  @test_throws ArgumentError Hecke._lattice_backtrack_automorphism_group([I3, [1 1 0; 0 1 0; 0 0 1]])
  @test_throws ArgumentError Hecke._lattice_backtrack_automorphism_group([E12, I3])
  @test_throws ArgumentError Hecke._lattice_backtrack_automorphism_group([-I3, D])

  for n in 0:1
    G = [ones(Int, n, n), -ones(Int, n, n)]
    generators, group_order = Hecke._lattice_backtrack_automorphism_group(G)
    @test group_order == 2^n
    @test all(M -> all(g -> M * g * transpose(M) == g, G), generators)
    M = Hecke._lattice_backtrack_isometry(G, G)
    @test M !== nothing
    if M !== nothing
      @test all(g -> M * g * transpose(M) == g, G)
    end
  end
end
