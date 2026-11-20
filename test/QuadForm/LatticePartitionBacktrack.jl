import Random

@testset "Lattice partition backtrack" begin
  PB = Hecke.LatticePartitionBacktrack
  A2 = ZZ[2 -1; -1 2]
  D4 = ZZ[2 0 -1 0; 0 2 -1 0; -1 -1 2 -1; 0 0 -1 2]
  E8 = change_base_ring(ZZ, gram_matrix(root_lattice(:E, 8)))

  # The set of short vectors: up to sign, the vectors up to the smallest norm
  # for which they generate the lattice. It does not depend on the basis,
  # also if the vectors are enumerated up to different norms.
  S = PB.ShortVectors([E8])
  @test PB.number_of_vectors(S) == 120
  @test all(p -> PB.find_point(S, PB.coordinates(S, p)) == p, [1, -1, 120])
  @test PB.find_point(S, [2, 0, 0, 0, 0, 0, 0, 0]) == 0
  bases = [(ZZ[1 0 0 0; 0 2 -1 -1; 0 -1 2 0; 0 -1 0 2],
            ZZ[1 0 0 0; 0 1 -1 0; 0 0 1 0; 0 0 0 1]),
           (ZZ[1 0 0 0; 0 2 0 0; 0 0 3 -1; 0 0 -1 3],
            ZZ[1 0 0 0; 0 1 -2 0; 0 0 1 1; 0 0 0 1])]
  for (G, T) in bases
    @test PB.number_of_vectors(PB.ShortVectors([G])) ==
          PB.number_of_vectors(PB.ShortVectors([T * G * transpose(T)]))
  end

  # isometry
  r = ZZ[0 1; -1 -1]
  for (G, F) in [(D4, ZZ[0 1 0 0; -1 0 0 0; 0 0 0 1; 0 0 -1 0]), (E8, E8)]
    n = nrows(G)
    T = identity_matrix(ZZ, n)
    T[1, 2] = 1
    T[n, 1] = -1
    forms1 = G == F ? [G] : [G, F]
    forms2 = [T * A * transpose(T) for A in forms1]
    fl, M = PB.isometry(forms1, forms2)
    @test fl
    @test all(M * forms2[i] * transpose(M) == forms1[i]
              for i in 1:length(forms1))
  end
  @test !PB.isometry([D4], [identity_matrix(ZZ, 4)])[1]
  E7A1 = gram_matrix(direct_sum(root_lattice(:E, 7), root_lattice(:A, 1))[1])
  @test !PB.isometry([2 * E8], [2 * identity_matrix(ZZ, 8)])[1]
  @test !PB.isometry([E8], [change_base_ring(ZZ, E7A1)])[1]
  @test !PB.isometry([A2, ZZ[0 1; -1 0]], [A2, ZZ[0 2; -2 0]])[1]

  # labels together with isometry: the isometry respects a vector, which is
  # given by its scalar products with the short vectors
  V = PB.enumerate_vectors(D4)
  w = ZZ[1 0 0 0] * D4
  T = identity_matrix(ZZ, 4)
  T[1, 2] = 1
  T[4, 1] = -1
  H = T * D4 * transpose(T)
  V2 = PB.enumerate_vectors(H)
  labels2 = Int[Int((w * transpose(matrix(ZZ, 1, 4, v) * T))[1, 1]) for v in V2]
  labels1 = Int[Int((w * matrix(ZZ, 4, 1, v))[1, 1]) for v in V]
  fl, M = PB.isometry([D4], [H], [(v, 0) for v in V], [(v, 0) for v in V2],
                      labels1, labels2)
  @test fl && M * H * transpose(M) == D4
  @test ZZ[1 0 0 0] * (M * T) == ZZ[1 0 0 0]
  labels2[1] += 1
  @test !PB.isometry([D4], [H], [(v, 0) for v in V], [(v, 0) for v in V2],
                     labels1, labels2)[1]

  # automorphism groups: compare generators and group order with known
  # automorphism group orders
  L0 = integer_lattice(; gram = zero_matrix(ZZ, 0, 0))
  gens, order = PB.automorphism_group(L0)
  @test order == 1

  lattices = [(root_lattice(:A, 1), 2),
              (root_lattice(:A, 2), 12),
              (root_lattice(:D, 4), 1152),
              (root_lattice(:E, 6), 103680),
              (root_lattice(:E, 8), 696729600),
              (rescale(root_lattice(:A, 3), -1//3), 48),
              (integer_lattice(; gram = ZZ[2 1 0; 1 4 1; 0 1 6]), 4),
              (direct_sum(root_lattice(:E, 7), root_lattice(:A, 5))[1],
               4180377600)]
  for (L, expected) in lattices
    gens, order = PB.automorphism_group(L)
    G = gram_matrix(L)
    @test order == expected
    @test all(g -> g * G * transpose(g) == G, gens)
  end

  # the chain data is consistent and the generators generate the whole group
  chain = PB.stabilizer_chain(PB.ShortVectors([D4]))
  @test prod(chain.orbit_lengths) == chain.order == 1152
  @test length(closure(matrix.(Ref(ZZ), chain.generators), *)) == 1152

  # without the table of scalar products
  @test PB.automorphism_group([E8]; cache_max_bytes = 0)[2] == 696729600
  S = PB.ShortVectors([D4]; cache_max_bytes = 0)
  @test PB.stabilizer_chain(S).nodes == chain.nodes

  # entries which do not fit into machine integers
  gens, order = PB.automorphism_group([ZZ(2)^70 * D4])
  @test order == 1152
  @test all(g -> g * D4 * transpose(g) == D4, gens)

  # several forms, also skew-symmetric and asymmetric ones: the centralizer
  # of a rotation of order 3 in the automorphism group of A2 has order 6
  for F in [ZZ[0 1; -1 0], r * A2]
    gens, order = PB.automorphism_group([A2, F])
    @test order == 6
    @test all(g -> g * A2 * transpose(g) == A2, gens)
    @test all(g -> g * F * transpose(g) == F, gens)
  end

  # labels: the stabilizer of a vector, given by its scalar products with
  # the short vectors; -1 is not in the group
  labels = Int[Int((w * matrix(ZZ, 4, 1, v))[1, 1]) for v in V]
  gens, order = PB.automorphism_group([D4], [(v, 0) for v in V], labels)
  @test order == 48
  @test all(g -> g * D4 * transpose(g) == D4, gens)
  @test all(g -> ZZ[1 0 0 0] * g == ZZ[1 0 0 0], gens)

  # labels together with a form which is not symmetric
  labels = Int[v[1] for v in PB.enumerate_vectors(A2)]
  vector_set = [(v, 0) for v in PB.enumerate_vectors(A2)]
  @test PB.automorphism_group([A2, r * A2])[2] == 6
  @test PB.automorphism_group([A2, r * A2], vector_set, labels)[2] == 1
  @test PB.automorphism_group([A2], vector_set, labels)[2] == 2

  # a unimodular lattice without roots; all 928 minimal vectors look alike
  # until scalar products inside the cells are taken into account
  X29 = matrix(ZZ, 29, 29, [
      3, 1, 1, 1, 1, 1, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, 1, 0, 1, 1, 3, -1, 1, 0, 1, 0, 0, 0, 1, 0, 0, -1, 0,
      0, 0, 1, 0, -1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, -1, 3, 1, 0, 0,
      1, 0, -1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0,
      0, 1, 1, 1, 1, 3, 1, 0, 1, 0, -1, 0, 1, 0, 0, -1, -1, 1, 1, 0, 0,
      0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 3, 1, 1, 0, 1, 0, 1, -1,
      -1, -1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0,
      1, 3, 1, 1, 1, 0, 1, 0, -1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0,
      1, 0, 0, 0, 0, 1, 1, 1, 1, 3, 0, 0, -1, 1, 0, 0, 0, 1, 0, 0, 1, 0,
      1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 3, 1, 0, 0, 1,
      0, -1, 0, 1, 1, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1,
      1, 1, 0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0,
      1, 0, 0, 1, 1, 0, 0, 0, 0, -1, 0, 1, 3, 0, 0, 0, 0, -1, 0, 0, 1,
      0, 0, 0, 1, -1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 3,
      0, -1, -1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, -1, 0, 0, 1,
      0, -1, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0,
      0, 0, 1, 0, 0, 0, -1, 1, 0, -1, -1, 0, 0, 0, 0, -1, 0, 3, 1, 0, 0,
      0, 0, 0, 0, 0, -1, 0, 1, -1, 0, 0, 0, 1, 0, 0, 0, -1, -1, 0, 0,
      -1, 0, 0, -1, 0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1,
      1, 0, 0, 0, -1, 0, 1, 1, 0, 0, -1, 0, 0, 0, 1, 3, 0, -1, 0, 0, 0,
      -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 3, 0, 0, 0, 1, 0, 1, -1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1,
      0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, -1, 1,
      0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, -1, 0, 0, 0, 0, 0, 3, 0, 1,
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0, 0, 0, 0, 3, 0, 1, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1,
      1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, -1, 0, 0, 1, 1, 0, 0, 0,
      1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 1, 0, 1, -1,
      3, 0, 1, -1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0,
      -1, 0, 0, 1, 0, 0, 0, 0, 0, 3, -1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0,
      0, 0, 1, -1, 0, -1, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 1, -1, 3, -1,
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      0, -1, 1, -1, 0, -1, 3, 1, 0, 0, -1, 0, 0, 1, -1, 0, 0, 1, 0, 0,
      0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 3, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0,
      0, 0, 3, -1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0,
      1, 0, 0, 0, 0, 1, 0, 0, 0, -1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, -1, 0, 0, 0, 3, 0, 1, 0,
      1, 0, 0, 0, 0, 0, 0, 1, -1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 3])
  gens, order = PB.automorphism_group(integer_lattice(; gram = X29))
  @test order == 232
  @test all(g -> g * X29 * transpose(g) == X29, gens)

  # with a table of scalar products which is too small for all vectors
  S = PB.ShortVectors([X29]; cache_max_bytes = 2^14)
  @test PB.stabilizer_chain(S).order == 232
  tabulated = count(table -> !isempty(table.sets), S.tables)
  @test 0 < tabulated < PB.number_of_vectors(S)

  # bases with a long vector: the short vectors and the base do not depend
  # on the basis, and the base is not the standard basis
  for G in [D4, E8, X29]
    n = nrows(G)
    T = identity_matrix(ZZ, n)
    T[n, 1:(n - 1)] = [3 * (-1)^j for j in 1:(n - 1)]
    H = T * G * transpose(T)
    S = PB.ShortVectors([H])
    @test PB.number_of_vectors(S) == PB.number_of_vectors(PB.ShortVectors([G]))
    @test PB.find_point(S, [j == n ? 1 : 0 for j in 1:n]) == 0
    @test length(PB.Reference(S).sequence) >= n
    gens, order = PB.automorphism_group([H])
    @test order == PB.automorphism_group([G])[2]
    @test all(g -> g * H * transpose(g) == H, gens)
    fl, M = PB.isometry([G], [H])
    @test fl && M * H * transpose(M) == G
    fl, M = PB.isometry([H], [G])
    @test fl && M * G * transpose(M) == H
  end

  @test_throws ArgumentError PB.automorphism_group(hyperbolic_plane_lattice())

  # canonical forms: they do not depend on the basis, they are isometric to
  # the given forms, and they tell lattices apart
  rng = Random.MersenneTwister(1)
  function another_basis(n)
    U = identity_matrix(ZZ, n)
    for _ in 1:(3 * n)
      E = identity_matrix(ZZ, n)
      i, j = rand(rng, 1:n), rand(rng, 1:n)
      i != j && (E[i, j] = rand(rng, -2:2))
      U = E * U
    end
    return U
  end
  D4D4 = block_diagonal_matrix([D4, D4])
  for forms in [[A2], [D4], [E8], [D4D4], [X29], [A2, r * A2],
                [ZZ[2 1 0; 1 4 1; 0 1 6]], [ZZ(2)^70 * A2]]
    canonical, T = PB.canonical_form(forms)
    @test abs(det(T)) == 1
    @test [T * F * transpose(T) for F in forms] == canonical
    W = another_basis(nrows(forms[1]))
    @test PB.canonical_form([W * F * transpose(W) for F in forms])[1] ==
          canonical
  end
  @test PB.canonical_form([E8])[1] != PB.canonical_form([D4D4])[1]
  @test PB.canonical_form([A2, r * A2])[1] !=
        PB.canonical_form([A2, transpose(r) * A2])[1]

  # the Leech lattice: here the canonical form relies on the automorphism
  # group, which is computed first
  Leech = change_base_ring(ZZ, gram_matrix(leech_lattice()))
  canonical, T = PB.canonical_form([Leech])
  @test T * Leech * transpose(T) == canonical[1]
  W = -identity_matrix(ZZ, 24)[24:-1:1, :]
  @test PB.canonical_form([W * Leech * transpose(W)])[1] == canonical

  # bases in which the vectors are enumerated up to different norms
  for (G, T) in bases
    @test PB.canonical_form([G])[1] ==
          PB.canonical_form([T * G * transpose(T)])[1]
  end

  # canonical forms of a lattice with a labelled set of vectors: the labels
  # single out a vector
  canonical, T = PB.canonical_form([D4], [(v, 0) for v in V], labels1)
  W = another_basis(4)
  H = W * D4 * transpose(W)
  V2 = PB.enumerate_vectors(H)
  labels2 = Int[Int((w * transpose(matrix(ZZ, 1, 4, v) * W))[1, 1]) for v in V2]
  @test PB.canonical_form([H], [(v, 0) for v in V2], labels2)[1] == canonical
  @test T * D4 * transpose(T) == canonical[1]

  # the search can be chosen where Hecke computes automorphism groups and
  # isometries of lattices; both searches agree
  L = root_lattice(:E, 6)
  M = lll(L)
  K, a = quadratic_field(-3)
  LK = lattice(hermitian_space(K, 2))
  for algorithm in [:partition_backtrack, :plesken_souvignier]
    @test automorphism_group_order(L; redo = true, algorithm) == 103680
    fl, T = is_isometric_with_isometry(L, M; algorithm)
    @test fl && T * gram_matrix(M) * transpose(T) == gram_matrix(L)
    @test automorphism_group_order(LK; redo = true, algorithm) == 72
    @test is_isometric_with_isometry(LK, LK; algorithm)[1]
  end
  @test_throws ArgumentError automorphism_group_generators(
                               L; redo = true, algorithm = :none)
  # Gram matrices with entries which do not fit into a machine integer
  B = rescale(root_lattice(:A, 3), ZZ(2)^70)
  @test automorphism_group_order(B) == 48
  @test is_isometric_with_isometry(B, lll(B))[1]
end
