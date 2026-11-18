@testset "Lattice partition backtrack" begin
  # Compare generators and group order with known automorphism group orders.
  PB = Hecke.LatticePartitionBacktrack

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
  D4 = ZZ[2 0 -1 0; 0 2 -1 0; -1 -1 2 -1; 0 0 -1 2]
  chain = PB.stabilizer_chain(PB.ShortVectors([D4]))
  @test prod(chain.orbit_lengths) == chain.order == 1152
  @test length(closure(matrix.(Ref(ZZ), chain.generators), *)) == 1152

  # entries which do not fit into machine integers
  gens, order = PB.automorphism_group([ZZ(2)^70 * D4])
  @test order == 1152
  @test all(g -> g * D4 * transpose(g) == D4, gens)

  # several forms, also skew-symmetric and asymmetric ones: the centralizer
  # of a rotation of order 3 in the automorphism group of A2 has order 6
  A2 = ZZ[2 -1; -1 2]
  r = ZZ[0 1; -1 -1]
  for F in [ZZ[0 1; -1 0], r * A2]
    gens, order = PB.automorphism_group([A2, F])
    @test order == 6
    @test all(g -> g * A2 * transpose(g) == A2, gens)
    @test all(g -> g * F * transpose(g) == F, gens)
  end

  # labels: the stabilizer of a vector, given by its scalar products with
  # the short vectors; -1 is not in the group
  V = PB.enumerate_vectors(D4)
  w = ZZ[1 0 0 0] * D4
  labels = Int[Int((w * matrix(ZZ, 4, 1, v))[1, 1]) for v in V]
  gens, order = PB.automorphism_group([D4], [(v, 0) for v in V], labels)
  @test order == 48
  @test all(g -> g * D4 * transpose(g) == D4, gens)
  @test all(g -> ZZ[1 0 0 0] * g == ZZ[1 0 0 0], gens)

  # isometry
  E8 = change_base_ring(ZZ, gram_matrix(root_lattice(:E, 8)))
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

  @test_throws ArgumentError PB.automorphism_group(hyperbolic_plane_lattice())
end
