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
end
