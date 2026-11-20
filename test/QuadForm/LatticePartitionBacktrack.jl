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
end
