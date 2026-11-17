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
  D4 = Int[2 0 -1 0; 0 2 -1 0; -1 -1 2 -1; 0 0 -1 2]
  chain = PB.stabilizer_chain(D4)
  @test prod(chain.orbit_lengths) == chain.order == 1152
  @test length(closure(matrix.(Ref(ZZ), chain.generators), *)) == 1152

  @test_throws ArgumentError PB.automorphism_group(hyperbolic_plane_lattice())
end
