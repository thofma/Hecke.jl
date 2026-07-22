@testset "Morphism" begin
  L = integer_lattice(gram = zero_matrix(ZZ, 0, 0))
  @test_throws ArgumentError shortest_vectors(L)
  @test_throws ArgumentError shortest_vectors(L, Vector{Int})
  @test_throws ArgumentError minimum(L)
  @test (@inferred short_vectors(L, 1)) == []
  @test (@inferred short_vectors(L, 1, 2)) == []

  G = ZZ[2 1 -1 -1 -1 1 1 -1 0 0 0 0 0 0 0 0; 1 2 -1 -1 -1 1 1 -1 0 0 0 0 0 0 0 0; -1 -1 2 0 1 0 -1 1 0 0 0 0 0 0 0 0; -1 -1 0 2 1 -1 0 0 0 0 0 0 0 0 0 0; -1 -1 1 1 2 0 -1 0 0 0 0 0 0 0 0 0; 1 1 0 -1 0 2 0 -1 0 0 0 0 0 0 0 0; 1 1 -1 0 -1 0 2 -1 0 0 0 0 0 0 0 0; -1 -1 1 0 0 -1 -1 2 0 0 0 0 0 0 0 0; 0 0 0 0 0 0 0 0 2 1 1 0 1 1 1 0; 0 0 0 0 0 0 0 0 1 2 1 0 1 1 0 0; 0 0 0 0 0 0 0 0 1 1 2 0 0 0 1 0; 0 0 0 0 0 0 0 0 0 0 0 2 1 0 -1 0; 0 0 0 0 0 0 0 0 1 1 0 1 4 1 0 1; 0 0 0 0 0 0 0 0 1 1 0 0 1 4 0 0; 0 0 0 0 0 0 0 0 1 0 1 -1 0 0 8 1; 0 0 0 0 0 0 0 0 0 0 0 0 1 0 1 18]
  L = integer_lattice(gram=G)
  @test length(shortest_vectors(L)) == 127

  A2 = root_lattice(:A, 2)
  Hecke.assert_has_automorphisms(A2, redo=true, try_small=false)
  @test automorphism_group_order(A2) == 12

  # Issue #2311: `ZLatAutoCtx`'s `init` threw `UndefRefError` whenever
  # more than 2 simultaneous Gram matrices were used, because the
  # short-vector length loop inside `init` always wrote to `w[2]`
  # instead of `w[k]`, leaving `w[3:r]` permanently undefined.
  # G4 == G2 is deliberate: it makes fingerprint's length comparison
  # loop reach (and previously crash on) the undefined w[3] slot
  # instead of bailing out earlier on an unrelated mismatch.
  let
    G1 = 2 * identity_matrix(ZZ, 3)
    G2 = 3 * identity_matrix(ZZ, 3)
    G3 = 5 * identity_matrix(ZZ, 3)
    G4 = 3 * identity_matrix(ZZ, 3)
    C = Hecke.ZLatAutoCtx([G1, G2, G3, G4])
    @test (Hecke.init(C, true); true)  # used to throw UndefRefError
  end
end
