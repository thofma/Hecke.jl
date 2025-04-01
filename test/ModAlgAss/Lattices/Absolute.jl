@with_gap @testset "Lattices for symmetric group" begin
  # Look at the hook partition [2, 1^(n-1)] of S_{n + 1}.
  # Will have dimension n

  # n = 4
  n = 4
  g1 = matrix(QQ, 4, 4, [ 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 1, -1, 1, -1 ])
  g2 = matrix(QQ, 4, 4, [ -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, -1, 1, -1, 1 ])
  A = matrix_algebra(QQ, 4)
  O = order(A, [g1, g2])
  L = Hecke.natural_lattice(O)
  for p in [2, 3, 5, 7]
    S = Hecke.sublattice_classes(L, p)
    @test length(S) == valuation(4 + 1, p) + 1
  end

  @test_throws ErrorException is_irreducible(L.V)

  n = 5
  g1 = matrix(QQ, 5, 5, [ 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, -1, 1, -1, 1])
  g2 = matrix(QQ, 5, 5, [ -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 1, -1, 1, -1, 1 ])
  A = matrix_algebra(QQ, 5)
  O = order(A, [g1, g2])
  L = Hecke.natural_lattice(O)
  for p in [2, 3, 5, 7]
    S = Hecke.sublattice_classes(L, p)
    @test length(S) == valuation(5 + 1, p) + 1
  end
end

@with_gap @testset "Lattices for matrix order" begin
  # provided by Gabi Nebe
  A = matrix(QQ, 3, 3, [1,3^4,0,0,1,0,0,0,1]);
  B = matrix(QQ, 3, 3, [1,0,0,27,1,0,0,0,1]);
  C = matrix(QQ, 3, 3, [125,3^4,0,3*18,125-90,0,0,0,1]);
  D = matrix(QQ, 3, 3, [1,0,0,0,1,0,0,0,-1]);
  E = matrix(QQ, 3, 3, [1,0,3^4,0,1,0,0,0,1]);
  F = matrix(QQ, 3, 3, [1,0,0,0,1,3^5,0,0,1]);
  G = matrix(QQ, 3, 3, [1,0,0,0,1,0,3^3,0,1]);
  H = matrix(QQ, 3, 3, [1,0,0,0,1,0,0,9,1]);
  l = [A, B, C, D, E, F, G, H]
  A = matrix_algebra(QQ, 3)
  O = order(A, l)
  L = Hecke.natural_lattice(O)
  S = Hecke.sublattices(L, 3)
  @test length(S) == 216
end
