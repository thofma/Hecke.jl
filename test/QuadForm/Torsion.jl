@testset "Torsion" begin
  D4_gram = matrix(ZZ, [[2, 0, 0, -1],
                        [0, 2, 0, -1],
                        [0, 0, 2, -1],
                        [-1 ,-1 ,-1 ,2]])

  L = Zlattice(gram = D4_gram)
  T = @inferred discriminant_group(L)
  @test order(T) == 4
  @test elementary_divisors(T) == fmpz[2, 2]

  Ld = dual(L)

  T = @inferred torsion_quadratic_module(Ld, L, snf = false)
  @test ngens(T) == 4
  G = gens(T)
  for i in 1:4
    @test T(lift(G[i])) == G[i]
  end

  TT, mTT = @inferred sub(T, [T([1, 1//2, 1//2, 1])])
  @test order(TT) == 2

  L = Zlattice(ZZ[1 0; 0 1])
  M = lattice(ambient_space(L), ZZ[2 0; 0 3])
  T = @inferred torsion_quadratic_module(L, M, gens = [[1, 1]])
  @test order(T) == 6

  @test_throws ArgumentError torsion_quadratic_module(L, M, gens = [[0, 0]])
  @test_throws ArgumentError torsion_quadratic_module(L, M, gens = [[1//2, 0]])
  @test_throws ArgumentError torsion_quadratic_module(L, M, gens = [[1, 1, 2]])
  @test_throws ArgumentError torsion_quadratic_module(L, lattice(ambient_space(L), QQ[1//2 0; 0 0]))
end
