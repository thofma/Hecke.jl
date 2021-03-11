@testset "Torsion" begin
  # Trivial torsion module

  A = diagonal_matrix(fmpq[1, 1])
  T = Hecke.TorQuadMod(A)
  @test order(T) == 1

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

  #primary part of a TorQuadMod
  L = Zlattice(matrix(ZZ, [[2,0,0],[0,2,0],[0,0,2]]))
  T = Hecke.discriminant_group(L)
  @test basis_matrix(Hecke.cover(Hecke.primary_part(T,fmpz(2))[1])) == matrix(QQ, 3, 3, [1//2, 0, 0, 0, 1//2, 0, 0, 0, 1//2])

  #orthogonal submodule to a TorQuadMod
  L = Zlattice(matrix(ZZ, [[2,0,0],[0,2,0],[0,0,2]]))
  T = Hecke.discriminant_group(L)
  S = sub(T, gens(T))[1]
  @test basis_matrix(Hecke.cover(Hecke.orthogonal_submodule_to(T, S)[1])) == matrix(QQ, 3, 3, [1//2,0,0,0,1//2,0,0,0,1//2])

  #checks if a TorQuadMod is degenerate
  @test Hecke.isdegenerate(T) == false

  #test for rescaled torsion quadratic module
  @test Hecke.gram_matrix_quadratic(Hecke.rescale(T, -1)) == matrix(QQ, 3, 3, [7//4,0,0,0,7//4,0,0,0,7//4])
  t = Hecke.TorQuadMod(QQ[1//3 0; 0 1//9])
  @test Hecke.gram_matrix_quadratic(Hecke.rescale(t, 2)) == matrix(QQ, 2, 2, [2//3,0,0,2//9])

  #test for normal form
  L1 = Zlattice(gram=matrix(ZZ, [[-2,0,0],[0,1,0],[0,0,4]]))
  T1 = Hecke.discriminant_group(L1)
  @test Hecke.gram_matrix_quadratic(Hecke.normal_form(T1)[1]) == matrix(QQ, 2, 2, [1//2,0,0,1//4])


  L1 = Zlattice(gram=ZZ[-4 0 0; 0 4 0; 0 0 -2])
  AL1 = discriminant_group(L1)
  L2 = Zlattice(gram=ZZ[-4 0 0; 0 -4 0; 0 0 2])
  AL2 = discriminant_group(L2)
  n1 = normal_form(AL1)[1]
  g1 = QQ[1//2   0   0;
            0 1//4   0;
            0   0 5//4]
  @test Hecke.gram_matrix_quadratic(n1) == g1
  n2 = normal_form(AL2)[1]
  g2 = QQ[1//2   0   0;
            0 1//4   0;
            0   0 5//4]
  @test Hecke.gram_matrix_quadratic(n2) == g2

  #test for brown invariant
  L = Zlattice(gram=matrix(ZZ, [[2,-1,0,0],[-1,2,-1,-1],[0,-1,2,0],[0,-1,0,2]]))
  T = discriminant_group(L)  
  @test Hecke.brown_invariant(T) == 4

  #test for genus
  L = Zlattice(gram=diagonal_matrix(fmpz[1,2,3,4]))
  D = discriminant_group(L)
  @test genus(D, (4,0)) == genus(L)
  
  #test for isgenus
  L = Zlattice(gram=diagonal_matrix(fmpz[1,2,3,4]))
  D = discriminant_group(L)
  @test_throws ErrorException isgenus(D, (4,0))
  L1 = Zlattice(gram=matrix(ZZ, [[2, -1, 0, 0, 0, 0],[-1, 2, -1, -1, 0, 0],[0, -1, 2, 0, 0, 0],[0, -1, 0, 2, 0, 0],[0, 0, 0, 0, 6, 3],[0, 0, 0, 0, 3, 6]]))
  T1 = discriminant_group(L1)  
  @test isgenus(T1, (6,0))
  G = genus(diagonal_matrix(fmpz[2, 6, 6]))
  D = discriminant_group(G)
  @test isgenus(D, (3,0))

end

