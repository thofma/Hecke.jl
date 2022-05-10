@testset "Torsion" begin
  # Trivial torsion module
  A = diagonal_matrix(fmpq[1, 1])
  T = Hecke.TorQuadMod(A)
  @test order(T) == 1
  # discriminant_group group of a non full lattice
  L = Zlattice(2*identity_matrix(ZZ,2))
  S = lattice(ambient_space(L),basis_matrix(L)[1,:])
  @test order(discriminant_group(S)) == 4

  D4_gram = matrix(ZZ, [[2, 0, 0, -1],
                        [0, 2, 0, -1],
                        [0, 0, 2, -1],
                        [-1 ,-1 ,-1 ,2]])

  L = Zlattice(gram = D4_gram)
  T = @inferred discriminant_group(L)
  @test elem_type(T) == typeof(gens(T)[1])
  @test order(T) == 4
  @test elementary_divisors(T) == fmpz[2, 2]

  S = lattice(ambient_space(L),basis_matrix(L)[:2,:])
  D = discriminant_group(S)
  D1, _ = sub(D,gens(D)[1:1])
  @test order(D1)==2

  q1 = discriminant_group(root_lattice(:D,4))
  q2 = discriminant_group(Zlattice(gram=ZZ[0 2; 2 0]))
  @test Hecke.gram_matrix_quadratic(q1) != Hecke.gram_matrix_quadratic(q2)
  @test Hecke.gram_matrix_bilinear(q1) == Hecke.gram_matrix_bilinear(q2)

  @test sprint(show, q1) isa String
  @test sprint(show, "text/plain", q1) isa String
  @test sprint(show, gens(q1)[1]) isa String
  a,b = gens(q1)
  @test lift(inner_product(a,b)) == 1//2
  @test order(a) == 2
  @test order(0*a) == 1
  set_attribute!(q1, :name, "q1")
  f = hom(q1,q1, ZZ[2 0; 0 1])
  @test sprint(show, f) isa String

  @test b == preimage(f,b)
  @test_throws ErrorException preimage(f,a)
  @test !is_bijective(f)

  T, i = primary_part(q1, 3)
  @test order(T) == 1

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
  L1 = Zlattice(identity_matrix(ZZ, 3))
  T1 = torsion_quadratic_module((1//6)*L1, L1)
  @test gram_matrix(Hecke.cover(Hecke.primary_part(T1,fmpz(2))[1])) == matrix(QQ, 3, 3, [1//4, 0, 0, 0, 1//4, 0, 0, 0, 1//4])
  @test ambient_space(Hecke.cover(Hecke.primary_part(T1, exponent(T1))[1]))==ambient_space(Hecke.cover(T1))
  @test Hecke.cover(Hecke.primary_part(T1, exponent(T1))[1]) == Hecke.cover(T1)
  @test gram_matrix(Hecke.cover(Hecke.primary_part(T1, exponent(T1))[1])) == gram_matrix(Hecke.cover(T1))

  #orthogonal submodule to a TorQuadMod
  L = Zlattice(matrix(ZZ, [[2,0,0],[0,2,0],[0,0,2]]))
  T = Hecke.discriminant_group(L)
  S, i = sub(T, gens(T))
  @test all([preimage(i,i(s))==s for s in gens(S)])
  @test basis_matrix(Hecke.cover(Hecke.orthogonal_submodule_to(T, S)[1])) == basis_matrix(L)
  L1 = Zlattice(identity_matrix(ZZ,10))
  T1 = torsion_quadratic_module(L1, 3*L1)
  S1, _ = sub(T1, gens(T1)[1:5])
  @test ambient_space(Hecke.cover(Hecke.orthogonal_submodule_to(T1, S1)[1])) == ambient_space(L1)

  #checks if a TorQuadMod is degenerate
  @test Hecke.is_degenerate(T) == false
  t = Hecke.TorQuadMod(matrix(QQ,1,1,[1//27]))
  d = sub(t, gens(t)*3)[1]
  @test Hecke.is_degenerate(d) == true

  #test for rescaled torsion quadratic module
  @test Hecke.gram_matrix_quadratic(Hecke.rescale(T, -1)) == matrix(QQ, 3, 3, [7//4,0,0,0,7//4,0,0,0,7//4])
  t = Hecke.TorQuadMod(QQ[1//3 0; 0 1//9])
  @test Hecke.gram_matrix_quadratic(Hecke.rescale(t, -1)) == matrix(QQ, 2, 2, [2//3,0,0,8//9])
  #This form is defined modulo `2`
  @test Hecke.gram_matrix_quadratic(Hecke.rescale(t, 2)) == matrix(QQ, 2, 2, [2//3,0,0,2//9])
  #The next form is defined modulo `3`
  @test Hecke.gram_matrix_quadratic(Hecke.rescale(t, 3)) == matrix(QQ, 2, 2, [1,0,0,1//3])
  #The next form is defined modulo `4`
  @test Hecke.gram_matrix_quadratic(Hecke.rescale(t, 4)) == matrix(QQ, 2, 2, [4//3,0,0,4//9])


  #test for normal form
  L1 = Zlattice(gram=matrix(ZZ, [[-2,0,0],[0,1,0],[0,0,4]]))
  T1 = Hecke.discriminant_group(L1)
  @test Hecke.gram_matrix_quadratic(normal_form(T1)[1]) == matrix(QQ, 2, 2, [1//2,0,0,1//4])

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
  @test Hecke.gram_matrix_quadratic(n2) == g1
  L3 = Zlattice(gram=matrix(ZZ, [[2,0,0,-1],[0,2,0,-1],[0,0,2,-1],[-1,-1,-1,2]]))
  T=torsion_quadratic_module((1//6)*dual(L3), L3)
  n3 = normal_form(T)[1]
  g3 = QQ[1//6 1//12      0     0     0     0     0     0;
          1//12 1//6      0     0     0     0     0     0;
            0     0   1//12 1//24     0     0     0     0;
            0     0   1//24 1//12     0     0     0     0;
            0     0       0     0   2//9    0     0     0;
            0     0       0     0     0    2//9   0     0;
            0     0       0     0     0     0    2//9   0;
            0     0       0     0     0     0     0   2//9]
  @test Hecke.gram_matrix_quadratic(n3) == g3
  T2 = torsion_quadratic_module((1//6)*dual(L3), L3, modulus=fmpq(1//36))
  n4 = normal_form(T2)[1]
  g4 = QQ[1//36 1//72;
          1//72 1//36]
  @test Hecke.gram_matrix_quadratic(n4) == g4

  #test for brown invariant
  L1 = Zlattice(gram=matrix(ZZ, [[2,-1,0,0],[-1,2,-1,-1],[0,-1,2,0],[0,-1,0,2]]))
  T1 = discriminant_group(L1)
  @test Hecke.brown_invariant(T1) == 4
  L2 = Zlattice(matrix(ZZ, 2,2,[4,2,2,4]))
  T2 = Hecke.discriminant_group(L2)
  @test Hecke.brown_invariant(T2) == 2
  L3 = Zlattice(gram=matrix(ZZ, [[1,0,0],[0,1,0],[0,0,1]]))
  T3 = torsion_quadratic_module((1//10)*L3, L3)
  @test_throws ArgumentError Hecke.brown_invariant(T3)

  #test for genus
  L = Zlattice(gram=diagonal_matrix(fmpz[1,2,3,4]))
  D = discriminant_group(L)
  @test genus(D, (4,0)) == genus(L)
  L1 = Zlattice(gram=matrix(ZZ, [[2, -1, 0, 0, 0, 0],[-1, 2, -1, -1, 0, 0],[0, -1, 2, 0, 0, 0],[0, -1, 0, 2, 0, 0],[0, 0, 0, 0, 6, 3],[0, 0, 0, 0, 3, 6]]))
  T1 = discriminant_group(L1)
  @test genus(T1, (6,0)) == genus(L1)

  #test for is_genus
  L = Zlattice(gram=diagonal_matrix(fmpz[1,2,3,4]))
  D = discriminant_group(L)
  @test is_genus(D, (4,0))
  L1 = Zlattice(gram=matrix(ZZ, [[2, -1, 0, 0, 0, 0],[-1, 2, -1, -1, 0, 0],[0, -1, 2, 0, 0, 0],[0, -1, 0, 2, 0, 0],[0, 0, 0, 0, 6, 3],[0, 0, 0, 0, 3, 6]]))
  T1 = discriminant_group(L1)
  @test is_genus(T1, (6,0)) == true
  @test is_genus(T1, (4,2)) == false
  @test is_genus(T1, (16,2)) == true
  @test is_genus(T1, (5,1)) == false
  G = genus(diagonal_matrix(fmpz[2, 6, 6]))
  D = discriminant_group(G)
  @test is_genus(D, (2,0)) == false
  @test is_genus(D, (3,0)) == true

  N, i = normal_form(D)
  @test N === normal_form(N)[1]
  j = inv(i)
  @test all(g == i(j(g)) for g in gens(N))
end
