@testset "Torsion" begin
  # Trivial torsion module
  A = diagonal_matrix(QQFieldElem[1, 1])
  T = Hecke.TorQuadModule(A)
  @test order(T) == 1
  # discriminant_group group of a non full lattice
  L = integer_lattice(2*identity_matrix(ZZ,2))
  S = lattice(ambient_space(L),basis_matrix(L)[1:1,:])
  @test order(discriminant_group(S)) == 4
  @test discriminant_group(S) === discriminant_group(S)

  D4_gram = matrix(ZZ, [[2, 0, 0, -1],
                        [0, 2, 0, -1],
                        [0, 0, 2, -1],
                        [-1 ,-1 ,-1 ,2]])

  L = integer_lattice(gram = D4_gram)
  T = @inferred discriminant_group(L)
  @test elem_type(T) == typeof(gens(T)[1])
  @test order(T) == 4
  @test elementary_divisors(T) == ZZRingElem[2, 2]

  S = lattice(ambient_space(L),basis_matrix(L)[2:2,:])
  D = discriminant_group(S)
  D0, _ = sub(D,gens(D)[1:0])
  @test order(D0)==1
  D1, _ = sub(D,gens(D)[1:1])
  @test order(D1)==2

  q1 = discriminant_group(root_lattice(:D,4))
  q2 = discriminant_group(integer_lattice(gram=ZZ[0 2; 2 0]))
  @test Hecke.gram_matrix_quadratic(q1) != Hecke.gram_matrix_quadratic(q2)
  @test Hecke.gram_matrix_bilinear(q1) == Hecke.gram_matrix_bilinear(q2)

  @test sprint(show, q1) isa String
  @test sprint(show, "text/plain", q1) isa String
  @test sprint(show, gens(q1)[1]) isa String
  a,b = gens(q1)
  @test lift(inner_product(a,b)) == 1//2
  @test order(a) == 2
  @test order(0*a) == 1
  AbstractAlgebra.set_name!(q1, "q1")
  f = hom(q1,q1, ZZ[2 0; 0 1])
  @test sprint(show, f) isa String

  ok, c = @inferred has_preimage_with_preimage(f ,b)
  @test ok
  @test b == c
  @test_throws ArgumentError preimage(f,a)
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

  @test order(-G[1])==order(G[1])
  @test iszero(0*G[1])

  TT, mTT = @inferred sub(T, [T([1, 1//2, 1//2, 1])])
  @test order(TT) == 2

  L = integer_lattice(ZZ[1 0; 0 1])
  M = lattice(ambient_space(L), ZZ[2 0; 0 3])
  T = @inferred torsion_quadratic_module(L, M, gens = [[1, 1]])
  @test order(T) == 6

  @test_throws ArgumentError torsion_quadratic_module(L, M, gens = [[0, 0]])
  @test_throws ArgumentError torsion_quadratic_module(L, M, gens = [[1//2, 0]])
  @test_throws ArgumentError torsion_quadratic_module(L, M, gens = [[1, 1, 2]])
  @test_throws ArgumentError torsion_quadratic_module(L, lattice(ambient_space(L), QQ[1//2 0; 0 0]))

  #primary part of a TorQuadModule
  L = integer_lattice(matrix(ZZ, [[2,0,0],[0,2,0],[0,0,2]]))
  T = Hecke.discriminant_group(L)
  @test basis_matrix(Hecke.cover(Hecke.primary_part(T,ZZRingElem(2))[1])) == matrix(QQ, 3, 3, [1//2, 0, 0, 0, 1//2, 0, 0, 0, 1//2])
  L1 = integer_lattice(identity_matrix(ZZ, 3))
  T1 = torsion_quadratic_module((1//6)*L1, L1)
  @test gram_matrix(Hecke.cover(Hecke.primary_part(T1,ZZRingElem(2))[1])) == matrix(QQ, 3, 3, [1//4, 0, 0, 0, 1//4, 0, 0, 0, 1//4])
  @test ambient_space(Hecke.cover(Hecke.primary_part(T1, exponent(T1))[1]))==ambient_space(Hecke.cover(T1))
  @test Hecke.cover(Hecke.primary_part(T1, exponent(T1))[1]) == Hecke.cover(T1)
  @test gram_matrix(Hecke.cover(Hecke.primary_part(T1, exponent(T1))[1])) == gram_matrix(Hecke.cover(T1))

  #orthogonal submodule to a TorQuadModule
  L = integer_lattice(matrix(ZZ, [[2,0,0],[0,2,0],[0,0,2]]))
  T = Hecke.discriminant_group(L)
  S, i = sub(T, gens(T))
  @test all([preimage(i,i(s))==s for s in gens(S)])
  @test basis_matrix(Hecke.cover(Hecke.orthogonal_submodule(T, S)[1])) == basis_matrix(L)
  L1 = integer_lattice(identity_matrix(ZZ,10))
  T1 = torsion_quadratic_module(L1, 3*L1)
  S1, _ = sub(T1, gens(T1)[1:5])
  @test ambient_space(Hecke.cover(Hecke.orthogonal_submodule(T1, S1)[1])) == ambient_space(L1)

  #checks if a TorQuadModule is degenerate
  @test Hecke.is_degenerate(T) == false
  t = Hecke.TorQuadModule(matrix(QQ,1,1,[1//27]))
  d = sub(t, gens(t)*3)[1]
  @test Hecke.is_degenerate(d) == true

  #test for rescaled torsion quadratic module
  @test Hecke.gram_matrix_quadratic(Hecke.rescale(T, -1)) == matrix(QQ, 3, 3, [7//4,0,0,0,7//4,0,0,0,7//4])
  t = Hecke.TorQuadModule(QQ[1//3 0; 0 1//9])
  @test Hecke.gram_matrix_quadratic(Hecke.rescale(t, -1)) == matrix(QQ, 2, 2, [2//3,0,0,8//9])
  #This form is defined modulo `2`
  @test Hecke.gram_matrix_quadratic(Hecke.rescale(t, 2)) == matrix(QQ, 2, 2, [2//3,0,0,2//9])
  #The next form is defined modulo `3`
  @test Hecke.gram_matrix_quadratic(Hecke.rescale(t, 3)) == matrix(QQ, 2, 2, [1,0,0,1//3])
  #The next form is defined modulo `4`
  @test Hecke.gram_matrix_quadratic(Hecke.rescale(t, 4)) == matrix(QQ, 2, 2, [4//3,0,0,4//9])


  #test for normal form
  L1 = integer_lattice(gram=matrix(ZZ, [[-2,0,0],[0,1,0],[0,0,4]]))
  T1 = Hecke.discriminant_group(L1)
  @test Hecke.gram_matrix_quadratic(normal_form(T1)[1]) == matrix(QQ, 2, 2, [1//2,0,0,1//4])

  L = integer_lattice(gram=QQ[-2 -1 -1 -1 1 1 1 -1 0 0 0 0 0 0 0 0; -1 -2 0 -1 0 0 0 -1 0 0 0 0 0 0 0 0; -1 0 -2 -1 1 1 1 0 0 0 0 0 0 0 0 0; -1 -1 -1 -2 1 1 1 0 0 0 0 0 0 0 0 0; 1 0 1 1 -2 -1 -1 0 0 0 0 0 0 0 0 0; 1 0 1 1 -1 -2 -1 0 0 0 0 0 0 0 0 0; 1 0 1 1 -1 -1 -2 0 0 0 0 0 0 0 0 0; -1 -1 0 0 0 0 0 -2 0 0 0 0 0 0 0 0; 0 0 0 0 0 0 0 0 -2 0 0 0 0 0 0 0; 0 0 0 0 0 0 0 0 0 -2 0 0 0 0 0 0; 0 0 0 0 0 0 0 0 0 0 -2 0 0 0 0 0; 0 0 0 0 0 0 0 0 0 0 0 -2 0 0 0 0; 0 0 0 0 0 0 0 0 0 0 0 0 -2 0 0 0; 0 0 0 0 0 0 0 0 0 0 0 0 0 -2 0 0; 0 0 0 0 0 0 0 0 0 0 0 0 0 0 -2 0; 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 -2])
  D = discriminant_group(L)
  nf = QQ[0 1//2 0 0 0 0 0 0 0 0; 1//2 0 0 0 0 0 0 0 0 0; 0 0 0 1//2 0 0 0 0 0 0; 0 0 1//2 0 0 0 0 0 0 0; 0 0 0 0 0 1//2 0 0 0 0; 0 0 0 0 1//2 0 0 0 0 0; 0 0 0 0 0 0 0 1//2 0 0; 0 0 0 0 0 0 1//2 0 0 0; 0 0 0 0 0 0 0 0 1//2 0; 0 0 0 0 0 0 0 0 0 3//2]
  @test Hecke.gram_matrix_quadratic(normal_form(D)[1]) == nf


  L1 = integer_lattice(gram=ZZ[-4 0 0; 0 4 0; 0 0 -2])
  AL1 = discriminant_group(L1)
  L2 = integer_lattice(gram=ZZ[-4 0 0; 0 -4 0; 0 0 2])
  AL2 = discriminant_group(L2)
  n1 = normal_form(AL1)[1]
  g1 = QQ[1//2   0   0;
            0 1//4   0;
            0   0 5//4]
  @test Hecke.gram_matrix_quadratic(n1) == g1
  n2 = normal_form(AL2)[1]
  @test Hecke.gram_matrix_quadratic(n2) == g1
  L3 = integer_lattice(gram=matrix(ZZ, [[2,0,0,-1],[0,2,0,-1],[0,0,2,-1],[-1,-1,-1,2]]))
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
  T2 = torsion_quadratic_module((1//6)*dual(L3), L3, modulus=QQFieldElem(1//36))
  n4 = normal_form(T2)[1]
  g4 = QQ[1//36 1//72;
          1//72 1//36]
  @test Hecke.gram_matrix_quadratic(n4) == g4
  q = QQ[1//2 0 1//2 1//2; 0 1//2 0 1//2; 1//2 0 1//8 5//16; 1//2 1//2 5//16 27//16]
  d = torsion_quadratic_module(q)
  nf = normal_form(d)[1]
  @test Hecke.gram_matrix_quadratic(nf) == QQ[1//2 0 0 0; 0 1//2 0 0; 0 0 3//16 0; 0 0 0 7//16]

  #test for brown invariant
  L1 = integer_lattice(gram=matrix(ZZ, [[2,-1,0,0],[-1,2,-1,-1],[0,-1,2,0],[0,-1,0,2]]))
  T1 = discriminant_group(L1)
  @test Hecke.brown_invariant(T1) == 4
  L2 = integer_lattice(matrix(ZZ, 2,2,[4,2,2,4]))
  T2 = Hecke.discriminant_group(L2)
  @test Hecke.brown_invariant(T2) == 2
  L3 = integer_lattice(gram=matrix(ZZ, [[1,0,0],[0,1,0],[0,0,1]]))
  T3 = torsion_quadratic_module((1//10)*L3, L3)
  @test_throws ArgumentError Hecke.brown_invariant(T3)


  #test for genus
  L = integer_lattice(gram=diagonal_matrix(ZZRingElem[1,2,3,4]))
  D = discriminant_group(L)
  @test genus(D, (4,0)) == genus(L)
  L1 = integer_lattice(gram=matrix(ZZ, [[2, -1, 0, 0, 0, 0],[-1, 2, -1, -1, 0, 0],[0, -1, 2, 0, 0, 0],[0, -1, 0, 2, 0, 0],[0, 0, 0, 0, 6, 3],[0, 0, 0, 0, 3, 6]]))
  T1 = discriminant_group(L1)
  @test genus(T1, (6,0)) == genus(L1)

  B = matrix(QQ, 8, 8 ,[2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 3//2, 1//2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1//2, 0, 1//2, 0, 0, 2//3, 1//6]);
  G = matrix(QQ, 8, 8 ,[1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, -42]);
  L = integer_lattice(B, gram = G);

  T = discriminant_group(L)
  @test genus(T, signature_tuple(L)[[1,3]]) == genus(L)
  T2 = Hecke._as_finite_bilinear_module(T)
  @test genus(T2, signature_tuple(L)[[1,3]]; parity = 2) == genus(L)

  B = matrix(QQ, 7, 7 ,[2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1//2, 1//2, 1//2, 0, 1//2, 0, 0, 1//2, 1, 1//2, 3//2, 0, 1//2, 0, 1//2, 1, 1//2, 1, 0, 0, 1//2]);
  G = matrix(QQ, 7, 7 ,[1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -10]);
  L = integer_lattice(B, gram = G);

  T = discriminant_group(L)
  @test genus(T, signature_tuple(L)[[1,3]]) == genus(L)
  T2 = Hecke._as_finite_bilinear_module(T)
  @test genus(T2, signature_tuple(L)[[1,3]]; parity = 2) == genus(L)

  #test for is_genus
  L = integer_lattice(gram=diagonal_matrix(ZZRingElem[1,2,3,4]))
  D = discriminant_group(L)
  @test is_genus(D, (4,0))
  L1 = integer_lattice(gram=matrix(ZZ, [[2, -1, 0, 0, 0, 0],[-1, 2, -1, -1, 0, 0],[0, -1, 2, 0, 0, 0],[0, -1, 0, 2, 0, 0],[0, 0, 0, 0, 6, 3],[0, 0, 0, 0, 3, 6]]))
  T1 = discriminant_group(L1)
  @test is_genus(T1, (6,0)) == true
  @test is_genus(T1, (4,2)) == false
  @test is_genus(T1, (16,2)) == true
  @test is_genus(T1, (5,1)) == false
  G = genus(diagonal_matrix(ZZRingElem[2, 6, 6]))
  D = discriminant_group(G)
  @test is_genus(D, (2,0)) == false
  @test is_genus(D, (3,0)) == true

  B = matrix(QQ, 7, 7 ,[2, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 9, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1//2, 13//2, 1//2, 1//2, 1, 0, 0, 3//2, 3, 0, 1//2, 1//2, 1//2, 0, 1, 5//2, 1//2, 0, 0, 0, 1//2]);
  G = matrix(QQ, 7, 7 ,[1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -38]);
  L = integer_lattice(B, gram = G);

  T = discriminant_group(L)
  @test is_genus(T, signature_tuple(L)[[1,3]]; parity = 1)

  B = matrix(QQ, 6, 6 ,[2, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 1, 6, 1, 0, 0, 0, 0, 5, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1//2, 9, 1//2, 0, 0, 1//2]);
  G = matrix(QQ, 6, 6 ,[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2]);
  L = integer_lattice(B, gram = G);

  T = discriminant_group(L)
  @test is_genus(T, signature_tuple(L)[[1,3]]; parity = 1)

  N, i = normal_form(D)
  @test N === normal_form(N)[1]
  j = inv(i)
  @test all(g == i(j(g)) for g in gens(N))

  # iterator
  gen = integer_genera((0,6), 2^3*3^3*5^2)
  disc = discriminant_group.(gen)
  @test all(T -> length(collect(T)) == order(T), disc)

  # radical_quadratic
  q = zero_matrix(QQ, 4, 4)
  q[3,3]=q[4,4]=1; q[1,3]=q[2,4]=q[3,1]=q[4,2]=1//2
  t = torsion_quadratic_module(q)
  k = sub(t,gens(t)[3:4])
  @test order(radical_quadratic(k[1])[1])==2

  # isometry

  L = integer_lattice(gram=matrix(ZZ, [[2, -1, 0, 0, 0, 0],[-1, 2, -1, -1, 0, 0],[0, -1, 2, 0, 0, 0],[0, -1, 0, 2, 0, 0],[0, 0, 0, 0, 6, 3],[0, 0, 0, 0, 3, 6]]))
  T = discriminant_group(L)
  N, S = normal_form(T)
  bool, phi = @inferred is_isometric_with_isometry(T, N)
  @test bool
  @test S.map_ab == phi.map_ab
  _, phi = is_isometric_with_isometry(T, T)
  @test phi.map_ab == id_hom(T).map_ab
  rq, _ = radical_quadratic(T)
  @test is_isometric_with_isometry(rq, torsion_quadratic_module(QQ[2;]))[1]
  Tsub, _ = sub(T, [T[1]])
  @test is_semi_regular(Tsub)
  @test !is_isometric_with_isometry(T, Tsub)[1]
  @test !is_anti_isometric_with_anti_isometry(T, Tsub)[1]
  @test_throws ArgumentError is_isometric_with_isometry(T, rescale(T, 1//2))

  Tsub, _ = sub(T, [2*T[1], 3*T[2]])
  @test !is_semi_regular(Tsub)
  rq, i = radical_quadratic(Tsub)
  bool, j = @inferred has_complement(i)
  N = domain(j)
  T2, _ = direct_sum(rq, N)
  @test is_degenerate(T2)
  bool, phi = @inferred is_isometric_with_isometry(Tsub, T2)
  @test bool
  @test is_bijective(phi)
  @test !is_anti_isometric_with_anti_isometry(Tsub, T2)[1]
  rq2, _ = radical_quadratic(Tsub) # the same as before but different julia object
  @test is_isometric_with_isometry(rq, rq2)[1]
  @test is_anti_isometric_with_anti_isometry(rq, rq2)[1]

  L = root_lattice(:E, 8)
  @test sprint(show, "text/plain", rescale(discriminant_group(L), 2)) isa String
  agg = automorphism_group_generators(L)
  for f in agg
    if isone(f)
      continue
    end
    L1 = invariant_lattice(L, f)
    L2 = orthogonal_submodule(L, L1)
    qL1 = discriminant_group(L1)
    qL2 = discriminant_group(L2)
    bool, phi = @inferred is_anti_isometric_with_anti_isometry(qL2, qL1)
    @test bool
    LL = overlattice(phi)
    @test det(LL) == 1 && iseven(LL)
  end

  f = matrix(QQ, 8, 8, [-1 0 0 0 0 0 0 0;
                        0 -1 0 0 0 0 0 0;
                        0 0 -1 0 0 0 0 0;
                        0 0 0 -1 0 0 0 0;
                        0 0 0 0 -1 0 0 0;
                        0 0 0 0 0 -1 0 0;
                        0 0 0 0 0 0 -1 0;
                        0 0 0 0 0 0 0 -1])
  Lf = invariant_lattice(L, f)
  @test rank(Lf) == 0
  qLf = discriminant_group(Lf)
  @test modulus_quadratic_form(qLf) == 2

  T = TorQuadModule(matrix(QQ, 1, 1, [1//27]))
  @test Hecke._isometry_non_split_degenerate(T, T)[1]
  T1sub, _ = sub(T, 3*gens(T))
  T2sub, _ = sub(T, 15*gens(T))
  ok, phi = @inferred is_isometric_with_isometry(T1sub, T2sub)
  @test ok
  @test is_bijective(phi)
  @test all(a -> Hecke.quadratic_product(a) == Hecke.quadratic_product(phi(a)), T1sub)
  ok, phi = @inferred is_anti_isometric_with_anti_isometry(T1sub, rescale(T1sub, -1))
  @test ok
  @test is_bijective(phi)
  @test all(a -> Hecke.quadratic_product(a) == (-1)*Hecke.quadratic_product(phi(a)), T1sub)

  # direct sums

  B = matrix(QQ, 3, 3 ,[1, 1, 0, 1, -1, 0, 0, 1, -1])
  G = matrix(QQ, 3, 3 ,[1, 0, 0, 0, 1, 0, 0, 0, 1])
  L1 = integer_lattice(B, gram = G)
  qL1 = discriminant_group(L1)
  Z = torsion_quadratic_module(QQ[1;])
  @test_throws ArgumentError direct_sum(qL1, Z)
  @test_throws ArgumentError direct_product(qL1, rescale(Z, 2))

  B = matrix(QQ, 4, 4 ,[2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 1, 1, 1])
  G = matrix(QQ, 4, 4 ,[1//2, 0, 0, 0, 0, 1//2, 0, 0, 0, 0, 1//2, 0, 0, 0, 0, 1//2])
  L2 = integer_lattice(B, gram = G)
  qL2 = discriminant_group(L2)
  Z = torsion_quadratic_module(QQ[2;])
  q, _ = @inferred direct_product(qL2, Z)
  @test is_isometric_with_isometry(q, qL2)[1]
  @test modulus_bilinear_form(q) == modulus_bilinear_form(qL2)
  @test modulus_quadratic_form(q) == modulus_quadratic_form(Z)

  L3, _ = direct_product(L1, L2)
  qL3 = discriminant_group(L3)

  q, inj = @inferred direct_sum(qL1, qL2)
  qL1inq, qL2inq = inj
  @test is_injective(qL1inq) && is_injective(qL2inq)
  bool, _ = is_isometric_with_isometry(qL3, q)
  @test bool

  # primary/elementary

  L = integer_lattice(gram=matrix(ZZ, [[2, -1, 0, 0, 0, 0],[-1, 2, -1, -1, 0, 0],[0, -1, 2, 0, 0, 0],[0, -1, 0, 2, 0, 0],[0, 0, 0, 0, 6, 3],[0, 0, 0, 0, 3, 6]]))
  T = discriminant_group(L)
  Tsub, _ = sub(T, [2*T[1], 3*T[2]])
  @test !is_primary_with_prime(Tsub)[1]
  bool, p = @inferred is_primary_with_prime(T)
  @test !bool && p == -1
  @test is_primary(primary_part(T, 2)[1], 2)
  @test !is_elementary(primary_part(T, 3)[1], 3)

  for i in [6,7,8]
    L = root_lattice(:E, i)
    qL = discriminant_group(L)
    @test is_elementary(qL, 9-i)
  end
  L = biproduct(root_lattice(:A, 7), root_lattice(:D, 7))[1]
  qL = discriminant_group(L)
  @test is_primary(qL, 2) && !is_elementary(qL, 2)

  # Additional direct sum
  list_lat = [root_lattice(:A, i) for i in 1:7]
  list_quad = discriminant_group.(list_lat)
  S, inj, proj = biproduct(list_quad)
  @test order(S) == prod(order.(list_quad))
  for i in 1:7, j in 1:7
    f = compose(inj[i], proj[j])
    m = f.map_ab.map
    @test i == j ? isone(m) : iszero(m)
  end

  T = discriminant_group(root_lattice(:D, 6))
  S, inj, proj = @inferred biproduct(T, T, T)

  U2 = hyperbolic_plane_lattice(2)
  q = discriminant_group(U2)
  qq, qqinq = sub(q, [q[1]+q[2]])
  ok, qqqinq = has_complement(qqinq)
  @test ok
  @test is_isometric_with_isometry(qq + domain(qqqinq), q)[1]

  # Smith normal form
  L = integer_lattice(gram=matrix(ZZ, [[2, -1, 0, 0, 0, 0],[-1, 2, -1, -1, 0, 0],[0, -1, 2, 0, 0, 0],[0, -1, 0, 2, 0, 0],[0, 0, 0, 0, 6, 3],[0, 0, 0, 0, 3, 6]]))
  T = discriminant_group(L)
  Tsub, _ = sub(T, [T[1]+T[2], T[1]-T[2]])
  @test !is_snf(Tsub)
  S, f = @inferred snf(Tsub)
  @test is_snf(S)

  # trivial element
  L = root_lattice(:E, 7)
  qL = discriminant_group(L)
  a = @inferred id(qL)
  @test iszero(a)

  # totally isotropic check
  V = quadratic_space(QQ, QQ[2 0 -1 0; 0 2 -1 0; -1 -1 2 -1; 0 0 -1 2])
  L = lattice(V, 2*identity_matrix(ZZ, 4))
  T = discriminant_group(L)
  S, = sub(T, [T([1, 0, 0, 0]), T([0, 1, 0, 0]), T([0, 0, 1, 0]), T([0, 0, 0, 1])])
  @test @inferred is_totally_isotropic(S)
  @test @inferred !is_totally_isotropic(T)

  # submodules
  T = torsion_quadratic_module(QQ[1//2 1//4; 1//4 1//2])
  @test length(collect(submodules(T, order = 2))) == 3
  @test length(collect(stable_submodules(T, [id_hom(T)], quotype = [2]))) == 3
end


@testset "Maps functionalities" begin

  L = rescale(root_lattice(:A, 3), 15)
  qL = discriminant_group(L)
  f = id_hom(qL)
  fab = @inferred abelian_group_homomorphism(f)
  @test all(a -> fab(data(a)) == data(f(a)), gens(qL))
  M = @inferred matrix(f)
  @test isone(M)

  f = @inferred trivial_morphism(qL)
  @test iszero(matrix(f))

  N, qLtoN = normal_form(qL)
  f = @inferred zero(qLtoN)
  @test domain(f) === qL
  @test codomain(f) === N
  @test iszero(matrix(f))

  K, KtoqL = @inferred kernel(qLtoN)
  @assert order(K) == 1
  K, KtoqL = kernel(f)
  @assert order(K) == order(qL)
  @assert isone(matrix(KtoqL))

  m = matrix(QQ, 3, 3, [ 0  1  1;
                        -1 -1 -1;
                         1  1  0])  # this has order 4
  f = hom(qL, qL, TorQuadModuleElem[qL(lift(a)*m) for a in gens(qL)]) # This has also order 4!
  p = minpoly(m) # p = (X^2+1)(X+1)

  @test iszero(matrix(p(f)))
  @test iszero(p(abelian_group_homomorphism(f))) #trivia for test coverage
  @test !iszero(matrix(p(-f)))
  @test iszero(matrix(f-f))
  @test iszero(matrix(f*order(qL)))
  @test isone(matrix(f^4))
  @test !isone(matrix(f^2))
  @test abelian_group_homomorphism(f) == abelian_group_homomorphism(f^5)
  @test abelian_group_homomorphism(f*4) == abelian_group_homomorphism(f)*4 #trivia for test coverage

  Zx, x = ZZ["x"]
  @test matrix((x-1)(f)) == matrix(f) - 1
  @test x(abelian_group_homomorphism(f)).map == matrix(f) #trivia for test coverage

  T = torsion_quadratic_module(QQ[1//2 1//4; 1//4 1//2])
  f = id_hom(T)
  @test is_isometry(f)
  @test !is_anti_isometry(f)

  f = hom(T, T, [gen(T, 1) + gen(T, 2), 3*gen(T, 1) + 2*gen(T, 2)])
  @test is_anti_isometry(f)
  @test !is_isometry(f)
end

@testset "Equality and hashes" begin
  L = root_lattice(:E, 7)
  T = discriminant_group(L)
  T2, _ = sub(T, gens(T))
  @test T == T2
  @test length(unique!([T, T2])) == 1
  @test length(unique!([T[1], -T[1]])) == 1
end

@testset "Map with trivial torsion quadratic modules" begin
  q = discriminant_group(integer_lattice(; gram=matrix(QQ, 0, 0, [])))
  q2 = discriminant_group(root_lattice(:E, 6))
  psi = @inferred hom(q, q, gens(q), gens(q))
  @test is_bijective(psi)
  phi = @inferred hom(q, q2, elem_type(q2)[])
  @test is_injective(phi)
end
