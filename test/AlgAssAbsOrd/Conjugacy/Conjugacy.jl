@testset "Conjugacy" begin
  a = ZZRingElem[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
           1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
           0, -9604, -7056, -12076, -2392, -2253, 952, 46, -16, 0, 0, 0, 0, 0,
           0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4900, -140]

  b = ZZRingElem[-4645900, -49391, -3848404, -16744, -15771, 6664, 17066, 470484,
           33488, 3779643, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1,
           0, -2, 0, -26, 0, -8, 0, 1, 0, 0, 1, 0, 9, -55750240, -592692,
           -46180848, -200928, -189252, 79969, 204792, 5645808, 396956,
           45355576, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -10, 0, -8, 0, 0, 0, 0, 1,
           0, 8, 101541620, 1079546, 84115116, 365984, 344709, -145656,
           -373022, -10283436, -692768, -82611077, -4, 0, 0, 0, 0, 0, 0, 0, 0,
           1, -18583040, -197564, -15393616, -66976, -63084, 26656, 68264,
           1881936, 129052, 15118432]

  A = matrix(ZZ, 10, 10, a)
  B = matrix(ZZ, 10, 10, b)

  fl, C = Hecke.is_GLZ_conjugate(A, B)
  @test fl
  @test C * A == B * C

  A = matrix(QQ, 10, 10, a)
  B = matrix(QQ, 10, 10, b)

  fl, C = Hecke.is_GLZ_conjugate(A, B)
  _C = map_entries(QQ, C)
  @test fl
  @test _C * A == B * _C

  A = QQFieldElem(1, 10) * A
  B = QQFieldElem(1, 10) * B
  fl, C = Hecke.is_GLZ_conjugate(A, B)
  _C = map_entries(QQ, C)
  @test fl
  @test _C * A == B * _C

  fl, _ = Hecke.is_GLZ_conjugate(QQ[1 2; 3 4], QQ[1 2 3; 4 5 6; 7 8 9])
  @test !fl

  R = residue_ring(FlintZZ, ZZRingElem(7))[1]
  x, y = R(6), R(6)
  q, r = divrem(x, y)
  @test y * q + r == x
  @test iszero(r)

  fl, = Hecke.is_GLZ_conjugate(ZZ[0 1; 0 0], ZZ[0 2; 0 0])
  @test !fl

  I = matrix(ZZ, 8, 8, [-21 12 17 -3 -3 15 10 -8;
                       -6 3 5 -1 -4 5 4 -2;
                       -36 18 29 -5 7 25 16 -16;
                       -72 36 58 -11 13 52 33 -33;
                       0 0 0 0 -9 3 2 0;
                       0 0 0 0 -21 0 5 4;
                       0 0 0 0 -9 0 2 2;
                       0 0 0 0 -36 0 8 7])
  J = matrix(ZZ, 8, 8, [0 3 0 -1 0 0 0 0;
                        -3 0 1 0 0 0 0 0;
                        0 0 0 1 0 0 0 0;
                        -9 0 2 0 0 0 0 0;
                        0 0 0 0 -63 48 51 -13;
                        0 0 0 0 -84 63 68 -17;
                        0 0 0 0 -36 27 29 -7;
                        0 0 0 0 -144 108 116 -29])
  for k in 1:10
    fl, T = is_GLZ_conjugate(I, J)
    @test fl
    @test T * I == J * T && isone(abs(det(T)))
  end

  # Example from #834
  M = matrix(ZZ, 6, 6, [-15, 8, 0, 0, -30, 26,
                        -30, 15, 0, 0, -30, 30,
                        0, 0, -15, 8, 0, -4,
                        0, 0, -30, 15, -30, 15,
                        0, 0, 0, 0, -45, 34,
                        0, 0, 0, 0, -60, 45 ])
  N = matrix(ZZ, 6, 6, [-15, 8, 0, 0, 0, -4,
                        -30, 15, 0, 0, -30, 15,
                        0, 0, -15, 8, -30, 26,
                        0, 0, -30, 15, -30, 30,
                        0, 0, 0, 0, -45, 34,
                        0, 0, 0, 0, -60, 45 ])

  for i in 1:5
    fl, T = is_GLZ_conjugate(M, N)
    @test fl
    @test T * M == N * T && isone(abs(det(T)))
  end
end

@testset "basis commutator algebra" begin

  F, z = cyclotomic_field(3, cached = false)
  As = dense_matrix_type(F)[matrix(F, 2, 2, [1 0; 0 -1]), identity_matrix(F, 2)]
  Bs = dense_matrix_type(F)[matrix(F, 2, 2, [0 1; 1 0]), matrix(F, 2, 2, [-z-1 0;0 z])]
  bas = @inferred Hecke._basis_of_commutator_algebra(As, Bs)
  @test isempty(bas)
  bas = @inferred Hecke._basis_of_commutator_algebra(Bs)
  @test bas == dense_matrix_type(F)[identity_matrix(F, 2)]
  bas = @inferred Hecke._basis_of_commutator_algebra(Bs[1])
  @test length(bas) == 2
  bas = @inferred Hecke._basis_of_commutator_algebra(As)
  @test length(bas) == 2

  F, z = cyclotomic_field(12, cached = false)
  As = dense_matrix_type(F)[matrix(F, 4, 4, [0 0 0 1; 0 0 -1 0; 0 1 0 0; -1 0 0 0])
                            matrix(F, 4, 4, [-1 0 0 0; 0 -1 0 0; 0 0 -1 0; 0 0 0 -1])
                            matrix(F, 4, 4, [1 0 0 0; 0 -z^4-1 0 0; 0 0 z^4 0; 0 0 0 1])]

  Bs = dense_matrix_type(F)[matrix(F, 2, 2, [0 1; -1 0])
                            matrix(F, 2, 2, [-1 0; 0 -1])
                            matrix(F, 2, 2, [-z^4-1 0; 0 z^4])]

  Cs = dense_matrix_type(F)[matrix(F, 1, 1, [z^3])
                            matrix(F, 1, 1, [-1])
                            matrix(F, 1, 1, [1])]

  @test length(Hecke._basis_of_commutator_algebra(As, Bs)) == 1
  @test length(Hecke._basis_of_commutator_algebra(As, Cs)) == 1
  @test length(Hecke._basis_of_commutator_algebra(Bs, Cs)) == 0

  # integral

  # the minimal polynomial of f if \Phi_5, mb is the "absolute representation matrix"
  # of a primitive 5-root of the unity. Then, changing the basis of the ZZLat on which
  # f acts, we can recover basis for which the induced action of f on the correspodning
  # hermitian lattice is given by multiplication by a 5-th root of the unity.
  # There are 4 of them and f is of order (size) 8, which is 4 times 2, so we should
  # get 8 matrices in the basis of the commutator algebra.

  f = matrix(QQ, 8, 8, [1 5 3 2 0 0 0 0; 0 -1 -1 -1 0 0 0 0; -2 -5 -1 0 0 0 0 0; 1 3 0 0 0 0 0 0; 0 0 0 0 1 5 3 2; 0 0 0 0 0 -1 -1 -1; 0 0 0 0 -2 -5 -1 0; 0 0 0 0 1 3 0 0])
  mb = matrix(QQ, 4, 4, [0 0 1 0; 0 0 0 1; -1 0 0 1; 0 -1 1 -1])
  bas = @inferred Hecke._basis_of_integral_commutator_algebra(f, mb)
  @test length(bas) == 8
  for i in 1:4
    @test bas[i][:, 1:4] == bas[i+4][:, 5:8]
  end

  As = QQMatrix[-identity_matrix(QQ, 3), identity_matrix(QQ, 3), identity_matrix(QQ, 3)]
  bas = @inferred Hecke._basis_of_integral_commutator_algebra(As, As)
  @test length(bas) == 9

end
