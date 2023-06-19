@testset "Ramification" begin
  K, a = Hecke.rationals_as_number_field()
  Q = Hecke.quaternion_algebra2(K, -1, -1)
  @test (@inferred Hecke.ramified_infinite_places(Q)) == real_places(K)

  Q = Hecke.quaternion_algebra2(QQ, -1, -1)
  QQQ = direct_product(Q, Q)[1]
  C, = center(QQQ)
  flds = first.(Hecke.components(Hecke.Field, C))
  @test (@inferred Hecke.ramified_infinite_places_of_center(QQQ)) == real_places.(flds)

  Q = matrix_algebra(QQ, 3)
  @test (@inferred schur_index(Q, inf)) == 1
  @test iseichler(Q)

  # Test (-1, -1/QQ)
  Q = Hecke.AlgQuat(QQ, QQ(-1), QQ(-1))
  @test !issplit(Q, 2)
  @test schur_index(Q, 2) == 2
  @test schur_index(Q, ZZ(2)) == 2
  @test schur_index(Q, inf) == 2
  @test !issplit(Q, inf)
  @test schur_index(Q, 3) == 1
  @test schur_index(Q, ZZ(3)) == 1
  @test issplit(Q, ZZ(3))
  @test schur_index(Q) == 2
  @test !issplit(Q)
  @test !iseichler(Q)

  Q, = AlgAss(Q)
  @test !issplit(Q, 2)
  @test schur_index(Q, 2) == 2
  @test schur_index(Q, ZZ(2)) == 2
  @test schur_index(Q, inf) == 2
  @test !issplit(Q, inf)
  @test schur_index(Q, 3) == 1
  @test schur_index(Q, ZZ(3)) == 1
  @test issplit(Q, ZZ(3))
  @test schur_index(Q) == 2
  @test !issplit(Q)
  @test !iseichler(Q)

  # Test Mat_2((-1, -1)/QQ)
  Q = Hecke.AlgQuat(QQ, QQ(-1), QQ(-1))
  A = matrix_algebra(QQ, Q, 2)
  @test !issplit(A, 2)
  @test schur_index(A, 2) == 2
  @test schur_index(A, ZZ(2)) == 2
  @test schur_index(A, inf) == 2
  @test !issplit(A, inf)
  @test schur_index(A, 3) == 1
  @test schur_index(A, ZZ(3)) == 1
  @test issplit(A, ZZ(3))
  @test schur_index(A) == 2
  @test !issplit(A)
  @test iseichler(A)

  K, = Hecke.rationals_as_number_field()
  OK = maximal_order(K)
  # Test (-1, -1; QQ)
  Q = Hecke.AlgQuat(K, K(-1), K(-1))
  p2 = prime_decomposition(OK, 2)[1][1]
  p3 = prime_decomposition(OK, 3)[1][1]
  rlp = real_places(K)[1]
  @test !issplit(Q, p2)
  @test schur_index(Q, p2) == 2
  @test schur_index(Q, rlp) == 2
  @test !issplit(Q, rlp)
  @test schur_index(Q, p3) == 1
  @test issplit(Q, p3)
  @test schur_index(Q) == 2
  @test !issplit(Q)
  @test !iseichler(Q)

  Q, = AlgAss(Q)
  @test !issplit(Q, p2)
  @test schur_index(Q, p2) == 2
  @test schur_index(Q, rlp) == 2
  @test !issplit(Q, rlp)
  @test schur_index(Q, p3) == 1
  @test issplit(Q, p3)
  @test schur_index(Q) == 2
  @test !issplit(Q)
  @test !iseichler(Q)

  A = Hecke.AlgQuat(QQ, QQ(1), QQ(1))
  @test schur_index(A) == 1
  @test issplit(A)
  @test iseichler(A)
  A = Hecke.AlgQuat(K, K(1), K(1))
  @test schur_index(A) == 1
  @test issplit(A)
  @test iseichler(A)

  K, = quadratic_field(5)
  A = Hecke.AlgQuat(K, K(1), K(1))
  @test schur_index(A) == 1
  @test issplit(A)
  @test iseichler(A)

  K, = quadratic_field(5)
  A = Hecke.AlgQuat(K, K(-1), K(-1))
  @test schur_index(A) == 2
  @test !issplit(A)
  @test !iseichler(A)

  A = matrix_algebra(K, 3)
  @test iseichler(A)

  Qx, x = QQ["x"]
  K, a = number_field(x^3 - 2, "a")
  A = Hecke.AlgQuat(K, K(-1), K(-1))
  @test schur_index(A) == 2
  @test !issplit(A)
  @test iseichler(A)
  p = complex_places(K)
  @test issplit(A, p[1])

  A = matrix_algebra(QQ, 2)
  @test schur_index(A) == 1

  @testset "ignore complex embeddings" begin
    # The schur index of QQ[i]^{2×2} is 1
    # Test this for various ways of writing QQ[i]^{2×2}

    QQi, i = cyclotomic_field(4, :i)
    QQi2x2 = matrix_algebra(QQi, 2)
    QQi2x2i = AlgAss(QQi, i .* multiplication_table(QQi2x2))
    QQi2x2ip1 = AlgAss(QQi, (i+1) .* multiplication_table(QQi2x2))

    @test schur_index(QQi2x2) == 1 # harmless
    @test schur_index(QQi2x2i) == 1
    @test schur_index(QQi2x2ip1) == 1

    # A usecase where QQi2x2i can pop up
    X = zero_matrix(QQ, 4, 4)
    Y = zero_matrix(QQ, 4, 4)
    IM = QQ[0 -1;1 0]
    X[1:2,1:2] = Y[1:2,3:4] = Y[3:4,1:2] = IM
    QQIM2x2 = matrix_algebra(QQ, [X, Y])
    QQIM2x2overQQi = Hecke._as_algebra_over_center(AlgAss(QQIM2x2)[1])[1]

    @test schur_index(QQIM2x2overQQi) == 1
  end
end
