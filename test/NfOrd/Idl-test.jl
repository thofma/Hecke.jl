function test_NfOrd_Idl()
  print("Testing NfOrd/Idl ... ")

  Qx, x = PolynomialRing(FlintQQ, "x")

  K1, a1 = NumberField(x^3 - 2, "a")
  O1 = Order(K1, Hecke.FakeFmpqMat(ZZ[1 0 0; 0 2 0; 0 0 4], one(ZZ)))

  # construction

  I = @inferred ideal(O1, -17)
  @test order(I) == O1
  @test I.princ_gen_special[1] == 1
  @test I.princ_gen_special[2] == 17
  @test I.princ_gen == O1(-17)
  @test I.basis_mat == MatrixSpace(ZZ, 3, 3)(17)

  J = @inferred ideal(O1, ZZ(-17))
  @test order(J) == O1
  @test J.princ_gen_special[1] == 2
  @test J.princ_gen_special[3] == ZZ(17)
  @test J.princ_gen == O1(-17)
  @test J.basis_mat == MatrixSpace(ZZ, 3, 3)(17)

  K = @inferred ideal(O1, O1(-17))
  @test K.princ_gen == O1(-17)
  @test K.basis_mat == MatrixSpace(ZZ, 3, 3)(17)

  M = @inferred O1(-17)*O1
  L = @inferred O1*O1(-17)

  @test I == J && J == K && K == M && M == L && L == I

  # minimum

  @test 17 == @inferred minimum(I)
  @test 17 == @inferred minimum(J)
  @test 17 == @inferred minimum(K)
  @test 17 == @inferred minimum(I)
  @test 17 == @inferred minimum(J)
  @test 17 == @inferred minimum(K)

  # test

  @test 4913 == @inferred norm(I)
  @test 4913 == @inferred norm(J)
  @test 4913 == @inferred norm(K)
  @test 4913 == @inferred norm(I)
  @test 4913 == @inferred norm(J)
  @test 4913 == @inferred norm(K)

  # deepcopy

  L = @inferred deepcopy(I)
  @test L == I
  @test order(L) == O1

  # basis

  b = @inferred basis(I)
  @test b == NfOrdElem{NfOrdGen}[ O1(17), O1(34*a1), O1(68*a1^2) ]

  # basis matrix

  M = @inferred ideal(O1, O1(4*a1^2))

  b = @inferred basis_mat(M)
  @test b == ZZ[16 0 0; 0 16 0; 0 0 1]

  b = @inferred basis_mat_inv(M)
  @test b == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 1 0; 0 0 16], ZZ(16))

  b = @inferred basis_mat(M)
  @test b == ZZ[16 0 0; 0 16 0; 0 0 1]

  b = @inferred basis_mat_inv(M)
  @test b == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 1 0; 0 0 16], ZZ(16))

  # inclusion

  M = @inferred ideal(O1, O1(4*a1^2))
  @test @inferred in(O1(4*a1^2), M)
  @test @inferred !in(O1(2*a1), M)

  # binary

  K = @inferred I + J # I == J
  @test K == I
  K = @inferred ideal(O1, 15) + ideal(O1, 10)
  @test K == ideal(O1, 5)

  K = @inferred intersection(ideal(O1, 15), ideal(O1, 10))
  @test K == ideal(O1, 30)
  K = @inferred lcm(ideal(O1, 15), ideal(O1, 10))
  @test K == ideal(O1, 30)

  K = @inferred ideal(O1, 15) * ideal(O1, 10)
  @test K == ideal(O1, 150)
  K = @inferred ideal(O1, O1(2*a1)) * ideal(O1, O1(4*a1^2))
  @test K == ideal(O1, 16)

  # adhoc binary

  I = ideal(O1, O1(2*a1))
  J = ideal(O1, 3)
  K = ideal(O1, fmpz(3))

  @test ideal(O1, O1(10*a1)) == @inferred 5 * I
  @test ideal(O1, O1(10*a1)) == @inferred I * 5

  @test ideal(O1, O1(10*a1)) == @inferred fmpz(5) * I
  @test ideal(O1, O1(10*a1)) == @inferred I * fmpz(5)

  @test ideal(O1, 30) == @inferred 10 * J
  @test ideal(O1, 30) == @inferred J * 10

  @test ideal(O1, 30) == @inferred fmpz(10) * J
  @test ideal(O1, 30) == @inferred J * fmpz(10)

  @test ideal(O1, 30) == @inferred 10 * K
  @test ideal(O1, 30) == @inferred K * 10

  @test ideal(O1, 30) == @inferred fmpz(10) * K
  @test ideal(O1, 30) == @inferred K * fmpz(10)

  @test ideal(O1, O1(4*a1^2)) == @inferred I * O1(2*a1)
  @test ideal(O1, O1(4*a1^2)) == @inferred O1(2*a1) * I

  # idempotents

  I = ideal(O1, 2)
  J = ideal(O1, 3)
  e, f = @inferred idempotents(I, J)
  @test in(e, I)
  @test in(f, J)
  @test e + f == 1

  I = ideal(O1, O1(2*a1))
  J = ideal(O1, O1(1 - 2*a1))
  e, f = @inferred idempotents(I, J)
  @test in(e, I)
  @test in(f, J)
  @test e + f == 1

  @test_throws ErrorException idempotents(I, I)

  # modular reduction

  I = ideal(O1, 10)
  a = O1([11, 11, 11])
  b = @inferred mod(a, I)
  @test b == O1([1, 1, 1])

  I = ideal(O1, O1(2*a1 + 4*a1^2))
  a = O1([544, 1, 1])
  b = @inferred mod(a, I)
  @test iszero(b)

  c = [ Hecke.fmpz_preinvn_struct(fmpz(544)),
        Hecke.fmpz_preinvn_struct(fmpz(1)),
        Hecke.fmpz_preinvn_struct(fmpz(1)) ]

  b = @inferred mod(a, I, c)
  @test iszero(b)

  # pradical

  I = @inferred pradical(O1, 2)
  @test I == ideal(O1, ZZ[2 0 0; 0 1 0; 0 0 1])

  println("PASS")
end
