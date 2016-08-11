function test_NfOrd_FracIdl()
  print("Testing NfOrd/FracIdl ... ")

  Qx, x = PolynomialRing(FlintQQ, "x")

  K1, a1 = NumberField(x^3 - 2, "a")
  O1 = Order(K1, Hecke.FakeFmpqMat(ZZ[1 0 0; 0 2 0; 0 0 4], one(ZZ)))

  i = ideal(O1, O1(2*a1))

  # construction

  I = @inferred frac_ideal(O1, i)
  @test I.basis_mat == Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], fmpz(1))
  @test basis_mat_inv(I) == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 16 0; 0 0 16], fmpz(16))

  J = @inferred frac_ideal(O1, i, 2)
  @test J.basis_mat == Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
  @test basis_mat(J) == Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
  @test basis_mat(J) == Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
  @test basis_mat_inv(J) == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 16 0; 0 0 16], fmpz(8))
  @test basis_mat_inv(J) == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 16 0; 0 0 16], fmpz(8))

  K = @inferred frac_ideal(O1, ZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
  @test K.basis_mat == Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
  @test basis_mat(K) == Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
  @test basis_mat_inv(K) == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 16 0; 0 0 16], fmpz(8))
  @test basis_mat_inv(K) == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 16 0; 0 0 16], fmpz(8))

  L = @inferred frac_ideal(O1, Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2)))
  @test L.basis_mat == Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
  @test basis_mat(L) == Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
  @test basis_mat_inv(L) == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 16 0; 0 0 16], fmpz(8))
  @test basis_mat_inv(L) == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 16 0; 0 0 16], fmpz(8))

  M = @inferred frac_ideal(O1, 2*a1//2)
  @test M.basis_mat == Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
  @test basis_mat(M) == Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
  @test basis_mat_inv(M) == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 16 0; 0 0 16], fmpz(8))
  @test basis_mat_inv(M) == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 16 0; 0 0 16], fmpz(8))

  @test J == K
  @test K == L
  @test L == M
  @test M == J

  # basis

  b = @inferred basis(J)
  @test b == [ K1(8), a1, 2*a1^2 ]
  b = @inferred basis(K)
  @test b == [ K1(8), a1, 2*a1^2 ]
  b = @inferred basis(L)
  @test b == [ K1(8), a1, 2*a1^2 ]
  b = @inferred basis(M)
  @test b == [ K1(8), a1, 2*a1^2 ]

  # norm

  b = @inferred norm(J)
  @test b == QQ(16, 2^3)

  # colon

  i = ideal(O1, ZZ[2 0 0; 0 1 0; 0 0 1])
  N = @inferred ring_of_multipliers(i)

  @test basis_mat(N) == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 2 0; 0 0 2], fmpz(1))

  println("PASS")
end
