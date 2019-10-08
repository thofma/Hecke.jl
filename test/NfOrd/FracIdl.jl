Qx, x = PolynomialRing(FlintQQ, "x")
K2, a2 = NumberField(x^3 - 2, "a1")
K3, (a3,) = NumberField([x^3 - 2], "a2")
@testset "Fractional ideals for $K1" for (K1, a1) in [(K2, a2), (K3, a3)] 
  O1 = Order(K1, Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 2 0; 0 0 4], one(FlintZZ)))

  i = ideal(O1, O1(2*a1))

  @testset "Construction" begin
    I = @inferred fractional_ideal(O1, i)
    @test basis_matrix(I) == Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], fmpz(1))
    @test basis_mat_inv(I) == Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 16 0; 0 0 16], fmpz(16))

    J = @inferred fractional_ideal(O1, i, 2)
    @test basis_matrix(J) == Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
    @test basis_matrix(J) == Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
    @test basis_matrix(J) == Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
    @test basis_mat_inv(J) == Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 16 0; 0 0 16], fmpz(8))
    @test basis_mat_inv(J) == Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 16 0; 0 0 16], fmpz(8))

    K = @inferred fractional_ideal(O1, FlintZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
    @test K.basis_matrix == Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
    @test basis_matrix(K) == Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
    @test basis_mat_inv(K) == Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 16 0; 0 0 16], fmpz(8))
    @test basis_mat_inv(K) == Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 16 0; 0 0 16], fmpz(8))

    L = @inferred fractional_ideal(O1, Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2)))
    @test L.basis_matrix == Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
    @test basis_matrix(L) == Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
    @test basis_mat_inv(L) == Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 16 0; 0 0 16], fmpz(8))
    @test basis_mat_inv(L) == Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 16 0; 0 0 16], fmpz(8))

    M = @inferred fractional_ideal(O1, 2*a1//2)
    @test M.basis_matrix == Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
    @test basis_matrix(M) == Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
    @test basis_mat_inv(M) == Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 16 0; 0 0 16], fmpz(8))
    @test basis_mat_inv(M) == Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 16 0; 0 0 16], fmpz(8))

    @test J == K
    @test K == L
    @test L == M
    @test M == J
  end

  J = fractional_ideal(O1, i, 2)
  K = fractional_ideal(O1, FlintZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2))
  L = fractional_ideal(O1, Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], fmpz(2)))
  M = fractional_ideal(O1, 2*a1//2)

  @testset "Basis" begin
    b = @inferred basis(J)
    @test b == [ K1(8), a1, 2*a1^2 ]
    b = @inferred basis(K)
    @test b == [ K1(8), a1, 2*a1^2 ]
    b = @inferred basis(L)
    @test b == [ K1(8), a1, 2*a1^2 ]
    b = @inferred basis(M)
    @test b == [ K1(8), a1, 2*a1^2 ]
  end

  @testset "Norm" begin
    b = @inferred norm(J)
    @test b == FlintQQ(16, 2^3)
  end

  @testset "Ring of multipliers" begin
    i = ideal(O1, FlintZZ[2 0 0; 0 1 0; 0 0 1])
    N = @inferred ring_of_multipliers(i)

    @test basis_matrix(N) == Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 2 0; 0 0 2], fmpz(1))
  end

  @testset "Denominator" begin
    # This was once a bug found by Johannes
    @testset begin
      R, x = PolynomialRing(FlintQQ, "x")
      K, a = NumberField(x, "a")
      O = maximal_order(K)
      I = Hecke.NfOrdFracIdl(ideal(O, O(2)), fmpz(2))
      @test denominator(I) == fmpz(2)
      basis_matrix(I)
      @test denominator(I) == fmpz(2)
    end
  end
end
