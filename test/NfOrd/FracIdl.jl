Qx, x = polynomial_ring(FlintQQ, "x")
K2, a2 = number_field(x^3 - 2, "a1")
K3, (a3,) = number_field([x^3 - 2], "a2")
@testset "Fractional ideals for $K1" for (K1, a1) in [(K2, a2), (K3, a3)]
  O1 = Order(K1, Hecke.Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 2 0; 0 0 4], one(FlintZZ)))

  i = ideal(O1, O1(2*a1))

  @testset "Construction" begin
    I = @inferred fractional_ideal(O1, i)
    @test basis_matrix(Hecke.FakeFmpqMat, I) == Hecke.Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(1))
    @test basis_mat_inv(Hecke.FakeFmpqMat, I) == Hecke.Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 16 0; 0 0 16], ZZRingElem(16))

    J = @inferred fractional_ideal(O1, i, 2)
    @test basis_matrix(Hecke.FakeFmpqMat, J) == Hecke.Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2))
    @test basis_mat_inv(Hecke.FakeFmpqMat, J) == Hecke.Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 16 0; 0 0 16], ZZRingElem(8))

    K = @inferred fractional_ideal(O1, FlintZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2))
    @test isdefined(K, :basis_matrix)
    @test basis_matrix(Hecke.FakeFmpqMat, K) == Hecke.Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2))
    @test basis_mat_inv(Hecke.FakeFmpqMat, K) == Hecke.Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 16 0; 0 0 16], ZZRingElem(8))

    L = @inferred fractional_ideal(O1, Hecke.Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2)))
    @test L.basis_matrix == Hecke.Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2))
    @test basis_matrix(Hecke.FakeFmpqMat, L) == Hecke.Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2))
    @test basis_mat_inv(Hecke.FakeFmpqMat, L) == Hecke.Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 16 0; 0 0 16], ZZRingElem(8))

    M = @inferred fractional_ideal(O1, 2*a1//2)
    @test basis_matrix(Hecke.FakeFmpqMat, M) == Hecke.Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2))
    @test basis_mat_inv(Hecke.FakeFmpqMat, M) == Hecke.Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 16 0; 0 0 16], ZZRingElem(8))

    @test J == K
    @test K == L
    @test L == M
    @test M == J
  end

  J = fractional_ideal(O1, i, 2)
  K = fractional_ideal(O1, FlintZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2))
  L = fractional_ideal(O1, Hecke.Hecke.FakeFmpqMat(FlintZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2)))
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

    @test basis_matrix(N) == QQMatrix(Hecke.Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 2 0; 0 0 2], ZZRingElem(1)))
  end

  @testset "Denominator" begin
    # This was once a bug found by Johannes
    @testset begin
      R, x = polynomial_ring(FlintQQ, "x")
      K, a = number_field(x, "a")
      O = maximal_order(K)
      I = Hecke.AbsSimpleNumFieldOrderFractionalIdeal(ideal(O, O(2)), ZZRingElem(2))
      @test denominator(I) == ZZRingElem(2)
      basis_matrix(Hecke.FakeFmpqMat, I)
      @test denominator(I) == ZZRingElem(2)
    end
  end

  let
    K, = quadratic_field(-1, cached = false)
    OK = maximal_order(K)
    I = zero(K) * OK
    @test basis_matrix(I) == zero_matrix(ZZ, 0, 2)
    @test basis(I) == elem_type(K)[]
    @test is_zero(I)
    I = one(K) * OK
    @test !is_zero(K)
  end
end
