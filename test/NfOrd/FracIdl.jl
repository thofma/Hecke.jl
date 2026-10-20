Qx, x = polynomial_ring(QQ, "x")
K2, a2 = number_field(x^3 - 2, "a1")
K3, (a3,) = number_field([x^3 - 2], "a2")
@testset "Fractional ideal types" begin
  K4, _ = number_field([x^2 - 2, x^2 - 3])
  for K in (K2, K3, K4)
    O = equation_order(K)
    I = fractional_ideal(O, 1)
    @test Hecke.field(O) === K
    @test fractional_ideal(I) === I
    @test (@inferred Hecke.fractional_ideal_type(O)) === typeof(I)
    @test (@inferred Hecke.fractional_ideal_type(typeof(O))) === typeof(I)
  end
end

@testset "Non-simple ideal scaling and membership" begin
  L, _ = quadratic_field(-1)
  OL = maximal_order(L)
  for polys in ([x^2 + 5], [x^2 + 5, x^2 + 7])
    K, a = number_field(polys)
    for O in (equation_order(K), maximal_order(K))
      I = ideal(O, 2, O(1 + a[1]))
      if Hecke.is_maximal_known_and_maximal(O)
        Hecke.assure_2_normal(I)
      end
      for A in (I, ideal(O, basis_matrix(I)))
        for n in (1, -1, 2, -3)
          for B in (A*n, n*A, A*ZZ(n), ZZ(n)*A)
            @test basis_matrix(B) == abs(n)*basis_matrix(A)
            @test norm(B) == abs(n)^degree(K)*norm(A)
          end
        end
        @test iszero(A*0)
        @test iszero(ZZ(0)*A)
        @test A*O(2) == A*2
        @test O(2)*A == A*2
      end
      J = fractional_ideal(O, I, 2)
      @test basis_matrix(Hecke.simplify(J*K(2))) == basis_matrix(I)
      @test K(2) in I
      @test !(K(1) in I)
      @test K(1) in J
      @test !(K(1//2) in J)
      @test O(1) in J
      @test 1 in J
      @test ZZ(1) in J
      @test_throws ArgumentError L(1) in I
      @test_throws ArgumentError L(1) in J
      @test_throws ArgumentError OL(1)*I
      @test_throws ArgumentError I*OL(1)
      for b in basis(I)
        @test b in I
        @test b//2 in J
      end
    end
  end
end

@testset "Fractional ideals for $K1" for (K1, a1) in [(K2, a2), (K3, a3)]
  O1 = order(K1, Hecke.FakeFmpqMat(ZZ[1 0 0; 0 2 0; 0 0 4], one(ZZ)))

  i = ideal(O1, O1(2*a1))

  @testset "Construction" begin
    I = @inferred fractional_ideal(O1, i)
    @test basis_matrix(Hecke.FakeFmpqMat, I) == Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(1))
    @test basis_mat_inv(Hecke.FakeFmpqMat, I) == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 16 0; 0 0 16], ZZRingElem(16))

    J = @inferred fractional_ideal(O1, i, 2)
    @test basis_matrix(Hecke.FakeFmpqMat, J) == Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2))
    @test basis_mat_inv(Hecke.FakeFmpqMat, J) == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 16 0; 0 0 16], ZZRingElem(8))

    K = @inferred fractional_ideal(O1, ZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2))
    @test isdefined(K, :basis_matrix)
    @test basis_matrix(Hecke.FakeFmpqMat, K) == Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2))
    @test basis_mat_inv(Hecke.FakeFmpqMat, K) == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 16 0; 0 0 16], ZZRingElem(8))

    L = @inferred fractional_ideal(O1, Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2)))
    @test L.basis_matrix == Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2))
    @test basis_matrix(Hecke.FakeFmpqMat, L) == Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2))
    @test basis_mat_inv(Hecke.FakeFmpqMat, L) == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 16 0; 0 0 16], ZZRingElem(8))

    LL = @inferred fractional_ideal(O1, QQ[8 0 0; 0 1//2 0; 0 0 1//2])
    @test LL.basis_matrix == Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2))
    @test basis_matrix(Hecke.FakeFmpqMat, LL) == Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2))
    @test basis_mat_inv(Hecke.FakeFmpqMat, LL) == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 16 0; 0 0 16], ZZRingElem(8))

    M = @inferred fractional_ideal(O1, 2*a1//2)
    @test basis_matrix(Hecke.FakeFmpqMat, M) == Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2))
    @test basis_mat_inv(Hecke.FakeFmpqMat, M) == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 16 0; 0 0 16], ZZRingElem(8))

    @test J == K
    @test K == L
    @test L == M
    @test M == J

    I = fractional_ideal(O1, K1(2))
    @test I == fractional_ideal(O1, 2)
    @test I == fractional_ideal(O1, ZZ(2))
    @test I == fractional_ideal(O1, O1(2))
    @test I == fractional_ideal(O1, BigInt(2))
  end

  J = fractional_ideal(O1, i, 2)
  K = fractional_ideal(O1, ZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2))
  L = fractional_ideal(O1, Hecke.FakeFmpqMat(ZZ[16 0 0; 0 1 0; 0 0 1], ZZRingElem(2)))
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

    b = basis(J)
    @test b !== basis(J)
    @test basis(J, copy = false) === basis(J, copy = false)
  end

  @testset "Norm" begin
    b = @inferred norm(J)
    @test b == QQ(16, 2^3)
  end

  @testset "Ring of multipliers" begin
    i = ideal(O1, ZZ[2 0 0; 0 1 0; 0 0 1])
    N = @inferred ring_of_multipliers(i)

    @test basis_matrix(N) == QQMatrix(Hecke.FakeFmpqMat(ZZ[1 0 0; 0 2 0; 0 0 2], ZZRingElem(1)))
  end

  @testset "Denominator" begin
    # This was once a bug found by Johannes
    @testset begin
      R, x = polynomial_ring(QQ, "x")
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

  # zero ideals constructed from basis matrices, #2377
  let
    K, = quadratic_field(-1, cached = false)
    O = equation_order(K)
    for I in (fractional_ideal(O, zero_matrix(QQ, 2, 2)),
              fractional_ideal(O, zero_matrix(ZZ, 2, 2)))
      @test basis_matrix(I) == zero_matrix(QQ, 0, 2)
      @test is_zero(I)
    end
  end

  # hashing
  let
    K, = quadratic_field(-1, cached = false)
    OK = maximal_order(K)
    I = zero(K) * OK
    @test parent(I) == parent(zero(K) * OK)
    @test hash(parent(I)) == hash(parent(zero(K) * OK))
  end

  # principality testing for non-maximal orders #1833
  let
    _, x = QQ[:x]
    O = equation_order(x^2 - 5)
    fl, a = is_principal_with_data(fractional_ideal(O, [one(number_field(O))]))
    @test fl && (a*O == 1*O)
  end

  let # printing
    Qx, x = polynomial_ring(QQ, "x")
    K, a = number_field(x^3 - 2, "a")
    O = equation_order(K)
    @test sprint(show, K(2)*O) isa String
    @test sprint(show, "text/plain", 2*O) isa String
    @test sprint(show, K(2)*O + K(4)*O) isa String
    @test sprint(show, "text/plain", K(2)*O + K(4)*O) isa String

    OK = maximal_order(K)
    p = prime_decomposition(OK, 2)[1][1]
    @test sprint(show, fractional_ideal(p, ZZ(3))) isa String
    @test sprint(show, "text/plain", fractional_ideal(p, ZZ(3))) isa String
  end

  let # subset
    Qx, x = polynomial_ring(QQ, "x")
    K, a = number_field(x^3 - 2, "a")
    O = maximal_order(K)
    @test is_subset(K(0) * O, K(1) * O)
    @test !is_subset(K(1) * O, K(0) * O)
    @test is_subset(K(0) * O, K(0) * O)
    @test is_subset(K(2) * O, K(1) * O)
    @test is_subset(K(4) * O, K(2) * O)
    @test !is_subset(K(4) * O, K(3) * O)
  end
end

@testset "Fractional ideal Trace" begin
  x = polynomial_ring(QQ, "x")[2]
  K, t = number_field(x^2 - 2, :t)
  O = maximal_order(K)

  @test @inferred tr(K(1) * O) == 2
  @test @inferred tr(K(1//2) * O) == 1
  @test @inferred tr(K(1//4) * O) == 1//2
  @test @inferred tr(inv(different(O))) == 1

  K, t = number_field(x^2 + 23, :t)
  O = maximal_order(K)
  @test @inferred tr(inv(different(O))) == 1
  @test @inferred tr(ideal(O, 1)//2) == 1//2
  @test @inferred tr(ideal(O, 3)//2) == 3//2

  @test @inferred tr(K(0) * O) == 0
  @test @inferred tr(ideal(O, 0)//2) == 0
end
