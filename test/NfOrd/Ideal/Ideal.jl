@testset "Ideal basics" begin
  Qx, x = polynomial_ring(QQ, "x")

  K1, a1 = number_field(x^3 - 2, "a")
  O1 = order(K1, Hecke.FakeFmpqMat(ZZ[1 0 0; 0 2 0; 0 0 4], one(ZZ)))

  K2, a2 = number_field(x^2 - 4^2*7^2*5, "a")
  O2 = order(K2, [K2(1), a2])

  @testset "Construction" begin
    I = @inferred ideal(O1, -17)
    @test order(I) == O1
    @test I.princ_gen_special[1] == 1
    @test I.princ_gen_special[2] == 17
    @test I.princ_gen == O1(-17)
    @test basis_matrix(I) == matrix_space(ZZ, 3, 3)(17)

    J = @inferred ideal(O1, ZZ(-17))
    @test order(J) == O1
    @test J.princ_gen_special[1] == 2
    @test J.princ_gen_special[3] == ZZ(17)
    @test J.princ_gen == O1(-17)
    @test basis_matrix(J) == matrix_space(ZZ, 3, 3)(17)

    K = @inferred ideal(O1, O1(-17))
    @test K.princ_gen == O1(-17)
    @test basis_matrix(K) == matrix_space(ZZ, 3, 3)(17)

    M = @inferred O1(-17)*O1
    L = @inferred O1*O1(-17)

    @test I == J && J == K && K == M && M == L && L == I

    I2 = @inferred ideal(O2, O2(1 + a2))

    Ib = basis(I2)
    II = ideal(O2, Ib)
    @test I2 == II

    @test is_zero(ideal(O1, 0))
    @test is_zero(ideal(O1, ZZ(0)))

    # ideal from vector of zeros should return the zero ideal
    @test is_zero(ideal(O1, [O1(0), O1(0)]))
  end

  I = ideal(O1, -17)
  J = ideal(O1, ZZ(-17))
  K = ideal(O1, O1(-17))
  M = O1(-17)*O1
  I2 = ideal(O2, O2(1 + a2))

  @testset "Minimum" begin
    @test 17 == @inferred minimum(I)
    @test 17 == @inferred minimum(J)
    @test 17 == @inferred minimum(K)
    @test 17 == @inferred minimum(I)
    @test 17 == @inferred minimum(J)
    @test 17 == @inferred minimum(K)

    # Test where gens are weakly normal and second generator is zero
    @testset begin
      R, x = polynomial_ring(QQ, "x")
      _K, _a = number_field(x, "a")
      _O = maximal_order(_K)
      _I = fractional_ideal(_O, _K(1))
      _J = _I*_K(QQFieldElem(-1, 5))
      @test minimum(numerator(_J)) == 1
    end
  end

  @testset "Norm" begin
    @test 4913 == @inferred norm(I)
    @test 4913 == @inferred norm(J)
    @test 4913 == @inferred norm(K)
    @test 4913 == @inferred norm(I)
    @test 4913 == @inferred norm(J)
    @test 4913 == @inferred norm(K)
  end

  @testset "Deepcopy" begin
    L = @inferred deepcopy(I)
    @test L == I
    @test order(L) == O1
  end

  @testset "Basis" begin
    b = @inferred basis(I)
    @test b == AbsSimpleNumFieldOrderElem[ O1(17), O1(34*a1), O1(68*a1^2) ]
  end

  @testset "Basismatrix" begin
    M = @inferred ideal(O1, O1(4*a1^2))

    b = @inferred basis_matrix(M)
    @test b == ZZ[16 0 0; 0 16 0; 0 0 1]

    b = @inferred basis_mat_inv(Hecke.FakeFmpqMat, M)
    @test b == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 1 0; 0 0 16], ZZ(16))

    b = @inferred basis_matrix(M)
    @test b == ZZ[16 0 0; 0 16 0; 0 0 1]

    b = @inferred basis_mat_inv(Hecke.FakeFmpqMat, M)
    @test b == Hecke.FakeFmpqMat(ZZ[1 0 0; 0 1 0; 0 0 16], ZZ(16))
  end

  @testset "Inclusion" begin
    M = @inferred ideal(O1, O1(4*a1^2))
    @test @inferred in(O1(4*a1^2), M)
    @test @inferred !in(O1(2*a1), M)
  end

  @testset "Modular reduction" begin
    I = ideal(O1, 10)
    a = O1([11, 11, 11])
    b = @inferred mod(a, I)
    @test b == O1([1, 1, 1])

    I = ideal(O1, O1(2*a1 + 4*a1^2))
    a = O1([544, 1, 1])
    b = @inferred mod(a, I)
    @test iszero(b)

    c = [ Hecke.fmpz_preinvn_struct(ZZRingElem(544)),
          Hecke.fmpz_preinvn_struct(ZZRingElem(1)),
          Hecke.fmpz_preinvn_struct(ZZRingElem(1)) ]

    b = @inferred mod(a, I, c)
    @test iszero(b)
  end

  @testset "p-Radical" begin
    I = @inferred pradical(O1, 2)
    @test I == ideal(O1, ZZ[2 0 0; 0 1 0; 0 0 1])

    # An order which does not contain the equation order
    P, x = polynomial_ring(QQ)
    f = x^5 + x^3 - x^2 - x - 1
    K, a = number_field(f)
    R = maximal_order(K)
    OO = order(K, basis(5*R))
    pradical(OO, 2)
  end

  @testset "Is principal" begin
    Qx, x = QQ["x"]
    f = x^2 - 5
    K, a = number_field(f, "a")
    OK = maximal_order(K)
    P = first(keys(factor(3 * OK)))
    fl, x = is_principal_fac_elem(P)
    @test fl
    @test OK(evaluate(x)) * OK == P
  end

  @testset "Gens" begin
    Qx, x = QQ["x"]
    f = x^2 - 5
    K, a = number_field(f, "a")
    OK = maximal_order(K)
    P = first(keys(factor(3 * OK)))
    lG = gens(P)
    @test ideal(OK, lG) == P

    Kns, gKns = number_field([x^2+5, x^2+7])
    OK = maximal_order(Kns)
    P = prime_decomposition(OK, 11)[1][1]
    @test ideal(OK, gens(P)) == P
    @test ideal(OK, gens(ideal(OK, basis_matrix(P)))) == P
  end

  # Some issue with ideal(O, M)
  K, a = quadratic_field(-1)
  O = maximal_order(K)
  @test basis_matrix(ideal(O, representation_matrix(O(a)))) == identity_matrix(ZZ, 2)

  # zero ideals, #1330
  let
    OK = maximal_order(quadratic_field(-1, cached = false)[1])
    I = 0 * OK
    @test basis_matrix(I) == zero_matrix(ZZ, 0, 2)
    @test basis(I) == elem_type(OK)[]
    @test is_zero(I)
    @test !is_zero(1 * OK)
    I = ideal(OK, zero_matrix(ZZ, 0, 2))
    @test is_zero(I)
    @test is_zero(I)
    @test minimum(I) == 0
    @test idempotents(I, 2*OK + 3 * OK) == (0, 1)
    @test idempotents(2*OK + 3 * OK, I) == (1, 0)
    @test is_coprime(2*OK + 3 * OK, I)
    I = ideal(OK, identity_matrix(ZZ, 2))
    @test !is_zero(I)
    @test !is_zero(I)
  end

  # zero ideals constructed from basis matrices or Z-generators, #2377
  let
    K, = quadratic_field(-1, cached = false)
    O = equation_order(K)
    Z = ideal(O, zero(O))
    ideals = [
      ideal(O, zero_matrix(ZZ, 2, 2)),
      Hecke.ideal_from_z_gens(O, [zero(O), zero(O)]),
      Hecke.ideal_from_z_gens(O, [zero(O)]),
      Hecke.ideal_from_z_gens(O, elem_type(O)[]),
      0 * ideal(O, one(O)),
    ]
    for I in ideals
      @test basis_matrix(I) == zero_matrix(ZZ, 0, 2)
      @test is_zero(I)
      @test I == Z
    end

    I = ideal(O, ZZ[0 0; 1 0; 0 1])
    @test basis_matrix(I) == identity_matrix(ZZ, 2)

    Qx, x = polynomial_ring(QQ, "x")
    K, = number_field(x, "a")
    O = equation_order(K)
    I = ideal(O, zero_matrix(ZZ, 1, 1))
    @test basis_matrix(I) == zero_matrix(ZZ, 0, 1)
    @test minimum(I) == 0
    @test norm(I) == 0
  end

  let
    P, x = polynomial_ring(ZZ)
    K, a = number_field(x^3 + x + 1)
    R = maximal_order(K)
    OO = order(K, basis(2*R))
    I = ideal(OO, [OO(x) for x in basis(2*R)])
    G = gens(I)
    @test I == ideal(OO, G)
  end

  # parent
  let
    Qx, x = polynomial_ring(QQ, "x")
    K, a = number_field(x^3 - 2, "a")
    O = equation_order(K)
    @test parent(1*O) == parent(1*O)
    @test hash(parent(1*O)) == hash(parent(1*O))
  end

  let
    Qx, x = polynomial_ring(QQ, "x")
    K, a = number_field(x^3 - 2, "a")
    O = equation_order(K)
    @test sprint(show, 2*O) isa String
    @test sprint(show, "text/plain", 2*O) isa String
    @test sprint(show, 2*O + 4*O) isa String
    @test sprint(show, "text/plain", 2*O + 4*O) isa String

    OK = maximal_order(K)
    p = prime_decomposition(OK, 2)
    @test sprint(show, p) isa String
    @test sprint(show, "text/plain", p) isa String
  end

  # ideals up to
  let
    Qx, x = polynomial_ring(QQ, "x")
    K, a = number_field(x^2 - 5, "a")
    O = equation_order(K)
    OK = maximal_order(K)
    l = @inferred Hecke.ideals_up_to(OK, 50)
    @test length(l) == 22
    @test length(unique(l)) == 22
    l = @inferred Hecke.ideals_up_to(O, 50)
    @test length(l) == 45
    @test length(unique(l)) == 45
  end

  # lll
  let
    R, x = polynomial_ring(QQ, :x)
    K, a = number_field(x^3-7);
    OK = maximal_order(K);
    B = lll_basis(3*OK)
    @test length(B) == 3

    @test length(Hecke.lll_basis_profile(3*OK)) == 3
  end

  let # simplify with evil defining polynomials
    QQx, x = QQ[:x]
    f = x^2 + 1//45
    for i in 1:10
      k, _ = number_field(f; cached = false)
      ok = maximal_order(k)
      P, = prime_ideals_over(ok, 3)
      Q, = prime_ideals_over(ok, 5)
      I = P * Q
      II = simplify(I)
      @test I == II
    end
  end
end
