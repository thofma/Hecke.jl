@testset "Ideals" begin
  global Qx, x = PolynomialRing(FlintQQ, "x")

  global K1, a1 = NumberField(x^3 - 2, "a")
  global O1 = Order(K1, Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 2 0; 0 0 4], one(FlintZZ)))

  global K2, a2 = NumberField(x^2 - 4^2*7^2*5, "a")
  global O2 = Order(K2, [K2(1), a2])

  @testset "Construction" begin
    I = @inferred ideal(O1, -17)
    @test order(I) == O1
    @test I.princ_gen_special[1] == 1
    @test I.princ_gen_special[2] == 17
    @test I.princ_gen == O1(-17)
    @test basis_mat(I) == MatrixSpace(FlintZZ, 3, 3)(17)

    J = @inferred ideal(O1, FlintZZ(-17))
    @test order(J) == O1
    @test J.princ_gen_special[1] == 2
    @test J.princ_gen_special[3] == FlintZZ(17)
    @test J.princ_gen == O1(-17)
    @test basis_mat(J) == MatrixSpace(FlintZZ, 3, 3)(17)

    K = @inferred ideal(O1, O1(-17))
    @test K.princ_gen == O1(-17)
    @test basis_mat(K) == MatrixSpace(FlintZZ, 3, 3)(17)

    M = @inferred O1(-17)*O1
    L = @inferred O1*O1(-17)

    @test I == J && J == K && K == M && M == L && L == I

    I2 = @inferred ideal(O2, O2(1 + a2))
  end

  I = ideal(O1, -17)
  J = ideal(O1, FlintZZ(-17))
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
      R, x = PolynomialRing(FlintQQ, "x")
      _K, _a = NumberField(x, "a")
      _O = maximal_order(_K)
      _I = frac_ideal(_O, _K(1))
      _J = _I*_K(fmpq(-1, 5))
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
    @test b == NfOrdElem[ O1(17), O1(34*a1), O1(68*a1^2) ]
  end

  @testset "Basismatrix" begin
    M = @inferred ideal(O1, O1(4*a1^2))

    b = @inferred basis_mat(M)
    @test b == FlintZZ[16 0 0; 0 16 0; 0 0 1]

    b = @inferred basis_mat_inv(M)
    @test b == Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 1 0; 0 0 16], FlintZZ(16))

    b = @inferred basis_mat(M)
    @test b == FlintZZ[16 0 0; 0 16 0; 0 0 1]

    b = @inferred basis_mat_inv(M)
    @test b == Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 1 0; 0 0 16], FlintZZ(16))
  end

  @testset "Inclusion" begin
    M = @inferred ideal(O1, O1(4*a1^2))
    @test @inferred in(O1(4*a1^2), M)
    @test @inferred !in(O1(2*a1), M)
  end

  @testset "Binary operations" begin
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
  end

  @testset "Ad hoc binary operations" begin
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
  end

  @testset "Idempotents" begin
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

    c = [ Hecke.fmpz_preinvn_struct(fmpz(544)),
          Hecke.fmpz_preinvn_struct(fmpz(1)),
          Hecke.fmpz_preinvn_struct(fmpz(1)) ]

    b = @inferred mod(a, I, c)
    @test iszero(b)
  end

  @testset "p-Radical" begin
    I = @inferred pradical(O1, 2)
    @test I == ideal(O1, FlintZZ[2 0 0; 0 1 0; 0 0 1])
  end

  include("Ideal/Prime.jl")
end
