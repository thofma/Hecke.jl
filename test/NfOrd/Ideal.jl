@testset "Ideals" begin
   Qx, x = PolynomialRing(FlintQQ, "x")

   K1, a1 = NumberField(x^3 - 2, "a")
   O1 = Order(K1, Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 2 0; 0 0 4], one(FlintZZ)))

   K2, a2 = NumberField(x^2 - 4^2*7^2*5, "a")
   O2 = Order(K2, [K2(1), a2])

  @testset "Construction" begin
    I = @inferred ideal(O1, -17)
    @test order(I) == O1
    @test I.princ_gen_special[1] == 1
    @test I.princ_gen_special[2] == 17
    @test I.princ_gen == O1(-17)
    @test basis_matrix(I) == MatrixSpace(FlintZZ, 3, 3)(17)

    J = @inferred ideal(O1, FlintZZ(-17))
    @test order(J) == O1
    @test J.princ_gen_special[1] == 2
    @test J.princ_gen_special[3] == FlintZZ(17)
    @test J.princ_gen == O1(-17)
    @test basis_matrix(J) == MatrixSpace(FlintZZ, 3, 3)(17)

    K = @inferred ideal(O1, O1(-17))
    @test K.princ_gen == O1(-17)
    @test basis_matrix(K) == MatrixSpace(FlintZZ, 3, 3)(17)

    M = @inferred O1(-17)*O1
    L = @inferred O1*O1(-17)

    @test I == J && J == K && K == M && M == L && L == I

    I2 = @inferred ideal(O2, O2(1 + a2))

    Ib = basis(I2)
    II = ideal(O2, Ib)
    @test I2 == II
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
      _I = fractional_ideal(_O, _K(1))
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

    b = @inferred basis_matrix(M)
    @test b == FlintZZ[16 0 0; 0 16 0; 0 0 1]

    b = @inferred basis_mat_inv(M)
    @test b == Hecke.FakeFmpqMat(FlintZZ[1 0 0; 0 1 0; 0 0 16], FlintZZ(16))

    b = @inferred basis_matrix(M)
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

    K = @inferred intersect(ideal(O1, 15), ideal(O1, 10))
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

  @testset "Prime Decomposition" begin
    L = NumberField(x^30-x^29+x^28-x^27+x^26+743*x^25-1363*x^24-3597*x^23-22009*x^22+458737*x^21+2608403*x^20+6374653*x^19-1890565*x^18-112632611*x^17-467834081*x^16-1365580319*x^15-1188283908*x^14+3831279180*x^13+28661663584*x^12+89106335984*x^11+226912479680*x^10+443487548480*x^9+719797891328*x^8+946994403328*x^7+1015828094976*x^6+878645952512*x^5+555353440256*x^4+124983967744*x^3+67515711488*x^2-5234491392*x+400505700352)[1]
    OL = maximal_order(L)
    @test length(prime_decomposition(OL, 2)) == 30
    Lns1 = number_field([x^2 - 2])[1]
    @test length(prime_decomposition(maximal_order(Lns1), 3)) == 1
    Lns, gLns = number_field([x^2-5, x^2-13])
    OLns = maximal_order(Lns)
    lP = prime_decomposition(OLns, 5)
    @test length(lP) == 1
  end

  @testset "Frobenius automorphism" begin
    K = number_field(x^2+1)[1]
    OK = maximal_order(K)
    lp = prime_decomposition(OK, 5)
    P = lp[1][1]
    @test Hecke.frobenius_automorphism(P) == id_hom(K)
    lp = prime_decomposition(OK, 7)
    P = lp[1][1]
    @test Hecke.frobenius_automorphism(P) != id_hom(K)
  end

  @testset "Minimum" begin
    k, = number_field(x^2 - 2);
    K, = number_field(x^4 - 144 * x^2 - 7938);
    f = hom(k, K, 1//81 * gen(K)^2 - 8//9);
    P = prime_decomposition(maximal_order(K), 7)[1][1]
    mP = minimum(f, P)
    @test norm(mP) == 7
  end

  @testset "Is principal" begin
    Qx, x = QQ["x"]
    f = x^2 - 5
    K, a = NumberField(f, "a")
    OK = maximal_order(K)
    P = first(keys(factor(3 * OK)))
    fl, x = Hecke.is_principal_fac_elem(P)
    @test fl
    @test OK(evaluate(x)) * OK == P
  end

  @testset "Gens" begin
    Qx, x = QQ["x"]
    f = x^2 - 5
    K, a = NumberField(f, "a")
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

  # Minimum for non-simple
  Qx, x = FlintQQ["x"]
  f = x - 1
  K, a = number_field([f], "a")
  O = maximal_order(K)
  I = Hecke.ideal(O, 2, O(2))
  @test (@inferred minimum(I)) == 2

  f = x^2 - 2
  K, a = number_field([f], "a")
  O = maximal_order(K)
  I = ideal(O, 2 * identity_matrix(ZZ, 2))
  Hecke.assure_2_normal(I)
  @test isdefined(I, :gen_two)

  include("Ideal/Prime.jl")
end
