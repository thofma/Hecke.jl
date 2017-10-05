@testset "Orders" begin

  @test Nemo.elem_type(Nemo.parent_type(NfOrdElem)) === NfOrdElem
  @test Nemo.parent_type(Nemo.elem_type(NfOrd)) === NfOrd

  @testset "Construction" begin
    Qx, x = PolynomialRing(FlintQQ, "x")

    K1, a1 = NumberField(x^3 - 2, "a")
    O1 = EquationOrder(K1)

    @test @inferred nf(O1) == K1
    @test parent(O1) == NfOrdSet(K1)

    K2, a2 = NumberField(x - 2, "a")
    O2 = EquationOrder(K2)

    @test @inferred nf(O2) == K2
    @test @inferred parent(O2) == NfOrdSet(K2)

    f3 = x^64 - 64*x^62 + 1952*x^60 - 37760*x^58 + 520144*x^56 - 5430656*x^54 + 44662464*x^52 - 296854272*x^50 + 1623421800*x^48 - 7398867840*x^46 + 28362326720*x^44 - 92043777280*x^42 + 254005423840*x^40 - 597659820800*x^38 + 1200442440064*x^36 - 2057901325824*x^34 + 3006465218196*x^32 - 3732682723968*x^30 + 3922021702720*x^28 - 3467892873984*x^26 + 2561511781920*x^24 - 1565841089280*x^22 + 782920544640*x^20 - 315492902400*x^18 + 100563362640*x^16 - 24754058496*x^14 + 4559958144*x^12 - 602516992*x^10 + 53796160*x^8 - 2968064*x^6 + 87296*x^4 - 1024*x^2 + 2

    K3, a3 = NumberField(f3, "a")
    O3 = Order(K3, [ a3^i for i in 0:63])

    @test nf(O3) == K3
    @test parent(O3) == NfOrdSet(K3)

    K4, a4 = NumberField(x^2 - 5, "a")
    O4 = Order(K4, Hecke.FakeFmpqMat(FlintZZ[1 0; 0 2], fmpz(1)))
    O44 = Order(K4, FlintQQ[1 0; 0 2])
    O444 = Order(K4, FlintZZ[1 0; 0 2])

    @test nf(O4) == K4
    @test parent(O4) == NfOrdSet(K4)

    @test O4 == O44
    @test O44 == O444
    @test O4 === O44
    @test O44 === O444

    K6, a6 = NumberField(x^2 - 180, "a")
    O6 = EquationOrder(K6)

    @test nf(O6) == K6
    @test parent(O6) == NfOrdSet(K6)

    O7 = Order(K6, Hecke.FakeFmpqMat(FlintZZ[6 0; 0 1], FlintZZ(6)), true, false)
    O77 = Order(K6, FlintQQ[6//6 0; 0 1//6])

    @test O7 == O77
    @test !(O7 === O77)

    @test_throws ErrorException Order(K1, [a1, a1, a1])
    #@test_throws ErrorException Order(K1, [1, a1, a1])
    #@test_throws ErrorException Order(K1, [1.0, a1, a1])
    @test_throws ErrorException Order(K6, Hecke.FakeFmpqMat(FlintZZ[0 0; 0 0], FlintZZ(6)))
    @test_throws ErrorException Order(K6, Hecke.FakeFmpqMat(FlintZZ[0 2; 2 0], FlintZZ(6)))
    @test_throws ErrorException Order(K6, Hecke.FakeFmpqMat(FlintZZ[0 0], FlintZZ(6)))
  end

  Qx, x = PolynomialRing(FlintQQ, "x")

  K1, a1 = NumberField(x^3 - 2, "a")
  O1 = EquationOrder(K1)

  K2, a2 = NumberField(x - 2, "a")
  O2 = EquationOrder(K2)

  f3 = x^64 - 64*x^62 + 1952*x^60 - 37760*x^58 + 520144*x^56 - 5430656*x^54 +
       44662464*x^52 - 296854272*x^50 + 1623421800*x^48 - 7398867840*x^46 +
       28362326720*x^44 - 92043777280*x^42 + 254005423840*x^40 -
       597659820800*x^38 + 1200442440064*x^36 - 2057901325824*x^34 +
       3006465218196*x^32 - 3732682723968*x^30 + 3922021702720*x^28 -
       3467892873984*x^26 + 2561511781920*x^24 - 1565841089280*x^22 +
       782920544640*x^20 - 315492902400*x^18 + 100563362640*x^16 -
       24754058496*x^14 + 4559958144*x^12 - 602516992*x^10 + 53796160*x^8 -
       2968064*x^6 + 87296*x^4 - 1024*x^2 + 2

  K3, a3 = NumberField(f3, "a")
  O3 = Order(K3, [ a3^i for i in 0:63])

  K4, a4 = NumberField(x^2 - 5, "a")
  O4 = Order(K4, Hecke.FakeFmpqMat(FlintZZ[1 0; 0 2], fmpz(1)))

  K6, a6 = NumberField(x^2 - 180, "a")
  O6 = EquationOrder(K6)

  O7 = Order(K6, Hecke.FakeFmpqMat(FlintZZ[6 0; 0 1], FlintZZ(6)))

  O5 = @inferred deepcopy(O2)

  @testset "Deepcopy" begin
    O5 = @inferred deepcopy(O2)
    @test nf(O2) == nf(O5)
  end

  @testset "Field access" begin
    b = @inferred parent(O2)
    @test b == @inferred parent(O5)

    @test K1 == @inferred nf(O1)
    @test K2 == @inferred nf(O2)
    @test K3 == @inferred nf(O3)

    @test @inferred isequation_order(O1)
    @test @inferred isequation_order(O2)
    @test @inferred !isequation_order(O3)
    @test @inferred !isequation_order(O4)
    @test @inferred isequation_order(O5)

    b = @inferred basis(O1)
    @test b == [ O1(1), O1(a1), O1(a1^2) ]

    b = @inferred basis(O2)
    @test b == [ O2(1) ]

    b = @inferred basis(O3)
    @test b == [ O3(a3^i) for i in 0:63]

    b = @inferred basis(O4)
    @test b == [ O4(1), O4(2*a4) ]

    @test O1.basis_nf == [ a1^0, a1, a1^2]

    @test O2.basis_nf == [ K2(1) ]

    @test O3.basis_nf == [ a3^i for i in 0:63]

    @test O4.basis_nf == [ a4^0, 2*a4 ]

    b = @inferred basis_mat(O1)
    @test b == Hecke.FakeFmpqMat(one(MatrixSpace(FlintZZ, 3, 3)), one(FlintZZ))

    b = @inferred basis_mat(O2)
    @test b == Hecke.FakeFmpqMat(one(MatrixSpace(FlintZZ, 1, 1)), one(FlintZZ))

    b = @inferred basis_mat(O3)
    @test b == Hecke.FakeFmpqMat(one(MatrixSpace(FlintZZ, 64, 64)), one(FlintZZ))

    b = @inferred basis_mat(O4)
    @test b == Hecke.FakeFmpqMat(FlintZZ[1 0; 0 2], one(FlintZZ))

    b = @inferred basis_mat_inv(O1)
    @test b == Hecke.FakeFmpqMat(one(MatrixSpace(FlintZZ, 3, 3)), one(FlintZZ))

    b = @inferred basis_mat_inv(O2)
    @test b == Hecke.FakeFmpqMat(one(MatrixSpace(FlintZZ, 1, 1)), one(FlintZZ))

    b = @inferred basis_mat_inv(O3)
    @test b == Hecke.FakeFmpqMat(one(MatrixSpace(FlintZZ, 64, 64)), one(FlintZZ))

    b = @inferred basis_mat_inv(O4)
    @test b == Hecke.FakeFmpqMat(FlintZZ[2 0; 0 1], FlintZZ(2))
  end

  @testset "Index" begin
    b = @inferred gen_index(O1)
    @test b == 1
    b = @inferred index(O1)
    @test b == 1

    b = @inferred gen_index(O2)
    @test b == 1
    b = @inferred index(O2)
    @test b == 1

    b = @inferred gen_index(O3)
    @test b == 1
    b = @inferred index(O3)
    @test b == 1

    b = @inferred gen_index(O4)
    @test b == FlintQQ(1, 2)
    @test_throws ErrorException index(O4)

    b = @inferred gen_index(O7)
    @test b == FlintQQ(6)
    b = @inferred index(O7)
    @test b == 6

    @test !@inferred isindex_divisor(O1, 2)
    @test !@inferred isindex_divisor(O1, 3)
    @test @inferred isindex_divisor(O7, 2)
    @test @inferred isindex_divisor(O7, fmpz(3))
    @test !@inferred isindex_divisor(O7, 5)
  end

  @testset "Discriminant" begin
    b = @inferred discriminant(O1)
    @test b == -108

    b = @inferred discriminant(O2)
    @test b == 1

    b = @inferred discriminant(O3)
    @test b == fmpz(2)^447

    b = @inferred discriminant(O4)
    @test b == fmpz(80)
  end

  @testset "Signature" begin
    @test 3 == @inferred degree(O1)
    @test 1 == @inferred degree(O2)
    @test 64 == @inferred degree(O3)
    @test 2 == @inferred degree(O4)

    @test (1, 1) == @inferred signature(O1)
    @test (1, 0) == @inferred signature(O2)
    @test (64, 0) == @inferred signature(O3)
    @test (2, 0) == @inferred signature(O4)
  end

  # minkowski mat

  @testset "Minkowski matrix" begin
    RR = ArbField(64)

    b = RR[ RR(1) sqrt(RR(2)) RR(0); (exp(1//RR(3) * log(RR(2)))) (-exp(-1//RR(6) * log(RR(2)))) (sqrt(RR(3)) * exp(-1//RR(6) * log(RR(2)))); (exp(1//RR(3) * log(RR(4)))) (-exp(1//RR(6) * log(RR(2)))) (-exp(1//RR(6) * log(RR(54)))) ]
    bb = @inferred minkowski_mat(O1, 256)

    @test overlaps(b, bb)
    for i in 1:3
      for j in 1:3
        @test Hecke.radiuslttwopower(bb[i, j], -256)
      end
    end

    b = one(MatrixSpace(RR, 1, 1))

    bb = @inferred minkowski_mat(O2, 1024)

    @test overlaps(b, bb)
    for i in 1:1
      for j in 1:1
        @test Hecke.radiuslttwopower(bb[i, j], -1024)
      end
    end

    bb = @inferred minkowski_mat(O3, 1024)

    for i in 1:64
      for j in 1:64
        @test Hecke.radiuslttwopower(bb[i, j], -1024)
      end
    end

    @test contains(RR("19063561108769878656033240617946635072004849200892084525390959717509 +/- 1"), det(bb))

    b = RR[ RR(1) RR(1); -2*sqrt(RR(5)) 2*sqrt(RR(5))]

    bb = @inferred minkowski_mat(O4, 1024)

    @test overlaps(b, bb) ||
    for i in 1:2
      for j in 1:2
        @test Hecke.radiuslttwopower(bb[i, j], -1024)
      end
    end
  end

  @testset "Element inclusion" begin
    b = @inferred in(a1, O1)
    @test b

    b = @inferred in(a1//2, O1)
    @test !b

    b = @inferred in(a2, O2)
    @test b

    b = @inferred in(a2//3, O2)
    @test !b

    b = @inferred in(a3^4, O3)
    @test b

    b = @inferred in(a3^3//2, O3)
    @test !b

    b = @inferred in(2*a4, O4)
    @test b

    b = @inferred in(a4, O4)
    @test !b
  end

  @testset "Denoninator of elements" begin
    b = @inferred den(a1, O1)
    @test b == 1
    b = @inferred den(a1//7, O1)
    @test b == 7

    b = @inferred den(a2, O2)
    @test b == 1
    b = @inferred den(a2//4, O2)
    @test b == 2

    b = @inferred den(a3, O3)
    @test b == 1
    b = @inferred den(a3^3//2, O3)
    @test b == 2

    b = @inferred den(a4, O4)
    @test b == 2
    b = @inferred den(a4//2, O4)
    @test b == 4
  end

  @testset "Addition" begin
    O6_2 = Order(K6, Hecke.FakeFmpqMat(FlintZZ[2 0; 0 1], FlintZZ(2)))
    O6_3 = Order(K6, Hecke.FakeFmpqMat(FlintZZ[3 0; 0 1], FlintZZ(3)))

    b = @inferred O6_2 + O6_3
    @test basis_mat(b) == Hecke.FakeFmpqMat(FlintZZ[6 0; 0 1], FlintZZ(6))

    @test discriminant(b) == 20

    @test_throws ErrorException O4 + O4
    @test_throws ErrorException O6_2 + O6_2
  end

  @testset "Maximal Order" begin
    KK, _a = number_field(x^18 - 78*x^17 + 2613*x^16 - 49085*x^15 + 567645*x^14
                          - 4204473*x^13 + 20464879*x^12 - 68501589*x^11 +
                          169973505*x^10 - 322856306*x^9 + 493384242*x^8 -
                          631138365*x^7 + 698201471*x^6 - 646804899*x^5 +
                          437728161*x^4 - 236413590*x^3 + 186076059*x^2 -
                          128459175*x + 34393321)

    O_KK = maximal_order(KK)
    @test discriminant(O_KK) == -82506874955368517242637353371059355648
  end
end
