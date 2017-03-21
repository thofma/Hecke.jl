@testset "Elements" begin
  Qx, x = PolynomialRing(FlintQQ, "x")

  K1, a1 = NumberField(x^3 - 2, "a")
  O1 = EquationOrder(K1)

  @testset "Construction" begin

    b1 = @inferred O1(2*a1^0)
    @test b1.elem_in_nf == 2*a1^0
    @test parent(b1) == O1
    @test typeof(b1) == NfOrdElem{NfOrdGen}

    b2 = @inferred O1(2)
    @test parent(b2) == O1
    @test typeof(b2) == NfOrdElem{NfOrdGen}
    @test b1 == b2

    b3 = @inferred O1(fmpz(2))
    @test parent(b3) == O1
    @test typeof(b3) == NfOrdElem{NfOrdGen}
    @test b1 == b3

    b4 = @inferred O1([2, 0, 0])
    @test parent(b4) == O1
    @test typeof(b4) == NfOrdElem{NfOrdGen}
    @test b4.has_coord
    @test b1 == b4

    b5 = @inferred O1([ZZ(2), ZZ(0), ZZ(0)])
    @test parent(b5) == O1
    @test typeof(b5) == NfOrdElem{NfOrdGen}
    @test b5.has_coord
    @test b1 == b5

    b6 = @inferred O1(2*a1^0, [ZZ(2), ZZ(0), ZZ(0)])
    @test parent(b6) == O1
    @test typeof(b6) == NfOrdElem{NfOrdGen}
    @test b6.has_coord
    @test b1 == b6

    b7 = @inferred O1()
    @test parent(b6) == O1
    @test typeof(b6) == NfOrdElem{NfOrdGen}
  end

  b1 = O1(2*a1^0)
  b2 = O1(2)

  @testset "Deepcopy" begin
    b = @inferred O1(a1)
    bb = @inferred deepcopy(b)
    @test b == bb
  end

  @testset "Conversion to basis and number field" begin
    b = @inferred elem_in_nf(b1)
    @test b == K1(2)

    b = @inferred elem_in_basis(b1)
    @test b == [ ZZ(2), ZZ(0), ZZ(0) ]

    b = O1(a1//2, false)
    @test_throws ErrorException elem_in_basis(b)
    
    b = O1(a1)
    c = @inferred K1(b)
  @test c == a1


  end

  @testset "Discriminant" begin

    b = @inferred discriminant([ O1(1), O1(2*a1), O1(4*a1^2) ])
    @test b == 64 * -108

    @test_throws ErrorException discriminant( [ O1(1) ])
  end

  @testset "Hashing" begin
    b = @inferred hash(b1)
    @test b == hash(b2)
  end

  @testset "Zero/one" begin
    b = @inferred one(O1)
    @test isone(b)

    b = @inferred one(b1)
    @test isone(b)

    b = @inferred zero(O1)
    @test iszero(b)

    b = @inferred zero(b1)
    @test iszero(b)
  end

  @testset "Unary operations" begin
    b = @inferred -b1
    @test b == O1(-2)
    b = -O1([2, 0, 0])
    @test b.has_coord
  end

  @testset "Binary operations" begin
    b = @inferred O1(a1) * O1(a1^2)
    @test b == O1(2)

    b = @inferred O1(a1) + O1(a1^2)
    @test b == O1(a1 + a1^2)

    c = @inferred O1([1, 0, 0]) + O1([0, 1, 0])
    @test c.has_coord

    b = @inferred O1(a1) - O1(a1^2)
    @test b == O1(a1 - a1^2)

    c = @inferred O1([1, 0, 0]) - O1([0, 1, 0])
    @test c.has_coord
  end

  @testset "Ad hoc binary operations" begin
    b = O1(2*a1)
    c = @inferred 2 * O1(a1)
    @test b == c
    c = @inferred O1(a1) * 2
    @test b == c
    c = @inferred fmpz(2) * O1(a1)
    @test b == c
    c = @inferred O1(a1) * fmpz(2)
    @test b == c

    b = O1(2 + a1)
    c = @inferred 2 + O1(a1)
    @test b == c
    c = @inferred O1(a1) + 2
    @test b == c
    c = @inferred fmpz(2) + O1(a1)
    @test b == c
    c = @inferred O1(a1) + fmpz(2)
    @test b == c

    b = O1(2 - a1)
    c = @inferred 2 - O1(a1)
    @test b == c
    c = @inferred -(O1(a1) - 2)
    @test b == c
    c = @inferred fmpz(2) - O1(a1)
    @test b == c
    c = @inferred -(O1(a1) - fmpz(2))
    @test b == c

    b = O1(2*a1)
    c = @inferred divexact(b, 2)
    @test c == O1(a1)
    c = @inferred divexact(b, fmpz(2))
    @test c == O1(a1)
  end
  
  @testset "Exponentiation" begin
    b = O1(a1)
    c = @inferred b^3
    @test c == O1(2)
    c = @inferred b^fmpz(3)
    @test c == O1(2)
  end

  @testset "Modular reduction" begin
    b = O1([3, 2, 2])
    c = @inferred mod(b, 2)
    @test c == O1(1)
    c = @inferred mod(b, fmpz(2))
    @test c == O1(1)
  end

  @testset "Modular exponentiation" begin
    b = O1(2*a1)
    c = @inferred powermod(b, fmpz(3), fmpz(3))
    @test c == O1(1)
    c = @inferred powermod(b, fmpz(3), 3)
    @test c == O1(1)
    c = @inferred powermod(b, 3, fmpz(3))
    @test c == O1(1)
    c = @inferred powermod(b, 3, 3)
    @test c == O1(1)
  end

  @testset "Representation matrix" begin
    b = O1(1)
    c = @inferred representation_mat(b)
    @test c == one(MatrixSpace(FlintZZ, 3, 3))
    b = O1(a1)
    c = @inferred representation_mat(b)
    @test c == ZZ[0 1 0; 0 0 1; 2 0 0]
    c = @inferred representation_mat(b, K1)
    @test c == Hecke.FakeFmpqMat(ZZ[0 1 0; 0 0 1; 2 0 0], one(FlintZZ))
  end

  @testset "Trace" begin
    b = O1(a1)
    c = @inferred trace(b)
    @test c == 0
  end 

  @testset "Norm" begin
    b = O1(a1)
    c = @inferred norm(b)
    @test c == 2
  end

  @testset "Random elements" begin
    B = 10
    b = @inferred rand(O1, -B:B)
    for i in 1:degree(O1)
      @test -B <= elem_in_basis(b)[i] && elem_in_basis(b)[i] <= B
    end

    B = BigInt(10)
    b = @inferred rand(O1, -B:B)
    B = fmpz(B)
    for i in 1:degree(O1)
      @test -B <= elem_in_basis(b)[i] && elem_in_basis(b)[i] <= B
    end

    B = 10
    b = @inferred rand(O1, B)
    for i in 1:degree(O1)
      @test -B <= elem_in_basis(b)[i] && elem_in_basis(b)[i] <= B
    end

    B = ZZ(10)
    b = @inferred rand(O1, B)
    for i in 1:degree(O1)
      @test -B <= elem_in_basis(b)[i] && elem_in_basis(b)[i] <= B
    end
  end

  RR = ArbField(64)

  @testset "Minkowski map" begin
    b = O1(a1)
    c = @inferred minkowski_map(b, 1024)
    @test overlaps(c[1], root(RR(2), 3))
    @test Hecke.radiuslttwopower(c[1], -1024)
    @test overlaps(c[2],  (-1//sqrt(RR(2))*root(RR(2), 3)))
    @test Hecke.radiuslttwopower(c[2], -1024)
    @test overlaps(c[3], (sqrt(RR(3)//RR(2))*root(RR(2), 3)))
    @test Hecke.radiuslttwopower(c[3], -1024)
  end

  CC = AcbField(64)

  @testset "Conjugates" begin
    b = O1(a1)
    c = @inferred conjugates_arb(b, 1024)
    @test isa(c, Array{acb, 1})
    @test overlaps(c[1], CC(root(RR(2), 3)))
    @test Hecke.radiuslttwopower(c[1], -1024)
    @test overlaps(c[2], (-CC(1)//2 + onei(CC)*sqrt(RR(3))//2)*CC(root(RR(2), 3)))
    @test Hecke.radiuslttwopower(c[1], -1024)
    @test overlaps(c[3], (-CC(1)//2 - onei(CC)*sqrt(RR(3))//2)*CC(root(RR(2), 3)))
    @test Hecke.radiuslttwopower(c[1], -1024)

    c = @inferred conjugates_arb_log(b, 1024)
    @test isa(c, Array{arb, 1})
    @test overlaps(c[1], log(RR(2))//3)
    @test Hecke.radiuslttwopower(c[1], -1024)
    @test overlaps(c[2], 2*log(RR(2))//3)
    @test Hecke.radiuslttwopower(c[2], -1024)
  end

  @testset "Promotion rule" begin
    b = @inferred ==(O1(1), 1)
  end
end
