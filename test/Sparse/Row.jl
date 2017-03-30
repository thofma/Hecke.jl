@testset "Row" begin
  
  R = FlintIntegerRing()
  S, x = PolynomialRing(R, "x")
  T = ResidueRing(R, 2)

  @testset "Creation" begin
    
    MR = @inferred SRowSpace(R)
    MS = @inferred SRowSpace(S)
    MT = @inferred SRowSpace(T, false)

    @test R == @inferred base_ring(MR)
    @test S == @inferred base_ring(MS)
    @test T == @inferred base_ring(MT)

    MR2 = SRowSpace(R)
    @test MR === MR2

    MT2 = SRowSpace(T, false)
    @test MT2 != MT

    Rr = @inferred MR()
    Sr = @inferred MS()
    Tr = @inferred MT()

    @test Rr.values == Array(elem_type(R), 0)
    @test Rr.pos == Array(Int, 0)
    @test Sr.values == Array(elem_type(S), 0)
    @test Sr.pos == Array(Int, 0)
    @test Tr.values == Array(elem_type(T), 0)
    @test Tr.pos == Array(Int, 0)

    @test @inferred iszero(Rr)
    @test @inferred iszero(Sr)
    @test @inferred iszero(Tr)

    Rr2 = @inferred SRow([(1,R(1)), (1000, R(2))])

    @test Rr2.values == [R(1), R(2)]
    @test Rr2. pos == [1, 1000]

    Rr3 = @inferred SRow([1, 1000], [R(1), R(2)])

    @test Rr2 == Rr3
    @test R == @inferred base_ring(Rr2)

    Sr1 = @inferred SRow([(1,S(1)), (1000, S(2))])
    Sr2 = @inferred SRow(Rr2, S)

    @test Sr1 == Sr2

    @test_throws ErrorException SRow([1,1], [ R(1) ])
    @test_throws ErrorException SRow([1], [ R(1), R(2) ])

    a = @inferred hash(Rr2)
    b = @inferred hash(Rr3)
    @test a == b
  end

  MR = @inferred SRowSpace(R)
  MS = @inferred SRowSpace(S)
  MT = @inferred SRowSpace(T)

  @testset "Copy" begin
    Rs = @inferred SRow([(1,x), (1000, x^2)])
    Rs2 = @inferred copy(Rs)
    @test Rs == Rs2
  end

  @testset "Modular reduction" begin
    Rr = SRow([1,2,3,4,5], [ZZ(1), ZZ(2), ZZ(3), ZZ(4), ZZ(5)])
    Rr2 = @inferred mod(Rr, 5)
    Rr3 = @inferred mod(Rr, ZZ(5))

    @test Rr2 == SRow([1,2,3,4], [ZZ(1), ZZ(2), ZZ(3), ZZ(4)])
    @test Rr2 == Rr3

    Rr2 = @inferred mod_sym(Rr, 5)
    Rr3 = @inferred mod_sym(Rr, ZZ(5))

    @test Rr2 == SRow([1,2,3,4], [ZZ(1), ZZ(2), ZZ(-2), ZZ(-1)])
    @test Rr2 == Rr3
  end  

  @testset "Changering the ring" begin
    Rr = SRow([1,2,3,4,5], [ZZ(1), ZZ(2), ZZ(3), ZZ(4), ZZ(5)])

    Tr = @inferred change_ring(Rr, T)
    Sr = @inferred change_ring(Rr, S)

    @test Tr == SRow([1,3,5], [T(1), T(1), T(1)])
    @test Sr == SRow([1,2,3,4,5], [S(1), S(2), S(3), S(4), S(5)])
  end

  @testset "Iteration" begin
    Rr = SRow([1,2,3,4,5], [ZZ(1), ZZ(2), ZZ(3), ZZ(4), ZZ(5)])

    t = Tuple{Int, fmpz}[]

    for (p, v) in Rr
      push!(t, (p, v))
    end

    @test t == [(1, ZZ(1)), (2, ZZ(2)), (3, ZZ(3)), (4, ZZ(4)), (5, ZZ(5))]
  end

  @testset "Scalar product" begin
    Rr = SRow([1,2,3,4,5], [ZZ(1), ZZ(2), ZZ(3), ZZ(4), ZZ(5)])

    @test 55 == @inferred mul(Rr, Rr)
  end

  @testset "Addition" begin
    Rr = SRow([1,2,3,4,5], [ZZ(1), ZZ(2), ZZ(3), ZZ(4), ZZ(5)])
    R2r = SRow([1,2,3,4,5], [ZZ(2), ZZ(4), ZZ(6), ZZ(8), ZZ(10)])

    @test R2r == @inferred Rr + Rr

    Tr = @inferred change_ring(Rr, T)

    @test Tr == @inferred Tr + SRow(T)
  end

  @testset "Scalar multiplication" begin
    Rr = SRow([1,2,3,4,5], [ZZ(1), ZZ(2), ZZ(3), ZZ(4), ZZ(5)])

    R2r = SRow([1,2,3,4,5], [ZZ(2), ZZ(4), ZZ(6), ZZ(8), ZZ(10)])

    @test R2r == @inferred 2*Rr
    @test R2r == @inferred ZZ(2)*Rr
  end

  @testset "Maximum and minimum" begin
    Rr = SRow([1,2,3,4,5,6], [ZZ(1), ZZ(2), ZZ(3), ZZ(4), ZZ(5), ZZ(-100)])

    @test 5 == @inferred max(Rr)
    @test -100 == @inferred min(Rr)
  end

  @testset "Lifting" begin
    U = ZZModUInt(UInt(5))
    Ur = SRow([1,2,3,4], [U(1), U(2), U(3), U(4)])
    Rr = SRow([1,2,3,4], [R(1), R(2), R(3), R(4)])

    @test Rr == @inferred lift(Ur)
  end
end
