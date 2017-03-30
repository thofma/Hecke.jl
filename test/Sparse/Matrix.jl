@testset "Matrix" begin

  R = FlintIntegerRing()
  S, x = PolynomialRing(R, "x")
  T = ResidueRing(R, 2)

  @testset "Creation" begin
    MR = @inferred SMatSpace(R, 1, 2)
    MS = @inferred SMatSpace(S, 2, 3)
    MT = @inferred SMatSpace(T, 2, 3, false)

    @test R == @inferred base_ring(MR)
    @test S == @inferred base_ring(MS)
    @test T == @inferred base_ring(MT)

    MR2 = SMatSpace(R, 1, 2)

    @test MR === MR2

    MT2 = SMatSpace(T, 2, 3, false)

    @test MT != MT2

    mR = MR()

    @test R == @inferred base_ring(mR)
    @test MR == @inferred parent(mR)
    @test 1 == @inferred rows(mR)
    @test 2 == @inferred cols(mR)
    @test 1 == @inferred length(mR.rows)

  end
end
 
