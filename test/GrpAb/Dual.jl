@testset "Dual" begin
  QZ = Hecke.QmodnZ()
  for T in [fmpz, Int, fmpq, Rational{BigInt}]
    @test @inferred QZ(0) == T(0)
    @test @inferred T(0) == QZ(0)
  end
  @test @inferred iszero(QZ(0))
  @test @inferred !iszero(QZ(1//2))
  for T in [fmpq, Rational{BigInt}]
    @test @inferred QZ(1//2) != T(1)
    @test @inferred T(1) != QZ(1//2)
  end
end
