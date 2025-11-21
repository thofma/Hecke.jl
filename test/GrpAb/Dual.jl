@testset "Dual" begin
  QZ = Hecke.QmodnZ()
  for T in [ZZRingElem, Int, QQFieldElem, Rational{BigInt}]
    @test (@inferred QZ(0)) == T(0)
    @test (@inferred T(0)) == QZ(0)
  end
  @test @inferred iszero(QZ(0))
  @test @inferred !iszero(QZ(1//2))
  for T in [QQFieldElem, Rational{BigInt}]
    @test @inferred QZ(1//2) != T(1)
    @test @inferred T(1) != QZ(1//2)
  end

  @test iszero(QZ(1//2) - QZ(1//2))
  @test -QZ(1//2) == QZ(1//2)
  @test -QZ(1//3) == QZ(2//3)

  @test sprint(show, "text/plain", QZ) isa String
  @test sprint(show, "text/plain", Hecke.QmodnZ(ZZ(2))) isa String
  s = sprint(show, "text/plain", map_from_func(x -> x, QZ, QZ))
  @test s isa String && !contains(s, "q/Z")
end
