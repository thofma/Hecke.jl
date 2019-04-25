@testset "Is integral" begin
  Qx, x = FlintQQ["x"]
  f = x^2 + 1
  A = AlgAss(f)

  @test Hecke.isintegral(A[1]) == true
  @test Hecke.isintegral(fmpq(1, 2)*A[1]) == false

  B = AlgGrp(FlintQQ, small_group(2, 1))
  @test Hecke.isintegral(B[1]) == true
  @test Hecke.isintegral(fmpq(1, 2)*B[1]) == false

  C = AlgMat(FlintQQ, B, 2)
  @test Hecke.isintegral(C[1]) == true
  @test Hecke.isintegral(fmpq(1, 2)*C[1]) == false
end
