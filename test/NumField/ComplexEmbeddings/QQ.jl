@testset "QQ" begin
  c = complex_conjugation(QQ)
  @test c(QQ(1)) == QQ(1)
end
